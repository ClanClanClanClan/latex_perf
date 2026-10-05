(* Regression test for OPEN-125: the multi-worker pool dropped requests.

   Each scenario runs in a re-exec'd copy of this binary that the parent kills
   after a deadline, so a hang is a FAIL naming the last step started, never a
   stuck test run. (The deadline is enforced by the PARENT: an OCaml signal
   handler in the child cannot be relied on, because when every thread is
   blocked in a C call no thread runs OCaml code to execute it — measured: a
   SIGALRM watchdog never fired in the hung no-mutex variant.)

   plain (no fault injection, requests take ~1 ms, the hedge never fires): P1 20
   sequential calls on a 2-worker pool all answer, identically, and no worker is
   rotated (C-123: a units bug made every reply report ~10^6x its allocation, so
   every request retired its worker). P2 retiring worker 0, then 1, then 0 again
   each returns (C-122: forked workers inherited the parent's end of earlier
   workers' sockets, so retiring worker 0 waited forever for an EOF worker 1 was
   holding off). P3 4 threads x 25 calls on a 2-worker pool all answer,
   identically (C-124: concurrent calls interleaved reads of one worker socket).
   hedge (L0_FAULT_MS=30 at rate 1.0: every request takes >= 30 ms, so the 12 ms
   hedge fires on every call and a loser reply is always left behind): H1 = P1
   under hedging, and the hedge path was taken. H2 = P3 under hedging. H3 a
   1-worker pool under hedging answers 20 sequential calls. *)

open Latex_parse_lib

let doc =
  Bytes.of_string
    "\\documentclass{article}\\begin{document}Hello $x^2$\\end{document}"

let fails = ref 0

let fail fmt =
  Printf.ksprintf
    (fun m ->
      prerr_endline ("[broker-pool] FAIL: " ^ m);
      incr fails)
    fmt

(* Progress marker: the parent reports the last one if the child hangs. *)
let step what = Printf.eprintf "[broker-pool] step %s\n%!" what

let call p =
  Broker.hedged_call p ~input:doc ~hedge_ms:Config.hedge_timer_ms_default

let same_as tag (r0 : Broker.svc_result) (r : Broker.svc_result) =
  if r.status <> 0 then fail "%s: status %d" tag r.status;
  if r.n_tokens <> r0.n_tokens || r.issues_len <> r0.issues_len then
    fail "%s: tokens/issues %d/%d, expected %d/%d" tag r.n_tokens r.issues_len
      r0.n_tokens r0.issues_len

let sequential tag p n =
  let r0 = call p in
  if r0.status <> 0 || r0.n_tokens <= 0 then
    fail "%s: first call status=%d tokens=%d" tag r0.status r0.n_tokens;
  for _ = 2 to n do
    same_as tag r0 (call p)
  done;
  r0

let concurrent tag p ~threads ~per =
  let r0 = call p in
  let bad = Atomic.make 0 in
  let body () =
    for _ = 1 to per do
      match call p with
      | r ->
          if
            r.status <> 0
            || r.n_tokens <> r0.n_tokens
            || r.issues_len <> r0.issues_len
          then Atomic.incr bad
      | exception e ->
          ignore e;
          Atomic.incr bad
    done
  in
  let ts = List.init threads (fun _ -> Thread.create body ()) in
  List.iter Thread.join ts;
  if Atomic.get bad > 0 then
    fail "%s: %d of %d concurrent calls wrong or failed" tag (Atomic.get bad)
      (threads * per)

let plain () =
  step "P1";
  let p = Broker.init_pool [| 0; 1 |] in
  ignore (sequential "P1" p 20);
  if Broker.rotations_count p <> 0 then
    fail "P1: %d rotations in 20 tiny requests (expected 0)"
      (Broker.rotations_count p);
  step "P2";
  Broker.retire p 0;
  Broker.retire p 1;
  Broker.retire p 0;
  ignore (sequential "P2-after" p 5);
  step "P3";
  let p2 = Broker.init_pool [| 0; 1 |] in
  concurrent "P3" p2 ~threads:4 ~per:25

let hedge () =
  step "H1";
  let p = Broker.init_pool [| 0; 1 |] in
  ignore (sequential "H1" p 20);
  (* The first call always hedges (both workers idle, 30 ms > 12 ms); later ones
     hedge when the previous loser has answered in time. *)
  if Broker.hedge_fired_count p < 1 then
    fail "H1: the hedge never fired in 20 calls of >= 30 ms";
  if Broker.rotations_count p <> 0 then
    fail "H1: %d rotations (expected 0)" (Broker.rotations_count p);
  step "H2";
  let p2 = Broker.init_pool [| 0; 1 |] in
  concurrent "H2" p2 ~threads:4 ~per:10;
  step "H3";
  let p3 = Broker.init_pool [| 0 |] in
  ignore (sequential "H3" p3 20)

let base_env = [ "L0_ALLOW_SCALAR=1"; "L0_NO_MLOCK=1"; "L0_MINOR_HEAP_MB=4" ]

(* Each scenario takes ~2 s when healthy. *)
let deadline_s = 90.0

let run_child mode extra =
  let env =
    Array.append (Array.of_list (base_env @ extra)) (Unix.environment ())
  in
  match Unix.fork () with
  | 0 -> (
      try Unix.execve Sys.executable_name [| Sys.executable_name; mode |] env
      with Unix.Unix_error _ -> Unix._exit 3)
  | pid ->
      let deadline = Unix.gettimeofday () +. deadline_s in
      let rec wait () =
        match Unix.waitpid [ Unix.WNOHANG ] pid with
        | 0, _ when Unix.gettimeofday () > deadline ->
            Unix.kill pid Sys.sigkill;
            ignore (Unix.waitpid [] pid);
            fail "%s scenario hung (> %.0f s; its last step is printed above)"
              mode deadline_s
        | 0, _ ->
            ignore (Unix.select [] [] [] 0.1);
            wait ()
        | _, Unix.WEXITED 0 -> Printf.printf "[broker-pool] %s: ok\n%!" mode
        | _, Unix.WEXITED n -> fail "%s scenario exited %d" mode n
        | _, (Unix.WSIGNALED n | Unix.WSTOPPED n) ->
            fail "%s scenario killed by signal %d" mode n
        | exception Unix.Unix_error (Unix.EINTR, _, _) -> wait ()
      in
      wait ()

let () =
  match Sys.argv with
  | [| _; "plain" |] ->
      plain ();
      exit (if !fails = 0 then 0 else 1)
  | [| _; "hedge" |] ->
      hedge ();
      exit (if !fails = 0 then 0 else 1)
  | _ ->
      run_child "plain" [];
      run_child "hedge" [ "L0_FAULT_MS=30"; "L0_FAULT_RATE_PPM=1000000" ];
      if !fails > 0 then exit 1;
      print_endline "[broker-pool] all scenarios passed"
