open Unix
open Latex_parse_lib

let unlink_if_exists p = try Unix.unlink p with _ -> ()
let rec read_exact fd b o l = if l=0 then () else let n=Unix.read fd b o l in if n=0 then failwith "client eof" else read_exact fd b (o+n) (l-n)
let rec write_all fd b o l = if l=0 then () else let n=Unix.write fd b o l in if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)

let () = Sys.set_signal Sys.sigpipe Sys.Signal_ignore

let sigchld_reaper _ =
  let rec reap () =
    match Unix.waitpid [Unix.WNOHANG] (-1) with
    | 0, _ -> ()
    | _, _ -> reap ()
  in
  (try reap () with _ -> ())

let run () =
  (* --- SIMD guard: refuse to run scalar unless explicitly allowed --- *)
  (try
     let (cpu_ok, sym_ok, allow_scalar) = Simd_guard.require () in
     if not (cpu_ok && sym_ok) && allow_scalar then
       prerr_endline "[svc] WARNING: running in scalar fallback because L0_ALLOW_SCALAR=1"
   with Failure msg ->
     prerr_endline ("[svc] FATAL: "^msg); exit 2
  );
  Sys.set_signal Sys.sigchld (Sys.Signal_handle sigchld_reaper);
  let sock_path = Config.service_sock_path in
  unlink_if_exists sock_path;
  let srv = Unix.socket PF_UNIX SOCK_STREAM 0 in
  Unix.set_close_on_exec srv;
  Unix.bind srv (ADDR_UNIX sock_path); Unix.listen srv 64;
  prerr_endline ("[svc] listening at "^sock_path);

  let pool = Broker.init_pool Config.pool_cores in

  let tail_csv_keep = Config.tail_trace_keep in
  let slow = ref ([] : (float * (int64*int64*int64*int64*int64*int64*bool*string)) list) in
  let add_slowest ms row =
    let xs = (ms, row) :: !slow in
    let xs = List.sort (fun (a,_) (b,_) -> compare b a) xs in
    let rec take n = function []->[] | _ when n=0 -> [] | y::ys -> y::take (n-1) ys in
    slow := take tail_csv_keep xs
  in
  let dump_csv () =
    let oc = open_out Config.tail_csv_path in
    output_string oc "ms_total,t_in_start,t_in_done,t_proc_start,t_hedge_fire,t_first_reply,t_reply_ready,hedged,origin\n";
    List.iter (fun (ms,(a,b,c,d,e,f,h,origin)) ->
      Printf.fprintf oc "%.3f,%Ld,%Ld,%Ld,%Ld,%Ld,%Ld,%d,%s\n" ms a b c d e f (if h then 1 else 0) origin
    ) (List.rev !slow);
    close_out oc
  in

  let rec accept_loop () =
    let (c,_) = Unix.accept srv in

    let recv () =
      let hdr = Bytes.create 4 in
      read_exact c hdr 0 4;
      let len =
        ((Char.code (Bytes.get hdr 0)) lsl 24)
        lor ((Char.code (Bytes.get hdr 1)) lsl 16)
        lor ((Char.code (Bytes.get hdr 2)) lsl 8)
        lor (Char.code (Bytes.get hdr 3))
      in
      if len > Config.max_req_bytes then failwith "req too large";
      let b = Bytes.create len in read_exact c b 0 len; b
    in

    let process req =
      try
        `Ok (Broker.hedged_call pool ~input:req ~hedge_ms:Config.hedge_timer_ms_default)
      with _exn ->
        `Err
    in

    let format = function
      | `Ok r ->
          let b = Bytes.create 13 in
          let put32 off v =
            Bytes.set b off     (Char.chr ((v lsr 24) land 0xFF));
            Bytes.set b (off+1) (Char.chr ((v lsr 16) land 0xFF));
            Bytes.set b (off+2) (Char.chr ((v lsr  8) land 0xFF));
            Bytes.set b (off+3) (Char.chr ( v        land 0xFF))
          in
          put32 0 r.Broker.status; put32 4 r.Broker.n_tokens; put32 8 r.Broker.issues_len;
          Bytes.set b 12 (match r.Broker.origin with `P->'\001' | `H->'\002'); b
      | `Err ->
          let b = Bytes.create 13 in
          let put32 off v =
            Bytes.set b off     (Char.chr ((v lsr 24) land 0xFF));
            Bytes.set b (off+1) (Char.chr ((v lsr 16) land 0xFF));
            Bytes.set b (off+2) (Char.chr ((v lsr  8) land 0xFF));
            Bytes.set b (off+3) (Char.chr ( v        land 0xFF))
          in
          put32 0 1; put32 4 0; put32 8 0; Bytes.set b 12 '\000'; b
    in

    let send reply =
      let len = Bytes.length reply in
      let hdr = Bytes.create 4 in
      Bytes.set hdr 0 (Char.chr ((len lsr 24) land 0xFF));
      Bytes.set hdr 1 (Char.chr ((len lsr 16) land 0xFF));
      Bytes.set hdr 2 (Char.chr ((len lsr  8) land 0xFF));
      Bytes.set hdr 3 (Char.chr ( len        land 0xFF));
      write_all c hdr 0 4; write_all c reply 0 len
    in

    let (ms, st) = Service_bracket.measure_bytes_in_to_reply_ready ~recv ~process ~format ~send in
    let hedged = false in
    add_slowest ms (st.Service_bracket.t_in_start, st.t_in_done, st.t_proc_start, st.t_hedge_fire, st.t_first_reply, st.t_reply_ready, hedged, "");
    if Broker.(pool.requests mod 10_000 = 0) then begin
      Printf.eprintf "[hedge] req=%d fired=%d (%.3f%%) wins=%d (%.1f%%) rotations=%d\n%!"
        Broker.(pool.requests) Broker.(pool.hedge_fired)
        (100.0 *. float Broker.(pool.hedge_fired) /. float (max 1 Broker.(pool.requests)))
        Broker.(pool.hedge_wins)
        (100.0 *. float Broker.(pool.hedge_wins) /. float (max 1 Broker.(pool.hedge_fired)))
        Broker.(pool.rotations);
      dump_csv ()
    end;
    Unix.close c; accept_loop ()
  in
  accept_loop ()

let () = run ()