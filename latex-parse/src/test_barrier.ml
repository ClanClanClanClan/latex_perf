(** Unit tests for Barrier one-shot thread synchronisation. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[barrier] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. create → ready = false *)
  run "create initial state" (fun tag ->
      let b = Barrier.create () in
      expect (not !(b.ready)) tag);

  (* 2. release sets ready *)
  run "release sets ready" (fun tag ->
      let b = Barrier.create () in
      Barrier.release b;
      expect !(b.ready) tag);

  (* 3. wait after release returns immediately *)
  run "wait after release" (fun tag ->
      let b = Barrier.create () in
      Barrier.release b;
      Barrier.wait b;
      expect true tag);

  (* 4. Blocking behavior: thread releases after delay *)
  run "blocking wait" (fun tag ->
      let b = Barrier.create () in
      let t0 = Clock.now () in
      let _ =
        Thread.create
          (fun () ->
            Unix.sleepf 0.020;
            Barrier.release b)
          ()
      in
      Barrier.wait b;
      let elapsed = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) in
      expect (elapsed >= 15.0) (tag ^ Printf.sprintf ": elapsed=%.1fms" elapsed));

  (* 5. Multiple waiters all unblocked *)
  run "multi-waiter" (fun tag ->
      let b = Barrier.create () in
      let counter = ref 0 in
      let mu = Mutex.create () in
      let threads =
        List.init 4 (fun _ ->
            Thread.create
              (fun () ->
                Barrier.wait b;
                Mutex.lock mu;
                incr counter;
                Mutex.unlock mu)
              ())
      in
      Unix.sleepf 0.010;
      Barrier.release b;
      List.iter Thread.join threads;
      expect (!counter = 4) (tag ^ Printf.sprintf ": count=%d" !counter));

  (* 6. Double release is safe *)
  run "double release" (fun tag ->
      let b = Barrier.create () in
      Barrier.release b;
      Barrier.release b;
      expect !(b.ready) tag);

  if !fails > 0 then (
    Printf.eprintf "[barrier] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[barrier] PASS %d cases\n%!" !cases
