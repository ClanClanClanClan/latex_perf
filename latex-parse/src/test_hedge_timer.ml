(** Smoke tests for Hedge_timer platform-specific C FFI. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[hedge-timer] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. create does not raise *)
  run "create" (fun tag ->
      let _ht = Hedge_timer.create () in
      expect true tag);

  (* 2. Arm 10ms, wait with no fds → timer fires *)
  run "timer fires" (fun tag ->
      let ht = Hedge_timer.create () in
      Hedge_timer.arm ht ~ns:10_000_000L;
      let tf, which = Hedge_timer.wait_two ht ~fd1:(-1) ~fd2:(-1) in
      expect (tf = 1) (tag ^ Printf.sprintf ": tf=%d" tf);
      expect (which = -1) (tag ^ Printf.sprintf ": which=%d" which));

  (* 3. Pipe with data ready, arm long timer → fd fires first *)
  run "fd fires before timer" (fun tag ->
      let ht = Hedge_timer.create () in
      let rd, wr = Unix.pipe () in
      let rd_int = Fd_util.fd_to_int rd in
      (* Write data so fd is immediately ready *)
      ignore (Unix.write wr (Bytes.of_string "x") 0 1);
      (* Arm a very long timer (5 seconds) so it won't fire *)
      Hedge_timer.arm ht ~ns:5_000_000_000L;
      let tf, which = Hedge_timer.wait_two ht ~fd1:rd_int ~fd2:(-1) in
      expect (tf = 0) (tag ^ Printf.sprintf ": tf=%d (expected 0)" tf);
      expect (which = rd_int)
        (tag ^ Printf.sprintf ": which=%d (expected %d)" which rd_int);
      Unix.close rd;
      Unix.close wr);

  (* 4. Two pipes, one with data → correct fd returned *)
  run "two fds one ready" (fun tag ->
      let ht = Hedge_timer.create () in
      let rd1, wr1 = Unix.pipe () in
      let rd2, _wr2 = Unix.pipe () in
      let rd2_int = Fd_util.fd_to_int rd2 in
      let _ = rd2_int in
      (* Only write to pipe 1 *)
      ignore (Unix.write wr1 (Bytes.of_string "y") 0 1);
      let rd1_int = Fd_util.fd_to_int rd1 in
      Hedge_timer.arm ht ~ns:5_000_000_000L;
      let tf, which =
        Hedge_timer.wait_two ht ~fd1:rd1_int ~fd2:(Fd_util.fd_to_int rd2)
      in
      expect (tf = 0) (tag ^ Printf.sprintf ": tf=%d" tf);
      expect (which = rd1_int)
        (tag ^ Printf.sprintf ": which=%d (expected %d)" which rd1_int);
      Unix.close rd1;
      Unix.close wr1;
      Unix.close rd2;
      Unix.close _wr2);

  (* 5. Short timer + immediate pipe → no crash (either result ok) *)
  run "race safe" (fun tag ->
      let ht = Hedge_timer.create () in
      let rd, wr = Unix.pipe () in
      ignore (Unix.write wr (Bytes.of_string "z") 0 1);
      Hedge_timer.arm ht ~ns:1_000_000L;
      let tf, _which =
        Hedge_timer.wait_two ht ~fd1:(Fd_util.fd_to_int rd) ~fd2:(-1)
      in
      (* Either timer fired or fd was ready — both are valid *)
      expect (tf = 0 || tf = 1) (tag ^ Printf.sprintf ": tf=%d" tf);
      Unix.close rd;
      Unix.close wr);

  if !fails > 0 then (
    Printf.eprintf "[hedge-timer] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[hedge-timer] PASS %d cases\n%!" !cases
