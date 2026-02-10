(** Unit tests for Fd_util safe fd-to-int conversion. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[fd-util] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  run "stdin = 0" (fun tag -> expect (Fd_util.fd_to_int Unix.stdin = 0) tag);

  run "stdout = 1" (fun tag -> expect (Fd_util.fd_to_int Unix.stdout = 1) tag);

  run "stderr = 2" (fun tag -> expect (Fd_util.fd_to_int Unix.stderr = 2) tag);

  run "roundtrip pipe fd" (fun tag ->
      let rd, wr = Unix.pipe () in
      let n = Fd_util.fd_to_int rd in
      let fd' = Fd_util.int_to_fd n in
      (* fstat should work on the reconverted fd *)
      (try
         ignore (Unix.fstat fd');
         ()
       with Unix.Unix_error _ -> expect false (tag ^ ": fstat failed"));
      Unix.close rd;
      Unix.close wr);

  run "pipe fd >= 3" (fun tag ->
      let rd, wr = Unix.pipe () in
      let n = Fd_util.fd_to_int rd in
      expect (n >= 3) (tag ^ Printf.sprintf ": got %d" n);
      Unix.close rd;
      Unix.close wr);

  run "double roundtrip" (fun tag ->
      let rd, wr = Unix.pipe () in
      let n1 = Fd_util.fd_to_int rd in
      let fd' = Fd_util.int_to_fd n1 in
      let n2 = Fd_util.fd_to_int fd' in
      expect (n1 = n2) (tag ^ Printf.sprintf ": %d <> %d" n1 n2);
      Unix.close rd;
      Unix.close wr);

  if !fails > 0 then (
    Printf.eprintf "[fd-util] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[fd-util] PASS %d cases\n%!" !cases
