(** Unit tests for Net_io robust socket I/O helpers. *)

open Latex_parse_lib

(* Ignore SIGPIPE so writing to closed sockets raises an exception instead of
   killing the process. *)
let () = Sys.set_signal Sys.sigpipe Sys.Signal_ignore
let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[net-io] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. Roundtrip via socketpair *)
  run "roundtrip" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      let data = "Hello, world!" in
      let b = Bytes.of_string data in
      (match Net_io.write_all wr b 0 (Bytes.length b) with
      | Ok () -> ()
      | Error _ -> expect false (tag ^ ": write_all failed"));
      let buf = Bytes.create (String.length data) in
      (match Net_io.read_exact rd buf 0 (Bytes.length buf) with
      | Ok () -> expect (Bytes.to_string buf = data) (tag ^ ": data mismatch")
      | Error _ -> expect false (tag ^ ": read_exact failed"));
      Unix.close rd;
      Unix.close wr);

  (* 2. read_exact on closed write end → Error Eof *)
  run "read_exact Eof" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      Unix.close wr;
      let buf = Bytes.create 4 in
      (match Net_io.read_exact rd buf 0 4 with
      | Error Net_io.Eof -> ()
      | Error Net_io.Short_write -> expect false (tag ^ ": wrong error type")
      | Ok () -> expect false (tag ^ ": should have failed"));
      Unix.close rd);

  (* 3. read_exact len=0 → Ok () *)
  run "read_exact zero-length" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      (match Net_io.read_exact rd Bytes.empty 0 0 with
      | Ok () -> ()
      | Error _ -> expect false (tag ^ ": zero-length should succeed"));
      Unix.close rd;
      Unix.close wr);

  (* 4. write_all len=0 → Ok () *)
  run "write_all zero-length" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      (match Net_io.write_all wr Bytes.empty 0 0 with
      | Ok () -> ()
      | Error _ -> expect false (tag ^ ": zero-length should succeed"));
      Unix.close rd;
      Unix.close wr);

  (* 5. 64KB roundtrip *)
  run "64KB roundtrip" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      let sz = 65536 in
      let data = Bytes.init sz (fun i -> Char.chr (i land 0xFF)) in
      (* Write in a thread to avoid deadlock on full socket buffer *)
      let t =
        Thread.create
          (fun () ->
            match Net_io.write_all wr data 0 sz with
            | Ok () -> Unix.close wr
            | Error _ -> Unix.close wr)
          ()
      in
      let buf = Bytes.create sz in
      (match Net_io.read_exact rd buf 0 sz with
      | Ok () -> expect (data = buf) (tag ^ ": data mismatch")
      | Error _ -> expect false (tag ^ ": read_exact failed"));
      Thread.join t;
      Unix.close rd);

  (* 6. read_exact_exn raises Failure on closed fd *)
  run "read_exact_exn raises" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      Unix.close wr;
      let buf = Bytes.create 4 in
      (try
         Net_io.read_exact_exn rd buf 0 4;
         expect false (tag ^ ": should have raised")
       with Failure _ -> ());
      Unix.close rd);

  (* 7. write_all_exn raises Failure on closed read end *)
  run "write_all_exn raises" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      Unix.close rd;
      (* Write enough to trigger EPIPE/Eof *)
      let big = Bytes.make 65536 'x' in
      (try
         Net_io.write_all_exn wr big 0 (Bytes.length big);
         (* Might not raise on first call; try again *)
         Net_io.write_all_exn wr big 0 (Bytes.length big);
         expect false (tag ^ ": should have raised")
       with Failure _ | Unix.Unix_error _ -> ());
      Unix.close wr);

  (* 8. error_to_string coverage *)
  run "error_to_string" (fun tag ->
      let s1 = Net_io.error_to_string Eof in
      let s2 = Net_io.error_to_string Short_write in
      expect (String.length s1 > 0) (tag ^ ": Eof msg");
      expect (String.length s2 > 0) (tag ^ ": Short_write msg"));

  (* 9. Chunked delivery via thread *)
  run "chunked delivery" (fun tag ->
      let rd, wr = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      let _ =
        Thread.create
          (fun () ->
            let b = Bytes.of_string "ABCDE" in
            ignore (Net_io.write_all wr b 0 5);
            Unix.sleepf 0.010;
            let b2 = Bytes.of_string "FGHIJ" in
            ignore (Net_io.write_all wr b2 0 5);
            Unix.close wr)
          ()
      in
      let buf = Bytes.create 10 in
      (match Net_io.read_exact rd buf 0 10 with
      | Ok () ->
          expect (Bytes.to_string buf = "ABCDEFGHIJ") (tag ^ ": data mismatch")
      | Error _ -> expect false (tag ^ ": read_exact failed"));
      Unix.close rd);

  if !fails > 0 then (
    Printf.eprintf "[net-io] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[net-io] PASS %d cases\n%!" !cases
