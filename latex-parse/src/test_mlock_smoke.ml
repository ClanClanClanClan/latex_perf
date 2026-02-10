(** Smoke tests for Mlock (mlockall FFI wrapper). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[mlock] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. With L0_NO_MLOCK=1: init returns without raising *)
  run "skip via env" (fun tag ->
      Unix.putenv "L0_NO_MLOCK" "1";
      (try Mlock.init ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 2. Without env var: init returns (catches privilege errors internally) *)
  run "init graceful" (fun tag ->
      (* Remove the env var if present *)
      (try Unix.putenv "L0_NO_MLOCK" "" with _ -> ());
      (try Mlock.init ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 3. Double init is safe *)
  run "double init" (fun tag ->
      Unix.putenv "L0_NO_MLOCK" "1";
      Mlock.init ();
      Mlock.init ();
      expect true tag);

  if !fails > 0 then (
    Printf.eprintf "[mlock] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[mlock] PASS %d cases\n%!" !cases
