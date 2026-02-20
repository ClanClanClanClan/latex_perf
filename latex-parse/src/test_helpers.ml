(** Shared test helpers for all test_validators_*.ml files.

    Eliminates ~25 lines of duplicated boilerplate per test file. Each file
    chooses a [label] (e.g. "typo", "enc") and calls [finalise label] at the
    end. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

(** [expect cond msg] increments the case counter and records a failure if
    [cond] is false. *)
let expect cond msg =
  incr cases;
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" msg;
    incr fails)

(** [run msg f] generates a numbered tag and passes it to [f]. *)
let run msg f =
  let tag = Printf.sprintf "case %d: %s" (!cases + 1) msg in
  f tag

(** [find_result id src] runs all validators on [src] and returns the result for
    rule [id], if any. *)
let find_result id src =
  let results = Validators.run_all src in
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

(** [fires id src] is [true] when rule [id] fires on [src]. *)
let fires id src = find_result id src <> None

(** [fires_with_count id src n] is [true] when rule [id] fires on [src] with
    exactly [n] occurrences. *)
let fires_with_count id src expected_count =
  match find_result id src with
  | Some r -> r.count = expected_count
  | None -> false

(** [does_not_fire id src] is [true] when rule [id] does not fire on [src]. *)
let does_not_fire id src = find_result id src = None

(** [finalise label] prints a summary and exits with code 1 if any test failed.
    Call this as the last [let () = ...] in the test file. *)
let finalise label =
  Printf.printf "[%s] PASS %d cases\n%!" label !cases;
  if !fails > 0 then (
    Printf.eprintf "[%s] %d FAILURES\n%!" label !fails;
    exit 1)
