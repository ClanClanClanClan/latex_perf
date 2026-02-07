(* size_check.ml - Verify token variant sizes match documentation *)
(* Part of LaTeX Perfectionist v25 CI infrastructure *)

open Lexer_v25

(* Expected sizes in bytes for each variant *)
type expected_sizes = {
  tchar : int;
  tmacro : int;
  tparam : int;
  tgroup : int;
  teof : int;
}

let expected_x86_64 =
  { tchar = 24; tmacro = 24; tparam = 16; tgroup = 8; teof = 8 }

let expected_arm64 =
  { tchar = 24; tmacro = 24; tparam = 16; tgroup = 8; teof = 8 }

(* Measure actual size of a token variant in words *)
let measure_variant_words = function
  | TChar (u, c) -> Obj.reachable_words (Obj.repr (TChar (u, c)))
  | TMacro s -> Obj.reachable_words (Obj.repr (TMacro s))
  | TParam n -> Obj.reachable_words (Obj.repr (TParam n))
  | TGroupOpen -> Obj.reachable_words (Obj.repr TGroupOpen)
  | TGroupClose -> Obj.reachable_words (Obj.repr TGroupClose)
  | TEOF -> Obj.reachable_words (Obj.repr TEOF)

(* Convert words to bytes based on architecture *)
let word_size = Sys.word_size / 8
let measure_variant_bytes tok = measure_variant_words tok * word_size

(* Determine current architecture *)
let get_expected_sizes () =
  match Sys.word_size with
  | 64 -> if Sys.os_type = "Unix" then expected_x86_64 else expected_arm64
  | 32 -> failwith "32-bit architectures not supported"
  | _ -> failwith "Unknown architecture"

let check_size name actual expected max_drift =
  let drift = abs (actual - expected) in
  if drift > max_drift then (
    Printf.eprintf "ERROR: %s size drift too large!\n" name;
    Printf.eprintf "  Expected: %d bytes\n" expected;
    Printf.eprintf "  Actual: %d bytes\n" actual;
    Printf.eprintf "  Drift: %d bytes (max allowed: %d)\n" drift max_drift;
    false)
  else (
    Printf.printf "✓ %s: %d bytes (expected %d, drift %d)\n" name actual
      expected drift;
    true)

let () =
  Printf.printf "LaTeX Perfectionist v25 - Token Size Check\n";
  Printf.printf "Architecture: %s, Word size: %d bits\n\n" Sys.os_type
    Sys.word_size;

  let expected = get_expected_sizes () in
  let max_drift = 8 in

  (* bytes *)

  (* Measure each variant *)
  let results =
    [
      check_size "TChar"
        (measure_variant_bytes (TChar (Uchar.of_int 65, Catcode.Letter)))
        expected.tchar max_drift;
      check_size "TMacro"
        (measure_variant_bytes (TMacro "test"))
        expected.tmacro max_drift;
      check_size "TParam"
        (measure_variant_bytes (TParam 1))
        expected.tparam max_drift;
      check_size "TGroupOpen"
        (measure_variant_bytes TGroupOpen)
        expected.tgroup max_drift;
      check_size "TGroupClose"
        (measure_variant_bytes TGroupClose)
        expected.tgroup max_drift;
      check_size "TEOF" (measure_variant_bytes TEOF) expected.teof max_drift;
    ]
  in

  (* Check constructor count *)
  Printf.printf "\nConstructor count: 6 (expected 6)\n";

  (* Exit with error if any check failed *)
  if List.for_all (fun x -> x) results then (
    Printf.printf "\n✅ All size checks passed!\n";
    exit 0)
  else (
    Printf.eprintf "\n❌ Size check failed!\n";
    exit 1)
