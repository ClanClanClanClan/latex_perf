(* ══════════════════════════════════════════════════════════════════════
   Execution_policy — controls which rule classes run per invocation
   ══════════════════════════════════════════════════════════════════════ *)

type t = { enable_a : bool; enable_b : bool; enable_c : bool; enable_d : bool }

let default =
  { enable_a = true; enable_b = true; enable_c = false; enable_d = false }

let with_build =
  { enable_a = true; enable_b = true; enable_c = true; enable_d = false }

(* PR #241 (memo §11): advisory path runs hot-path classes + Class D (STYLE
   family). Used by IDE/editor modes that want heuristic suggestions without a
   build profile. *)
let with_advisory =
  { enable_a = true; enable_b = true; enable_c = false; enable_d = true }

let full =
  { enable_a = true; enable_b = true; enable_c = true; enable_d = true }

let allows (p : t) (cls : Execution_class.t) : bool =
  match cls with
  | A -> p.enable_a
  | B -> p.enable_b
  | C -> p.enable_c
  | D -> p.enable_d
