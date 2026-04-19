(* ══════════════════════════════════════════════════════════════════════
   Execution_class — rule execution class taxonomy (v26 spec §6)
   ══════════════════════════════════════════════════════════════════════ *)

type t = A | B | C | D

let _class_c_ids =
  [
    "FIG-020";
    "LAY-001";
    "LAY-002";
    "LAY-003";
    "LAY-004";
    "LAY-006";
    "LAY-009";
    "LAY-011";
    "LAY-017";
    "LAY-018";
    "LAY-021";
    "MATH-026";
    "MATH-027";
    "TIKZ-002";
    "LAY-025";
    "LAY-026";
    "LAY-027";
  ]

let _class_c_tbl : (string, unit) Hashtbl.t =
  let tbl = Hashtbl.create 16 in
  List.iter (fun id -> Hashtbl.replace tbl id ()) _class_c_ids;
  tbl

let classify (id : string) : t = if Hashtbl.mem _class_c_tbl id then C else A
let is_keystroke_safe = function A | B -> true | C | D -> false
let to_string = function A -> "A" | B -> "B" | C -> "C" | D -> "D"
