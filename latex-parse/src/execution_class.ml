(* ══════════════════════════════════════════════════════════════════════
   Execution_class — rule execution class taxonomy (v26 spec §6)
   ══════════════════════════════════════════════════════════════════════ *)

type t = A | B | C | D

(* Class C rules — log-dependent. Kept as a hardcoded hot-path table so
   [classify] doesn't pay the contract-loader cost when routing build-log work,
   and so the list stays readable for audit. CI drift gate
   [scripts/tools/check_rule_contracts.py] verifies this list matches the
   [execution_class: C] entries in rule_contracts.yaml. *)
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

(** PR #241 (p1.2): [classify] now returns the real A/B/C/D class for every rule
    by consulting [Rule_contract_loader]. The fast-path hardcoded C table is
    kept as a sanity check; when the contract agrees (the common case) we still
    return [C] without touching the contract loader. Rules absent from the
    contract (internal utility IDs like "no_tabs") default to [A] — safe on the
    hot path. *)
let classify (id : string) : t =
  if Hashtbl.mem _class_c_tbl id then C
  else
    match Rule_contract_loader.find_opt id with
    | Some c -> (
        match c.execution_class with
        | Rule_contract_loader.A -> A
        | Rule_contract_loader.B -> B
        | Rule_contract_loader.C -> C
        | Rule_contract_loader.D -> D)
    | None -> A

let is_keystroke_safe = function A | B -> true | C | D -> false
let to_string = function A -> "A" | B -> "B" | C -> "C" | D -> "D"
