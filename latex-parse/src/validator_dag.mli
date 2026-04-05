(** Validator dependency graph + conflict resolution (spec §6.1). *)

type phase = L0 | L1 | L2 | L3 | L4

type validator_meta = {
  id : string;
  phase : phase;
  provides : string list;
  requires : string list;
  conflicts : string list;
}

type dag = {
  nodes : validator_meta list;
  edges : (string * string) list;
  topo_order : string list;
}

type conflict = { rule_a : string; rule_b : string; reason : string }

val phase_ordinal : phase -> int
val phase_of_string : string -> phase
val build_dag : validator_meta list -> (dag, string) result
val detect_conflicts : validator_meta list -> conflict list
val resolve_conflict : validator_meta -> validator_meta -> int -> int -> string
val default_meta : string -> phase -> validator_meta
