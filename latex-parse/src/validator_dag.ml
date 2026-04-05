(* ══════════════════════════════════════════════════════════════════════
   Validator_dag — dependency graph + conflict resolution (spec §6.1)

   Each validator declares: - id: unique rule identifier - phase: execution
   layer (L0..L4) - provides: list of capabilities this rule provides -
   requires: list of capabilities this rule depends on - conflicts: list of rule
   IDs this rule conflicts with

   A static DAG is built at start-up; cycles cause bootstrap failure. Conflicts
   resolve by priority tuple: (severity, phase_ordinal, id_lex).
   ══════════════════════════════════════════════════════════════════════ *)

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
  edges : (string * string) list; (* (from, to) = from depends on to *)
  topo_order : string list; (* topological execution order *)
}

(* ── Phase ordering ─────────────────────────────────────────────── *)

let phase_ordinal = function L0 -> 0 | L1 -> 1 | L2 -> 2 | L3 -> 3 | L4 -> 4

let phase_of_string = function
  | "L0" | "L0_Lexer" -> L0
  | "L1" | "L1_Expanded" -> L1
  | "L2" | "L2_Ast" -> L2
  | "L3" | "L3_Semantics" -> L3
  | "L4" | "L4_Style" -> L4
  | _ -> L0

(* ── DAG construction ───────────────────────────────────────────── *)

let build_dag (metas : validator_meta list) : (dag, string) result =
  (* Build capability → provider index *)
  let providers = Hashtbl.create 64 in
  List.iter
    (fun m ->
      List.iter (fun cap -> Hashtbl.replace providers cap m.id) m.provides)
    metas;
  (* Build edges: if rule A requires capability C, and rule B provides C, then A
     depends on B → edge (A, B) *)
  let edges = ref [] in
  List.iter
    (fun m ->
      List.iter
        (fun req ->
          match Hashtbl.find_opt providers req with
          | Some provider_id when provider_id <> m.id ->
              edges := (m.id, provider_id) :: !edges
          | _ -> ())
        m.requires)
    metas;
  let edges = !edges in
  (* Topological sort via Kahn's algorithm *)
  let n = List.length metas in
  let id_to_meta = Hashtbl.create n in
  List.iter (fun m -> Hashtbl.replace id_to_meta m.id m) metas;
  let in_degree = Hashtbl.create n in
  List.iter (fun m -> Hashtbl.replace in_degree m.id 0) metas;
  List.iter
    (fun (from_id, _to_id) ->
      let d = Hashtbl.find in_degree from_id in
      Hashtbl.replace in_degree from_id (d + 1))
    edges;
  (* Initialize queue with nodes of in-degree 0 *)
  let queue = Queue.create () in
  Hashtbl.iter (fun id d -> if d = 0 then Queue.push id queue) in_degree;
  let order = ref [] in
  let visited = ref 0 in
  while not (Queue.is_empty queue) do
    let id = Queue.pop queue in
    order := id :: !order;
    incr visited;
    (* Reduce in-degree of dependents *)
    List.iter
      (fun (from_id, to_id) ->
        if to_id = id then (
          let d = Hashtbl.find in_degree from_id in
          let d' = d - 1 in
          Hashtbl.replace in_degree from_id d';
          if d' = 0 then Queue.push from_id queue))
      edges
  done;
  if !visited < n then Error "Cycle detected in validator dependency graph"
  else Ok { nodes = metas; edges; topo_order = List.rev !order }

(* ── Conflict detection ─────────────────────────────────────────── *)

type conflict = { rule_a : string; rule_b : string; reason : string }

let detect_conflicts (metas : validator_meta list) : conflict list =
  let conflicts = ref [] in
  List.iter
    (fun m ->
      List.iter
        (fun conflicting_id ->
          if
            List.exists (fun m2 -> m2.id = conflicting_id) metas
            && m.id < conflicting_id
            (* avoid duplicates *)
          then
            conflicts :=
              {
                rule_a = m.id;
                rule_b = conflicting_id;
                reason = "declared conflict";
              }
              :: !conflicts)
        m.conflicts)
    metas;
  List.rev !conflicts

(* ── Conflict resolution ────────────────────────────────────────── *)

let resolve_conflict (a : validator_meta) (b : validator_meta)
    (severity_a : int) (severity_b : int) : string =
  (* Priority tuple: (severity DESC, phase_ordinal ASC, id_lex ASC) *)
  if severity_a <> severity_b then
    if severity_a > severity_b then a.id else b.id
  else if phase_ordinal a.phase <> phase_ordinal b.phase then
    if phase_ordinal a.phase < phase_ordinal b.phase then a.id else b.id
  else if a.id < b.id then a.id
  else b.id

(* ── Default metadata for existing rules ────────────────────────── *)

let default_meta (id : string) (phase : phase) : validator_meta =
  { id; phase; provides = [ id ]; requires = []; conflicts = [] }
