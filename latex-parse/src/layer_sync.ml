(* ══════════════════════════════════════════════════════════════════════
   Layer_sync — cross-layer consistency & synchronisation protocol (spec §5)

   Key concepts: - Version Vector: each artefact carries {gen; parent_gen}.
   Layer N accepts deltas iff parent_gen = Layer(N-1).gen. - Memory Barrier:
   Elder orchestrator performs swap-and-publish under an Atomic generation
   counter; validators read a snapshot by Arc handle. - Rollback: on error,
   Elder rolls back child layer only; parent artefacts remain valid. -
   Consistency Window: at most one generation; validators observe either old or
   new snapshot, never interleaved.
   ══════════════════════════════════════════════════════════════════════ *)

type layer_id = L0 | L1 | L2 | L3 | L4
type version_vector = { gen : int; parent_gen : int }
type 'a layer_state = { layer : layer_id; version : version_vector; data : 'a }
type 'a snapshot = { generation : int; states : 'a layer_state list }

(* ── Generation counter (atomic for cross-domain safety) ─────── *)

let _generation = Atomic.make 0
let next_gen () = Atomic.fetch_and_add _generation 1
let current_gen () = Atomic.get _generation

(* ── Version vector operations ──────────────────────────────── *)

let mk_version ~gen ~parent_gen = { gen; parent_gen }
let initial_version = { gen = 0; parent_gen = 0 }

let accepts_delta (parent : version_vector) (child : version_vector) : bool =
  child.parent_gen = parent.gen

let advance (parent : version_vector) : version_vector =
  { gen = next_gen (); parent_gen = parent.gen }

(* ── Snapshot operations ────────────────────────────────────── *)

let create_snapshot (states : 'a layer_state list) : 'a snapshot =
  { generation = current_gen (); states }

let layer_of_snapshot (snap : 'a snapshot) (lid : layer_id) :
    'a layer_state option =
  List.find_opt (fun s -> s.layer = lid) snap.states

(* ── Rollback ───────────────────────────────────────────────── *)

type rollback_result = Rolled_back | No_rollback_needed

let rollback_child (snap : 'a snapshot) (child_layer : layer_id) :
    'a snapshot * rollback_result =
  let new_states = List.filter (fun s -> s.layer <> child_layer) snap.states in
  if List.length new_states < List.length snap.states then
    ({ generation = snap.generation; states = new_states }, Rolled_back)
  else (snap, No_rollback_needed)

(* ── Consistency check ──────────────────────────────────────── *)

let is_consistent (snap : 'a snapshot) : bool =
  let sorted =
    List.sort
      (fun a b ->
        compare
          (match a.layer with L0 -> 0 | L1 -> 1 | L2 -> 2 | L3 -> 3 | L4 -> 4)
          (match b.layer with L0 -> 0 | L1 -> 1 | L2 -> 2 | L3 -> 3 | L4 -> 4))
      snap.states
  in
  let rec check_pairs = function
    | [] | [ _ ] -> true
    | parent :: (child :: _ as rest) ->
        accepts_delta parent.version child.version && check_pairs rest
  in
  check_pairs sorted
