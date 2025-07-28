(** Version Vector Protocol - LaTeX Perfectionist v25
    
    Implements the atomic version-vector protocol from integration resolution #88
    for cross-layer consistency guarantees.
*)

open Lwt.Syntax

(* Global version vector type *)
type t = {
  mutable σ₀ : int64;  (* L0 lexer version *)
  mutable σ₁ : int64;  (* L1 expander version *)
  mutable σ₂ : int64;  (* L2 parser version *)
  mutable σ₃ : int64;  (* L3 interpreter version *)
  mutable σ₄ : int64;  (* L4 style version *)
}

(* Immutable snapshot for transactions *)
type snapshot = {
  s₀ : int64;
  s₁ : int64;
  s₂ : int64;
  s₃ : int64;
  s₄ : int64;
}

(* Layer identifier *)
type layer = L0 | L1 | L2 | L3 | L4

(* Global version vector - single source of truth *)
let global_vector = {
  σ₀ = 0L;
  σ₁ = 0L;
  σ₂ = 0L;
  σ₃ = 0L;
  σ₄ = 0L;
}

(* Mutex for CAS operations *)
let vector_mutex = Lwt_mutex.create ()

(* Take atomic snapshot *)
let snapshot () =
  Lwt_mutex.with_lock vector_mutex (fun () ->
    Lwt.return {
      s₀ = global_vector.σ₀;
      s₁ = global_vector.σ₁;
      s₂ = global_vector.σ₂;
      s₃ = global_vector.σ₃;
      s₄ = global_vector.σ₄;
    })

(* Compare snapshots for equality *)
let equal_snapshot s1 s2 =
  s1.s₀ = s2.s₀ &&
  s1.s₁ = s2.s₁ &&
  s1.s₂ = s2.s₂ &&
  s1.s₃ = s2.s₃ &&
  s1.s₄ = s2.s₄

(* Bump version for dirty layers *)
let bump_version snap dirty_layers =
  let bump_if_dirty layer current =
    if List.mem layer dirty_layers then
      Int64.succ current
    else
      current
  in
  {
    s₀ = bump_if_dirty L0 snap.s₀;
    s₁ = bump_if_dirty L1 snap.s₁;
    s₂ = bump_if_dirty L2 snap.s₂;
    s₃ = bump_if_dirty L3 snap.s₃;
    s₄ = bump_if_dirty L4 snap.s₄;
  }

(* Transaction result *)
type tx_result = 
  | Committed
  | Retry
  | Aborted of string

(* Edit transaction context *)
type transaction = {
  id : int;
  start_snapshot : snapshot;
  mutable dirty_layers : layer list;
  mutable deltas : (layer * Obj.t) list;  (* Polymorphic deltas *)
}

(* Transaction ID counter *)
let tx_counter = ref 0

(* Begin transaction *)
let begin_transaction () =
  let* snap = snapshot () in
  incr tx_counter;
  Lwt.return {
    id = !tx_counter;
    start_snapshot = snap;
    dirty_layers = [];
    deltas = [];
  }

(* Record delta for a layer *)
let record_delta tx layer delta =
  if not (List.mem layer tx.dirty_layers) then
    tx.dirty_layers <- layer :: tx.dirty_layers;
  tx.deltas <- (layer, Obj.repr delta) :: tx.deltas

(* Commit transaction with CAS *)
let commit_transaction tx publish_fn =
  let rec try_commit retries =
    if retries > 10 then
      Lwt.return (Aborted "Too many retries")
    else
      Lwt_mutex.with_lock vector_mutex (fun () ->
        (* Get current snapshot *)
        let current = {
          s₀ = global_vector.σ₀;
          s₁ = global_vector.σ₁;
          s₂ = global_vector.σ₂;
          s₃ = global_vector.σ₃;
          s₄ = global_vector.σ₄;
        } in
        
        (* Check if base snapshot matches *)
        if equal_snapshot current tx.start_snapshot then begin
          (* Compute new version *)
          let new_snap = bump_version current tx.dirty_layers in
          
          (* Update global vector *)
          global_vector.σ₀ <- new_snap.s₀;
          global_vector.σ₁ <- new_snap.s₁;
          global_vector.σ₂ <- new_snap.s₂;
          global_vector.σ₃ <- new_snap.s₃;
          global_vector.σ₄ <- new_snap.s₄;
          
          (* Publish snapshots - this is atomic after CAS *)
          publish_fn tx.deltas;
          
          Lwt.return Committed
        end else begin
          (* Another transaction won - retry *)
          Lwt.return Retry
        end)
  in
  
  let rec retry_loop retries =
    let* result = try_commit retries in
    match result with
    | Retry ->
        (* Small delay before retry *)
        let* () = Lwt_unix.sleep 0.001 in
        retry_loop (retries + 1)
    | other -> Lwt.return other
  in
  
  retry_loop 0

(* Layer severity for error handling *)
type severity = Warn | Error | Fatal

(* Handle layer error according to protocol *)
let handle_layer_error tx layer severity error_msg =
  match severity with
  | Warn ->
      (* Continue with warning *)
      Printf.eprintf "Warning in %s: %s\n" 
        (match layer with L0 -> "L0" | L1 -> "L1" | L2 -> "L2" | L3 -> "L3" | L4 -> "L4")
        error_msg;
      `Continue
      
  | Error ->
      (* Commit lower layers, mark higher as dirty *)
      let layer_index = match layer with L0 -> 0 | L1 -> 1 | L2 -> 2 | L3 -> 3 | L4 -> 4 in
      tx.dirty_layers <- List.filter (fun l ->
        let idx = match l with L0 -> 0 | L1 -> 1 | L2 -> 2 | L3 -> 3 | L4 -> 4 in
        idx < layer_index
      ) tx.dirty_layers;
      `PartialCommit
      
  | Fatal ->
      (* Abort entire transaction *)
      `Abort

(* Helper to check if a layer's version has changed *)
let has_layer_changed snap layer =
  match layer with
  | L0 -> snap.s₀ <> global_vector.σ₀
  | L1 -> snap.s₁ <> global_vector.σ₁
  | L2 -> snap.s₂ <> global_vector.σ₂
  | L3 -> snap.s₃ <> global_vector.σ₃
  | L4 -> snap.s₄ <> global_vector.σ₄

(* Get version for specific layer *)
let get_layer_version layer =
  match layer with
  | L0 -> global_vector.σ₀
  | L1 -> global_vector.σ₁
  | L2 -> global_vector.σ₂
  | L3 -> global_vector.σ₃
  | L4 -> global_vector.σ₄

(* Debug: print current vector state *)
let debug_print () =
  Printf.printf "Version Vector: L0=%Ld L1=%Ld L2=%Ld L3=%Ld L4=%Ld\n"
    global_vector.σ₀
    global_vector.σ₁
    global_vector.σ₂
    global_vector.σ₃
    global_vector.σ₄