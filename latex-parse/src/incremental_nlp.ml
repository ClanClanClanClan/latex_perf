(* ══════════════════════════════════════════════════════════════════════
   Incremental_nlp — sentence-level diff detection for NLP pipeline (spec W76)

   Only re-process changed sentences through the NLP pipeline. Compares old and
   new sentence lists, identifies additions, deletions, and modifications, and
   returns only the delta for processing.
   ══════════════════════════════════════════════════════════════════════ *)

type sentence_id = int

type sentence_change =
  | Added of { id : sentence_id; text : string }
  | Removed of { id : sentence_id }
  | Modified of { id : sentence_id; old_text : string; new_text : string }

type diff_result = {
  changes : sentence_change list;
  unchanged_count : int;
  total_old : int;
  total_new : int;
}

(** Compute sentence-level diff between old and new document. Uses
    sentence_split.ml for boundary detection, then compares sentence texts for
    equality. *)
let compute_diff (old_src : string) (new_src : string) : diff_result =
  let old_sents = Sentence_split.split old_src in
  let new_sents = Sentence_split.split new_src in
  let old_texts =
    List.mapi (fun i (s : Sentence_split.sentence) -> (i, s.text)) old_sents
  in
  let new_texts =
    List.mapi (fun i (s : Sentence_split.sentence) -> (i, s.text)) new_sents
  in
  let old_set = Hashtbl.create (List.length old_texts) in
  List.iter (fun (i, t) -> Hashtbl.replace old_set t i) old_texts;
  let new_set = Hashtbl.create (List.length new_texts) in
  List.iter (fun (i, t) -> Hashtbl.replace new_set t i) new_texts;
  let changes = ref [] in
  let unchanged = ref 0 in
  (* Find added and modified sentences *)
  List.iter
    (fun (new_id, new_text) ->
      if Hashtbl.mem old_set new_text then incr unchanged
      else changes := Added { id = new_id; text = new_text } :: !changes)
    new_texts;
  (* Find removed sentences *)
  List.iter
    (fun (old_id, old_text) ->
      if not (Hashtbl.mem new_set old_text) then
        changes := Removed { id = old_id } :: !changes)
    old_texts;
  {
    changes = List.rev !changes;
    unchanged_count = !unchanged;
    total_old = List.length old_sents;
    total_new = List.length new_sents;
  }

(** Return only the sentences that need NLP re-processing. *)
let sentences_to_process (diff : diff_result) : (sentence_id * string) list =
  List.filter_map
    (fun change ->
      match change with
      | Added { id; text } -> Some (id, text)
      | Modified { id; new_text; _ } -> Some (id, new_text)
      | Removed _ -> None)
    diff.changes

(** Percentage of sentences that were unchanged (cache hit rate). *)
let cache_hit_rate (diff : diff_result) : float =
  if diff.total_new = 0 then 1.0
  else float_of_int diff.unchanged_count /. float_of_int diff.total_new
