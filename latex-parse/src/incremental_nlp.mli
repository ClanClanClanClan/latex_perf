(** Incremental sentence-level diff for NLP pipeline (spec W76). Only
    re-processes changed sentences, skipping unchanged ones. *)

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

val compute_diff : string -> string -> diff_result
val sentences_to_process : diff_result -> (sentence_id * string) list
val cache_hit_rate : diff_result -> float
