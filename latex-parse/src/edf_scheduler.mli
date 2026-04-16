(** Priority-ordered scheduler for incremental validation.

    Assigns priorities based on edit proximity + layer ordinal. Chunks closer to
    the edit point and lower layers execute first. Sequential execution in this
    version; concurrent execution deferred to v26. *)

type task = {
  task_id : string;
  layer_id : int;
  chunk_id : int64;
  priority : float;  (** Lower = higher priority. NOT a wall-clock deadline. *)
  work : unit -> Validators_common.result list;
}

type scheduler

type stats = {
  tasks_executed : int;
  tasks_cancelled : int;
  avg_latency_ms : float;
  max_latency_ms : float;
}

val create : ?capacity:int -> unit -> scheduler
val compute_priority : edit_pos:int -> chunk_start:int -> layer_id:int -> float
val submit : scheduler -> task -> unit
val submit_batch : scheduler -> task list -> unit
val drain : scheduler -> Validators_common.result list
val pending_count : scheduler -> int
val cancel_chunk : scheduler -> int64 -> unit
val stats : scheduler -> stats
val reset_stats : scheduler -> unit
