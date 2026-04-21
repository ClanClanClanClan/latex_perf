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
  execution_class : Rule_contract_loader.execution_class;
      (** PR #241 (p1.6, memo §11.2): per-class priority offset ensures Class A
          tasks outrank B, which outrank C, which outrank D. Sort key is
          [priority + class_priority_offset execution_class]. *)
}

val class_priority_offset : Rule_contract_loader.execution_class -> float
(** Per-class offset added during [drain] sort. A=0, B=1e6, C=2e6, D=3e6. *)

val effective_priority : task -> float
(** [priority + class_priority_offset execution_class]. *)

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
