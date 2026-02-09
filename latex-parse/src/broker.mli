(** Hedged-RPC broker with worker-pool management.

    Dispatches tokenisation requests to a pool of forked worker processes using
    a hedged-request strategy: if the primary worker does not reply within
    [hedge_ms], a secondary is speculatively fired in parallel. *)

type pool
(** Opaque worker pool. *)

type svc_result = {
  status : int;
  n_tokens : int;
  issues_len : int;
  origin : [ `P | `H ];
  hedge_fired : bool;
}

val init_pool : int array -> pool
(** [init_pool cores] spawns one worker per core id. *)

val hedged_call : pool -> input:bytes -> hedge_ms:int -> svc_result
(** Send [input] to the pool with a hedge timeout of [hedge_ms] milliseconds.
    May raise [Failure] if rescue-after-HUP fails (fatal protocol violation). *)

(** {2 Monitoring accessors} *)

val requests : pool -> int
val hedge_fired_count : pool -> int
val hedge_wins_count : pool -> int
val rotations_count : pool -> int
