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
    Thread-safe: concurrent callers are serialised (one call owns the pool, its
    timer and its sockets at a time). A worker that dies mid-request is replaced
    and the request retried once on another worker; raises [Failure] only if
    that retry also fails or a worker breaks the protocol. *)

val retire : pool -> int -> unit
(** [retire p i] waits for worker [i] to answer what it still owes, then closes
    it, reaps it and spawns its replacement. Returns once the old worker process
    has exited. *)

val worker_count : pool -> int

(** {2 Monitoring accessors} *)

val requests : pool -> int
val hedge_fired_count : pool -> int
val hedge_wins_count : pool -> int
val rotations_count : pool -> int
