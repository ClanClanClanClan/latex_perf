(** Service-wide configuration constants.

    Tuning parameters for the GC, worker lifecycle, arena sizing, networking,
    and performance invariants. Environment overrides are noted where
    applicable. *)

(** {2 Memory / page size} *)

val page_bytes : int

(** {2 Hedge timer} *)

val hedge_timer_ms_default : int

(** {2 SIMD guard} *)

val require_simd : bool

(** {2 GC tuning}

    [minor_heap_bytes] respects [L0_MINOR_HEAP_MB] env override. *)

val minor_heap_bytes : int
val gc_space_overhead : int
val gc_max_overhead : int
val gc_full_major_budget_mb : int

(** {2 Worker lifecycle} *)

val worker_alloc_budget_mb : int
val worker_major_cycles_budget : int

(** {2 Arena capacity} *)

val arenas_tokens_cap : int

(** {2 Service socket} *)

val service_sock_path : string

(** {2 Request limits} *)

val max_req_bytes : int

(** {2 Tail-latency CSV tracing} *)

val tail_csv_path : string
val tail_trace_keep : int
val pool_cores : int array

(** {2 A+B microbench invariants (simd_v2 spec)} *)

val ab_expected_tokens_min : int
val ab_expected_tokens_max : int
val ab_p999_target_ms : float
