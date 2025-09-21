let page_bytes                   = 4096

(* Hedge timer tuned for balanced tail protection without aggressive churn. *)
let hedge_timer_ms_default       = 12
let require_simd                 = true (* refuse to start if SIMD missing unless L0_ALLOW_SCALAR=1 *)

(* GC settings revert to a roomy minor heap with gentler overheads. *)
let minor_heap_bytes             = 128 * 1024 * 1024
let gc_space_overhead            = 120
let gc_max_overhead              = 1_000
let gc_full_major_budget_mb      = 192

(* Worker lifecycle tuned to retire before memory spikes while avoiding thrash. *)
let worker_alloc_budget_mb       = 512
let worker_major_cycles_budget   = 6

(* Arena capacity sized for 1.1MB perf_smoke windows with headroom. *)
let arenas_tokens_cap            = 2_000_000

(* Service socket *)
let service_sock_path            = "/tmp/l0_lex_svc.sock"

(* Limits *)
let max_req_bytes                = 2 * 1024 * 1024

(* Tail CSV *)
let tail_csv_path                = "/tmp/l0_service_tail.csv"
let tail_trace_keep              = 100

let pool_cores                   = [|0;1;2;3|]

(* A+B microbench conservative invariants (simd_v2 spec) *)
let ab_expected_tokens_min       = 900_000
let ab_expected_tokens_max       = 1_050_000
let ab_p999_target_ms            = 15.0
