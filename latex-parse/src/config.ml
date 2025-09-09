let page_bytes                   = 4096

(* Hedging *)
let hedge_timer_ms_default       = 10    (* best result in your final 100k run *)
let require_simd                 = false (* refuse to start if SIMD missing unless L0_ALLOW_SCALAR=1 *)

(* GC / rotation budgets (per worker, since last spawn) *)
let minor_heap_bytes             = 256 * 1024 * 1024
let gc_space_overhead            = 10_000
let gc_max_overhead              = 10_000
let gc_full_major_budget_mb      = 256

(* Per-spawn deltas, not cumulative forever *)
let worker_alloc_budget_mb       = 5000   (* 5 GB since spawn, then rotate *)
let worker_major_cycles_budget   = 50     (* full majors since spawn, then rotate *)

(* Arena: 3M tokens ~ 48MB per arena; double buffer ~ 96MB *)
let arenas_tokens_cap            = 3_000_000

(* Service socket *)
let service_sock_path            = "/tmp/l0_lex_svc.sock"

(* Limits *)
let max_req_bytes                = 2 * 1024 * 1024

(* Tail CSV *)
let tail_csv_path                = "/tmp/l0_service_tail.csv"
let tail_trace_keep              = 100

let pool_cores                   = [|0;1|]

(* A+B microbench conservative invariants (simd_v2 spec) *)
let ab_expected_tokens_min       = 900_000
let ab_expected_tokens_max       = 1_050_000
let ab_p999_target_ms            = 15.0