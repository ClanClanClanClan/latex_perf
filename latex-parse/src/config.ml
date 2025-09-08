let page_bytes                   = 4096

(* Hedging *)
let hedge_timer_ms_default       = 10

(* GC / rotation budgets (per worker, since last spawn) *)
let minor_heap_bytes             = 256 * 1024 * 1024
let gc_space_overhead            = 10_000
let gc_max_overhead              = 10_000
let gc_full_major_budget_mb      = 256   (* trigger occasional full_major off-path *)

(* Important: these are per-spawn deltas, not cumulative forever *)
let worker_alloc_budget_mb       = 5000   (* 5 GB since spawn, then rotate *)
let worker_major_cycles_budget   = 50     (* 50 majors since spawn, then rotate *)

(* Arena: 3M tokens ~ 48MB per arena; double buffer ~ 96MB *)
let arenas_tokens_cap            = 3_000_000

(* Service socket *)
let service_sock_path            = "/tmp/l0_lex_svc.sock"

(* Limits *)
let max_req_bytes                = 2 * 1024 * 1024

(* Tail CSV *)
let tail_csv_path                = "/tmp/l0_service_tail.csv"
let tail_trace_keep              = 100

(* Pool: pick 2 cores (logical ids). macOS pinning is advisory. *)
let pool_cores                   = [|0;1|]

(* SIMD requirements *)
let require_simd_in_ci = match Sys.getenv_opt "CI" with Some _ -> true | None -> false