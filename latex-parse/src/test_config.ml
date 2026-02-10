(** Sanity checks for Config constants. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[config] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  run "page_bytes = 4096" (fun tag -> expect (Config.page_bytes = 4096) tag);

  run "hedge_timer_ms_default > 0" (fun tag ->
      expect (Config.hedge_timer_ms_default > 0) tag);

  run "minor_heap_bytes > 0" (fun tag ->
      expect (Config.minor_heap_bytes > 0) tag);

  run "minor_heap_bytes multiple of 1024" (fun tag ->
      expect (Config.minor_heap_bytes mod 1024 = 0) tag);

  run "gc_space_overhead > 0" (fun tag ->
      expect (Config.gc_space_overhead > 0) tag);

  run "gc_max_overhead > 0" (fun tag -> expect (Config.gc_max_overhead > 0) tag);

  run "gc_full_major_budget_mb > 0" (fun tag ->
      expect (Config.gc_full_major_budget_mb > 0) tag);

  run "worker_alloc_budget_mb > 0" (fun tag ->
      expect (Config.worker_alloc_budget_mb > 0) tag);

  run "worker_major_cycles_budget > 0" (fun tag ->
      expect (Config.worker_major_cycles_budget > 0) tag);

  run "arenas_tokens_cap > 0" (fun tag ->
      expect (Config.arenas_tokens_cap > 0) tag);

  run "service_sock_path valid" (fun tag ->
      expect (String.length Config.service_sock_path > 0) (tag ^ ": non-empty");
      expect (Config.service_sock_path.[0] = '/') (tag ^ ": starts with /"));

  run "max_req_bytes bounded" (fun tag ->
      expect (Config.max_req_bytes > 0) (tag ^ ": > 0");
      expect (Config.max_req_bytes <= 100 * 1024 * 1024) (tag ^ ": <= 100MB"));

  run "tail_trace_keep > 0" (fun tag -> expect (Config.tail_trace_keep > 0) tag);

  run "pool_cores non-empty" (fun tag ->
      expect (Array.length Config.pool_cores > 0) tag);

  run "ab_expected_tokens ordered" (fun tag ->
      expect (Config.ab_expected_tokens_min < Config.ab_expected_tokens_max) tag);

  run "ab_p999_target_ms > 0" (fun tag ->
      expect (Config.ab_p999_target_ms > 0.0) tag);

  if !fails > 0 then (
    Printf.eprintf "[config] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[config] PASS %d cases\n%!" !cases
