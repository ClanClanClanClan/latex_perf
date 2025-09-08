(* Comprehensive integration test for v25_R1 + SIMD.md enhancements *)

open L0_lexer

let test_basic_functionality () =
  Printf.printf "\n=== TEST 1: Basic Functionality ===\n";
  
  (* Test document *)
  let doc = Bytes.of_string "\\documentclass{article}\\begin{document}Hello\\end{document}" in
  let arena = Arena.create_arena () in
  
  (* Test real processor *)
  let (tokens, _digest, process_ns) = Real_processor.run doc arena in
  Printf.printf "Tokens: %d, Process time: %.3fms\n" 
    tokens (Int64.to_float process_ns /. 1_000_000.0);
  
  assert (tokens > 0);
  Printf.printf "✅ Basic tokenization works\n"

let test_timing_stamps () =
  Printf.printf "\n=== TEST 2: 5-Stamp Timing ===\n";
  
  let st = Service_bracket.make () in
  Unix.sleepf 0.001;
  let st = Service_bracket.stamp_in_done st in
  Unix.sleepf 0.001;
  let st = Service_bracket.stamp_proc_start st in
  Unix.sleepf 0.001;
  let st = Service_bracket.stamp_hedge_fire st in
  Unix.sleepf 0.001;
  let st = Service_bracket.stamp_first_reply st in
  Unix.sleepf 0.001;
  let st = Service_bracket.stamp_reply_ready st in
  
  Printf.printf "t_in_start: %Ld\n" st.Service_bracket.t_in_start;
  Printf.printf "t_in_done: %Ld\n" st.t_in_done;
  Printf.printf "t_proc_start: %Ld\n" st.t_proc_start;
  Printf.printf "t_hedge_fire: %Ld\n" st.t_hedge_fire;
  Printf.printf "t_first_reply: %Ld\n" st.t_first_reply;
  Printf.printf "t_reply_ready: %Ld\n" st.t_reply_ready;
  
  assert (st.t_in_done > st.t_in_start);
  assert (st.t_proc_start > st.t_in_done);
  assert (st.t_hedge_fire > st.t_proc_start);
  assert (st.t_first_reply > st.t_hedge_fire);
  assert (st.t_reply_ready > st.t_first_reply);
  Printf.printf "✅ All 5 timestamps captured in order\n"

let test_hedge_timer () =
  Printf.printf "\n=== TEST 3: Event-Driven Hedge Timer ===\n";
  
  let timer = Hedge_timer.create () in
  Printf.printf "Timer created\n";
  
  (* Arm for 10ms *)
  Hedge_timer.arm_ms timer 10;
  Printf.printf "Timer armed for 10ms\n";
  assert (Hedge_timer.is_armed timer);
  
  (* Disarm *)
  Hedge_timer.disarm timer;
  Printf.printf "Timer disarmed\n";
  assert (not (Hedge_timer.is_armed timer));
  
  Printf.printf "✅ Hedge timer arms/disarms correctly\n"

let test_metrics_logger () =
  Printf.printf "\n=== TEST 4: Metrics Logger ===\n";
  
  let metrics = Metrics_logger.create ~keep:10 in
  
  (* Add some test metrics *)
  for i = 1 to 20 do
    let row = {
      Metrics_logger.ms_total = float i;
      t_in_start = Int64.of_int (i * 1000);
      t_in_done = Int64.of_int (i * 2000);
      t_proc_start = Int64.of_int (i * 3000);
      t_hedge_fire = if i mod 2 = 0 then Int64.of_int (i * 4000) else 0L;
      t_first_reply = Int64.of_int (i * 5000);
      t_reply_ready = Int64.of_int (i * 6000);
      hedged = (i mod 2 = 0);
      origin = if i mod 2 = 0 then "H" else "P";
    } in
    Metrics_logger.note metrics row
  done;
  
  (* Test hedge tracking *)
  Metrics_logger.bump_hedge metrics ~win:true;
  Metrics_logger.bump_hedge metrics ~win:false;
  Metrics_logger.set_rotations metrics 5;
  
  (* Export CSV *)
  Metrics_logger.dump_csv metrics "test_metrics.csv";
  
  (* Check file exists *)
  let exists = Sys.file_exists "test_metrics.csv" in
  if exists then begin
    Printf.printf "✅ Metrics CSV exported successfully\n";
    Sys.remove "test_metrics.csv"
  end else
    Printf.printf "❌ CSV export failed\n"

let test_broker_hedging () =
  Printf.printf "\n=== TEST 5: Broker Hedging Logic ===\n";
  
  let broker = Broker.create_broker "/tmp/test_p.sock" "/tmp/test_s.sock" in
  let doc = Bytes.of_string "\\documentclass{article}\\begin{document}Test\\end{document}" in
  
  (* Test with different hedge thresholds *)
  let result1 = Broker.hedged_call broker ~input:doc ~hedge_ms:1 in
  Printf.printf "Fast hedge (1ms): origin=%s, tokens=%d\n" 
    (match result1.origin with `P -> "P" | `H -> "H") result1.n_tokens;
  
  let result2 = Broker.hedged_call broker ~input:doc ~hedge_ms:1000 in
  Printf.printf "Slow hedge (1000ms): origin=%s, tokens=%d\n"
    (match result2.origin with `P -> "P" | `H -> "H") result2.n_tokens;
  
  let rate = Broker.get_hedge_rate broker in
  Printf.printf "Hedge rate: %.1f%%\n" rate;
  
  (* Hedge rate should be between 0 and 100, not always 100 *)
  if rate = 100.0 then
    Printf.printf "⚠️  WARNING: Hedge rate is 100%% - hedging logic needs fix\n"
  else
    Printf.printf "✅ Hedge rate is reasonable\n"

let load_perf_corpus () =
  let path = "corpora/perf/perf_smoke_big.tex" in
  if Sys.file_exists path then begin
    let ic = open_in_bin path in
    let len = in_channel_length ic in
    let content = Bytes.create len in
    really_input ic content 0 len;
    close_in ic;
    Some content
  end else None

let test_performance_p99 () =
  Printf.printf "\n=== TEST 6: Performance P99.9 Measurement ===\n";
  
  match load_perf_corpus () with
  | None -> Printf.printf "❌ Cannot find perf_smoke_big.tex\n"
  | Some doc ->
    let iterations = 100 in (* Reduced for testing - would be 100k for production *)
    Printf.printf "Running %d iterations on perf_smoke_big.tex...\n" iterations;
    
    let broker = Broker.create_broker "/tmp/perf_p.sock" "/tmp/perf_s.sock" in
    let measurements = Array.make iterations 0.0 in
    
    for i = 0 to iterations - 1 do
      let t0 = Clock.now_ns () in
      let _result = Broker.hedged_call broker ~input:doc ~hedge_ms:12 in
      let t1 = Clock.now_ns () in
      measurements.(i) <- Int64.to_float (Int64.sub t1 t0) /. 1_000_000.0;
      
      if (i + 1) mod 10 = 0 then
        Printf.printf "  %d/%d iterations\n%!" (i + 1) iterations
    done;
    
    (* Calculate percentiles *)
    Array.sort Float.compare measurements;
    let p50_idx = iterations / 2 in
    let p99_idx = iterations * 99 / 100 in
    let p999_idx = min (iterations - 1) (iterations * 999 / 1000) in
    let mean = Array.fold_left (+.) 0.0 measurements /. float iterations in
    
    Printf.printf "\nResults (%d iterations):\n" iterations;
    Printf.printf "  Mean: %.3fms\n" mean;
    Printf.printf "  P50:  %.3fms\n" measurements.(p50_idx);
    Printf.printf "  P99:  %.3fms\n" measurements.(p99_idx);
    Printf.printf "  P99.9: %.3fms (approximated from %d samples)\n" measurements.(p999_idx) iterations;
    Printf.printf "  Hedge rate: %.1f%%\n" (Broker.get_hedge_rate broker);
    
    (* Check against SIMD.md acceptance gates *)
    if measurements.(p999_idx) <= 20.0 then
      Printf.printf "✅ P99.9 ≤ 20ms acceptance gate PASSED\n"
    else
      Printf.printf "❌ P99.9 > 20ms acceptance gate FAILED (%.3fms)\n" measurements.(p999_idx)

let () =
  Printf.printf "=== V25_R1 + SIMD.md Integration Test Suite ===\n";
  
  test_basic_functionality ();
  test_timing_stamps ();
  test_hedge_timer ();
  test_metrics_logger ();
  test_broker_hedging ();
  test_performance_p99 ();
  
  Printf.printf "\n=== Test Suite Complete ===\n"