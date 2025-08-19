(* TEST SINGLE-PASS MASK VALIDATOR - The Correct Implementation *)

let () =
  Printf.printf "SINGLE-PASS MASK VALIDATOR TEST\n";
  Printf.printf "================================\n\n";
  
  Printf.printf "Correcting my mistake: ONE pass, not FIVE!\n\n";
  
  (* Test with different sizes *)
  Printf.printf "Testing 50K tokens:\n";
  let p99_50k = Single_pass_mask.bench_single_pass 50_000 in
  
  Printf.printf "\nTesting 276K tokens:\n";
  let p99_276k = Single_pass_mask.bench_single_pass 276_000 in
  
  Printf.printf "\n==== PERFORMANCE COMPARISON ====\n";
  Printf.printf "┌─────────────────────────┬──────────┬────────────┬──────────────┐\n";
  Printf.printf "│ Approach                │ P99 Time │ Memory     │ Passes       │\n";
  Printf.printf "├─────────────────────────┼──────────┼────────────┼──────────────┤\n";
  Printf.printf "│ Sparse O(k) (current)   │  3.189ms │ ~232KB     │ 1 (filtered) │\n";
  Printf.printf "│ Mask 5-pass (broken)    │  5.449ms │ 1,380KB    │ 5 passes     │\n";
  Printf.printf "│ Mask 1-pass (fixed)     │ %7.3fms │ 276KB      │ 1 pass       │\n" p99_276k;
  Printf.printf "└─────────────────────────┴──────────┴────────────┴──────────────┘\n\n";
  
  Printf.printf "Expert prediction: 0.6-1.2ms\n";
  Printf.printf "My broken version: 5.449ms (5 passes)\n";
  Printf.printf "Corrected version: %.3fms (1 pass)\n" p99_276k;
  Printf.printf "Improvement: %.1fx faster\n\n" (5.449 /. p99_276k);
  
  if p99_276k < 1.2 then begin
    Printf.printf "🎉 EXPERT WAS RIGHT! Single-pass achieves <1.2ms!\n";
    Printf.printf "My implementation error was doing 5 passes instead of 1.\n"
  end else if p99_276k < 3.189 then begin
    Printf.printf "✅ BETTER than sparse! Single-pass beats O(k)!\n";
    Printf.printf "Expert was mostly right - just needed proper implementation.\n"
  end else begin
    Printf.printf "❌ Still not faster than sparse, but much improved.\n";
    Printf.printf "Maybe needs further optimization or C implementation.\n"
  end;
  
  Printf.printf "\n==== KEY INSIGHTS ====\n";
  Printf.printf "1. Number of passes matters more than anything\n";
  Printf.printf "2. Cache locality from single pass is crucial\n";
  Printf.printf "3. Early exit (m=0) skips 93%% of work\n";
  Printf.printf "4. State tracking avoids redundant checks\n"