(* TEST MASK-ONLY VALIDATORS - Verify <1ms Performance *)

open Printf

let test_sizes = [50_000; 276_000]

let () =
  printf "MASK-ONLY VALIDATOR TEST\n";
  printf "========================\n\n";
  printf "Following expert advice: Read ONLY 8-bit mask, not 32-bit arrays\n\n";
  
  List.iter (fun n ->
    printf "Testing with %d tokens:\n" n;
    printf "%s\n" (String.make 60 '-');
    
    (* Create test interest mask *)
    let interest = Mask_only_validators.create_test_interest_mask n in
    
    (* Show memory savings *)
    let old_memory = float (n * 4 * 2) /. 1_000_000.0 in  (* kinds + codes *)
    let new_memory = float n /. 1_000_000.0 in             (* just mask *)
    printf "Memory traffic:\n";
    printf "  Old approach (kinds+codes): %.3fMB\n" old_memory;
    printf "  New approach (mask only):   %.3fMB\n" new_memory;
    printf "  Reduction:                  %.1fx\n\n" (old_memory /. new_memory);
    
    (* Run benchmark *)
    let p99 = Mask_only_validators.bench_mask_only interest n in
    
    (* Extrapolate to 276K if needed *)
    if n < 276_000 then begin
      let scale = 276_000.0 /. float n in
      printf "\nEstimated for 276K tokens: %.3fms\n" (p99 *. scale)
    end;
    
    printf "\n"
  ) test_sizes;
  
  printf "\n🎯 COMPARISON WITH PREVIOUS APPROACHES:\n";
  printf "┌─────────────────────────┬──────────┬──────────────┐\n";
  printf "│ Approach                │ P99 Time │ Memory Read  │\n";
  printf "├─────────────────────────┼──────────┼──────────────┤\n";
  printf "│ Original (baseline)     │  7.590ms │ 2.2MB        │\n";
  printf "│ Sparse candidates       │  3.189ms │ 1.1MB (est)  │\n";
  printf "│ Mask-only (this)       │  ?.???ms │ 0.276MB      │\n";
  printf "└─────────────────────────┴──────────┴──────────────┘\n\n";
  
  printf "KEY OPTIMIZATIONS:\n";
  printf "1. Fused interest mask writing into L0 (eliminates 7.4ms build pass)\n";
  printf "2. Read ONLY 8-bit mask (8x less memory traffic)\n";
  printf "3. Run-skipping for hyphens/periods (skip already-seen bytes)\n";
  printf "4. Zero allocations in hot loops\n";
  printf "5. Branch-minimal design\n\n";
  
  printf "If this achieves <1ms, the expert was RIGHT!\n"