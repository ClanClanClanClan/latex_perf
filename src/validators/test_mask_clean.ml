(* TEST CLEAN MASK VALIDATORS *)

let () =
  Printf.printf "MASK-ONLY VALIDATOR TEST (Expert Approach)\n";
  Printf.printf "==========================================\n\n";
  
  Printf.printf "Key optimization: Read ONLY 8-bit mask (0.276MB), not 32-bit arrays (2.2MB)\n\n";
  
  (* Test with different sizes *)
  let _ = Mask_validators_clean.bench 50_000 in
  Printf.printf "\n";
  let p99_276k = Mask_validators_clean.bench 276_000 in
  
  Printf.printf "\n==== COMPARISON ====\n";
  Printf.printf "Previous approaches for 276K tokens:\n";
  Printf.printf "  Original:    7.590ms (2.2MB memory traffic)\n";
  Printf.printf "  Sparse:      3.189ms (~1.1MB memory traffic)\n"; 
  Printf.printf "  Mask-only:   %.3fms (0.276MB memory traffic)\n" p99_276k;
  
  if p99_276k < 1.0 then begin
    Printf.printf "\n🎉 SUCCESS: Expert was RIGHT! <1ms achieved!\n";
    Printf.printf "The key was:\n";
    Printf.printf "  1. Fuse mask writing into L0 (no 7.4ms build pass)\n";
    Printf.printf "  2. Read ONLY 8-bit mask (8x less memory)\n";
    Printf.printf "  3. Run-skipping for sequences\n"
  end else begin
    Printf.printf "\n⚠️ Still %.3fms - investigate further\n" p99_276k
  end