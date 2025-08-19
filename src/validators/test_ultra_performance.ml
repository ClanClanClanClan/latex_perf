(* TEST ULTRA-OPTIMIZED VALIDATORS *)

open Printf

let generate_tokens n =
  Array.init n (fun i ->
    let tok = match i mod 10 with
      | 0 -> Validator_core_fixed.TChar (Uchar.of_int 34, Other)  (* Quote *)
      | 1 | 2 -> Validator_core_fixed.TChar (Uchar.of_int 45, Other)  (* Hyphen *)
      | 3 -> Validator_core_fixed.TChar (Uchar.of_int 32, Space)
      | _ -> Validator_core_fixed.TChar (Uchar.of_int 97, Letter)
    in {
      Validator_core_fixed.token = tok;
      location = { line = i / 100; column = i mod 100; offset = i }
    })

let () =
  printf "ULTRA-OPTIMIZED VALIDATOR PERFORMANCE TEST\n";
  printf "==========================================\n\n";
  
  (* Test with realistic sizes *)
  let sizes = [10_000; 50_000; 100_000; 276_000] in
  
  List.iter (fun size ->
    printf "Testing with %d tokens:\n" size;
    let tokens = generate_tokens size in
    Single_pass_ultra.bench_ultra tokens;
    printf "\n"
  ) sizes;
  
  printf "Target: Validators should add <1ms to the 10ms pipeline\n";
  printf "Total pipeline with validators should be <11ms P99\n"