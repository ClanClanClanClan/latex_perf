#use "extracted_types.ml";;
#use "extracted_validators.ml";;
#use "validator_runner.ml";;

(* Test if validators are defined *)
let test_validator name f =
  try 
    let _ = f { 
      tokens = []; expanded_tokens = Some [];
      ast = None; semantics = None;
      filename = []; doc_layer = L1_Expanded;
    } in
    Printf.printf "%s: ✓ defined\n" name
  with _ ->
    Printf.printf "%s: ✗ not found\n" name

let () =
  Printf.printf "=== VALIDATOR AVAILABILITY CHECK ===\n\n";
  
  (* DELIM validators *)
  Printf.printf "DELIM validators:\n";
  test_validator "delim_001" delim_001_validator_real;
  test_validator "delim_002" delim_002_validator_real;
  test_validator "delim_003" delim_003_validator_real;
  test_validator "delim_004" delim_004_validator_real;
  test_validator "delim_005" delim_005_validator_real;
  test_validator "delim_006" delim_006_validator_real;
  test_validator "delim_007" delim_007_validator_real;
  test_validator "delim_008" delim_008_validator_real;
  test_validator "delim_009" delim_009_validator_real;
  test_validator "delim_010" delim_010_validator_real;
  
  Printf.printf "\nMATH validators:\n";
  test_validator "math_002" math_002_validator_real;
  test_validator "math_003" math_003_validator_real;
  test_validator "math_004" math_004_validator_real;
  test_validator "math_005" math_005_validator_real;
  test_validator "math_006" math_006_validator_real;
  test_validator "math_007" math_007_validator_real;
  test_validator "math_009" math_009_validator_real;
  test_validator "math_010" math_010_validator_real;
  test_validator "math_012" math_012_validator_real;
  test_validator "math_013" math_013_validator_real;
  test_validator "math_015" math_015_validator_real;
  test_validator "math_016" math_016_validator_real;
  test_validator "math_018" math_018_validator_real;
  test_validator "math_020" math_020_validator_real;
  
  Printf.printf "\nREF validators:\n";
  test_validator "ref_001" ref_001_validator_real;
  test_validator "ref_002" ref_002_validator_real;
  test_validator "ref_003" ref_003_validator_real;
  test_validator "ref_004" ref_004_validator_real;
  test_validator "ref_005" ref_005_validator_real;
  test_validator "ref_006" ref_006_validator_real;
  
  Printf.printf "\nSCRIPT validators:\n";
  test_validator "script_001" script_001_validator_real;
  test_validator "script_002" script_002_validator_real;
  
  Printf.printf "\nCMD validators:\n";
  test_validator "cmd_001" cmd_001_validator_real;
  test_validator "cmd_002" cmd_002_validator_real;
  test_validator "cmd_003" cmd_003_validator_real;
  test_validator "cmd_004" cmd_004_validator_real;
  test_validator "cmd_005" cmd_005_validator_real;
  
  Printf.printf "\n=== CHECKING run_all_validators ===\n";
  let doc = { 
    tokens = []; expanded_tokens = Some [];
    ast = None; semantics = None;
    filename = []; doc_layer = L1_Expanded;
  } in
  let issues = run_all_validators doc in
  Printf.printf "run_all_validators returned %d issues for empty doc\n" (List.length issues)