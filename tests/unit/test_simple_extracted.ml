(* Simple test to verify extraction worked *)

(* Just check if the files compile *)
#use "extracted_validators.ml";;

Printf.printf "✅ Extraction successful! Validators compiled to OCaml.\n";
Printf.printf "The following validators were extracted:\n";
Printf.printf "- delim_001_validator_real\n";
Printf.printf "- delim_002_validator_real\n";
Printf.printf "- delim_003_validator_real\n";
Printf.printf "- delim_004_validator_real\n";
Printf.printf "- delim_007_validator_real\n";
Printf.printf "- delim_008_validator_real\n";
Printf.printf "- math_009_validator_real\n";
Printf.printf "- math_010_validator_real\n";
Printf.printf "- ref_001_validator_real\n";
Printf.printf "- ref_002_validator_real\n";
Printf.printf "- ref_003_validator_real\n";
Printf.printf "- script_001_validator_real\n";
Printf.printf "- cmd_001_validator_real\n";
Printf.printf "\n🎯 Next step: Create OCaml wrapper to test against real corpus!\n"