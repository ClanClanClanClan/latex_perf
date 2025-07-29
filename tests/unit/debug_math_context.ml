(* Debug math context detection *)

#use "extracted_types.ml";;
#use "extracted_validators.ml";;
#use "validator_runner.ml";;

let s2c s = 
  let rec explode i acc =
    if i < 0 then acc else explode (i - 1) (s.[i] :: acc)
  in explode (String.length s - 1) []

let c2s chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let debug_math () =
  Printf.printf "🔍 Debugging math context detection\n";
  Printf.printf "====================================\n\n";
  
  (* Test if any validators detect math context properly *)
  let math_doc = {
    tokens = []; 
    expanded_tokens = Some [TMathShift; TCommand (s2c "frac"); TMathShift];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let math_issues = run_all_validators math_doc in
  Printf.printf "  Issues in $\\frac$: %d\n" (List.length math_issues);
  List.iter (fun issue -> 
    Printf.printf "    - %s: %s\n" (c2s issue.rule_id) (c2s issue.message)
  ) math_issues;
  
  (* Test MATH-009 which should detect \frac outside math *)
  let non_math_doc = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "frac")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let non_math_issues = run_all_validators non_math_doc in
  let math_009_found = List.exists (fun i -> c2s i.rule_id = "MATH-009") non_math_issues in
  Printf.printf "  MATH-009 (\\frac outside math): %s\n" (if math_009_found then "✅ WORKING" else "❌ NOT WORKING");
  
  Printf.printf "\n🎯 Math context debug complete!\n"

let () = debug_math ()