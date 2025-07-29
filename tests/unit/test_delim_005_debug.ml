(* Debug DELIM-005 validator - mismatched parenthesis sizes *)

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

let test_delim_005 () =
  Printf.printf "🔍 Debugging DELIM-005 (mismatched parenthesis sizes)\n";
  Printf.printf "===================================================\n\n";
  
  (* Test if DELIM-005 validator exists and returns anything *)
  let simple_doc = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "test")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let all_issues = run_all_validators simple_doc in
  let delim_005_issues = List.filter (fun i -> c2s i.rule_id = "DELIM-005") all_issues in
  Printf.printf "  Simple test - DELIM-005 issues found: %d\n" (List.length delim_005_issues);
  
  (* Test different size command patterns *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "big"); TText (s2c "("); TText (s2c "x"); TCommand (s2c "Big"); TText (s2c ")")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let found1 = List.exists (fun i -> c2s i.rule_id = "DELIM-005") issues1 in
  Printf.printf "  \\big( x \\Big): %s\n" (if found1 then "✅ DETECTED" else "❌ MISSED");
  
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "Big"); TText (s2c "("); TText (s2c "x"); TCommand (s2c "big"); TText (s2c ")")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let found2 = List.exists (fun i -> c2s i.rule_id = "DELIM-005") issues2 in
  Printf.printf "  \\Big( x \\big): %s\n" (if found2 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test if any other validators are triggered *)
  Printf.printf "\n  All validators triggered on test case:\n";
  List.iter (fun issue -> 
    Printf.printf "    - %s\n" (c2s issue.rule_id)
  ) issues1;
  
  Printf.printf "\n🎯 DELIM-005 debug complete!\n"

let () = test_delim_005 ()