(* Test DELIM-009 validator - nested delimiters validation *)

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

let test_delim_009 () =
  Printf.printf "🧪 Testing DELIM-009 (nested delimiters validation)\n";
  Printf.printf "====================================================\n\n";
  
  (* Test case 1: nested parentheses inside braces (should trigger warning) *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TBeginGroup; TText (s2c "("); TText (s2c "x"); TText (s2c ")"); TEndGroup];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let found1 = List.exists (fun i -> c2s i.rule_id = "DELIM-009") issues1 in
  Printf.printf "  {(x)} nested delimiters: %s\n" (if found1 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 2: regular parentheses (should not trigger) *)
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "("); TText (s2c "x"); TText (s2c ")")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let found2 = List.exists (fun i -> c2s i.rule_id = "DELIM-009") issues2 in
  Printf.printf "  (x) regular parens: %s\n" (if found2 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  (* Test case 3: braces without nested parens (should not trigger) *)
  let doc3 = {
    tokens = []; 
    expanded_tokens = Some [TBeginGroup; TText (s2c "x"); TEndGroup];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues3 = run_all_validators doc3 in
  let found3 = List.exists (fun i -> c2s i.rule_id = "DELIM-009") issues3 in
  Printf.printf "  {x} braces only: %s\n" (if found3 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  Printf.printf "\n🎯 DELIM-009 validator test complete!\n"

let () = test_delim_009 ()