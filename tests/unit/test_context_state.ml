(* Test context state building *)

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

let test_context () =
  Printf.printf "🔍 Testing context state building\n";
  Printf.printf "==================================\n\n";
  
  (* Test 1: DELIM-006 detects \big outside math (should work) *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "big"); TText (s2c "(")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let delim_006_found = List.exists (fun i -> c2s i.rule_id = "DELIM-006") issues1 in
  Printf.printf "  DELIM-006 (\\big outside math): %s\n" (if delim_006_found then "✅ WORKS" else "❌ BROKEN");
  
  (* Test 2: DELIM-006 should NOT detect \big inside math *)
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TMathShift; TCommand (s2c "big"); TText (s2c "("); TMathShift];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let delim_006_found2 = List.exists (fun i -> c2s i.rule_id = "DELIM-006") issues2 in
  Printf.printf "  DELIM-006 ($\\big($): %s\n" (if delim_006_found2 then "❌ FALSE POSITIVE" else "✅ CORRECT");
  
  (* Test 3: DELIM-010 should detect \big inside math *)
  let delim_010_found2 = List.exists (fun i -> c2s i.rule_id = "DELIM-010") issues2 in
  Printf.printf "  DELIM-010 ($\\big($): %s\n" (if delim_010_found2 then "✅ WORKS" else "❌ BROKEN");
  
  (* Test 4: Different math token order *)
  let doc3 = {
    tokens = []; 
    expanded_tokens = Some [TMathShift; TText (s2c "x"); TCommand (s2c "big"); TText (s2c "("); TText (s2c "y"); TMathShift];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues3 = run_all_validators doc3 in
  let delim_010_found3 = List.exists (fun i -> c2s i.rule_id = "DELIM-010") issues3 in
  Printf.printf "  DELIM-010 ($x\\big(y$): %s\n" (if delim_010_found3 then "✅ WORKS" else "❌ BROKEN");
  
  Printf.printf "\n🎯 Context state test complete!\n"

let () = test_context ()