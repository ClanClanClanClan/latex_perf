(* Test POST-028 validator - verbatim environment validation *)

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

let test_post_028 () =
  Printf.printf "🧪 Testing POST-028 (verbatim environment validation)\n";
  Printf.printf "====================================================\n\n";
  
  (* Test case 1: Unbalanced environment - missing end (should trigger error) *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "begin"); TText (s2c "content")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let found1 = List.exists (fun i -> c2s i.rule_id = "POST-028") issues1 in
  Printf.printf "  \\begin without \\end: %s\n" (if found1 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 2: Balanced environment (should not trigger) *)
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "begin"); TText (s2c "content"); TCommand (s2c "end")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let found2 = List.exists (fun i -> c2s i.rule_id = "POST-028") issues2 in
  Printf.printf "  \\begin...\\end balanced: %s\n" (if found2 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  (* Test case 3: Extra end (should trigger) *)
  let doc3 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "content"); TCommand (s2c "end")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues3 = run_all_validators doc3 in
  let found3 = List.exists (fun i -> c2s i.rule_id = "POST-028") issues3 in
  Printf.printf "  \\end without \\begin: %s\n" (if found3 then "✅ DETECTED" else "❌ MISSED");
  
  Printf.printf "\n🎯 POST-028 validator test complete!\n"

let () = test_post_028 ()