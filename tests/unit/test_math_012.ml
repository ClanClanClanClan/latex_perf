(* Test MATH-012 validator - multi-letter functions *) 

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

let test_math_012 () =
  Printf.printf "🧪 Testing MATH-012 (multi-letter functions)\n";
  Printf.printf "==========================================\n\n";
  
  (* Test case 1: sin function without operatorname *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "sin")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let found1 = List.exists (fun i -> c2s i.rule_id = "MATH-012") issues1 in
  Printf.printf "  sin function: %s\n" (if found1 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 2: cos function *)
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "cos")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let found2 = List.exists (fun i -> c2s i.rule_id = "MATH-012") issues2 in
  Printf.printf "  cos function: %s\n" (if found2 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 3: regular single letter (should not trigger) *)
  let doc3 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "x")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues3 = run_all_validators doc3 in
  let found3 = List.exists (fun i -> c2s i.rule_id = "MATH-012") issues3 in
  Printf.printf "  single letter: %s\n" (if found3 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  (* Test case 4: log function *)
  let doc4 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "log")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues4 = run_all_validators doc4 in
  let found4 = List.exists (fun i -> c2s i.rule_id = "MATH-012") issues4 in
  Printf.printf "  log function: %s\n" (if found4 then "✅ DETECTED" else "❌ MISSED");
  
  Printf.printf "\n🎯 MATH-012 validator test complete!\n"

let () = test_math_012 ()