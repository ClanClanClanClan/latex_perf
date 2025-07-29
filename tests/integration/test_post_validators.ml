(* Test POST validators individually *)

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

let test_post () =
  Printf.printf "🧪 Testing POST validators individually\n";
  Printf.printf "======================================\n\n";
  
  (* POST-028: Unbalanced verbatim *)
  Printf.printf "POST-028 (unbalanced verbatim):\n";
  let doc28a = { tokens = []; expanded_tokens = Some [TCommand (s2c "begin"); TText (s2c "content")]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues28a = run_all_validators doc28a in
  let found28a = List.exists (fun i -> c2s i.rule_id = "POST-028") issues28a in
  Printf.printf "  \\begin without \\end: %s\n" (if found28a then "✅ DETECTED" else "❌ MISSED");
  
  (* POST-029: Code listings without package/language *)
  Printf.printf "\nPOST-029 (code listings):\n";
  let doc29a = { tokens = []; expanded_tokens = Some [TCommand (s2c "lstlisting")]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues29a = run_all_validators doc29a in
  let found29a = List.exists (fun i -> c2s i.rule_id = "POST-029") issues29a in
  Printf.printf "  \\lstlisting command: %s\n" (if found29a then "✅ DETECTED" else "❌ MISSED");
  
  let doc29b = { tokens = []; expanded_tokens = Some [TCommand (s2c "lstinline")]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues29b = run_all_validators doc29b in
  let found29b = List.exists (fun i -> c2s i.rule_id = "POST-029") issues29b in
  Printf.printf "  \\lstinline command: %s\n" (if found29b then "✅ DETECTED" else "❌ MISSED");
  
  (* POST-030: Algorithm environment *)
  Printf.printf "\nPOST-030 (algorithm):\n";
  let doc30a = { tokens = []; expanded_tokens = Some [TCommand (s2c "begin"); TBeginGroup; TText (s2c "algorithm"); TEndGroup]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues30a = run_all_validators doc30a in
  let found30a = List.exists (fun i -> c2s i.rule_id = "POST-030") issues30a in
  Printf.printf "  \\begin{algorithm}: %s\n" (if found30a then "✅ DETECTED" else "❌ MISSED");
  
  (* Try what POST-030 is actually looking for *)
  let doc30b = { tokens = []; expanded_tokens = Some [TCommand (s2c "caption")]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues30b = run_all_validators doc30b in
  let post_issues = List.filter (fun i -> String.sub (c2s i.rule_id) 0 4 = "POST") issues30b in
  Printf.printf "  \\caption triggers: ";
  List.iter (fun i -> Printf.printf "%s " (c2s i.rule_id)) post_issues;
  Printf.printf "\n";
  
  (* POST-031: Theorem environment */
  Printf.printf "\nPOST-031 (theorem):\n";
  let doc31a = { tokens = []; expanded_tokens = Some [TCommand (s2c "begin"); TBeginGroup; TText (s2c "theorem"); TEndGroup]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues31a = run_all_validators doc31a in
  let found31a = List.exists (fun i -> c2s i.rule_id = "POST-031") issues31a in
  Printf.printf "  \\begin{theorem}: %s\n" (if found31a then "✅ DETECTED" else "❌ MISSED");
  
  (* POST-032: Proof environment *)
  Printf.printf "\nPOST-032 (proof):\n";
  let doc32a = { tokens = []; expanded_tokens = Some [TCommand (s2c "begin"); TBeginGroup; TText (s2c "proof"); TEndGroup]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues32a = run_all_validators doc32a in
  let found32a = List.exists (fun i -> c2s i.rule_id = "POST-032") issues32a in
  Printf.printf "  \\begin{proof}: %s\n" (if found32a then "✅ DETECTED" else "❌ MISSED");
  
  (* POST-033: Definition *)
  Printf.printf "\nPOST-033 (definition):\n";
  let doc33a = { tokens = []; expanded_tokens = Some [TCommand (s2c "definition")]; ast = None; semantics = None; filename = s2c "test.tex"; doc_layer = L1_Expanded; } in
  let issues33a = run_all_validators doc33a in
  let found33a = List.exists (fun i -> c2s i.rule_id = "POST-033") issues33a in
  Printf.printf "  \\definition command: %s\n" (if found33a then "✅ DETECTED" else "❌ MISSED");
  
  Printf.printf "\n🎯 POST validator test complete!\n"

let () = test_post ()