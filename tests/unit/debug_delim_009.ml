(* Debug DELIM-009 validator - check token structure *)

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

let debug_delim_009 () =
  Printf.printf "🔍 Debugging DELIM-009 validator\n";
  Printf.printf "=================================\n\n";
  
  (* Check if DELIM-009 exists in extraction *)
  let simple_doc = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "test")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let all_issues = run_all_validators simple_doc in
  Printf.printf "  Total validator issues on simple doc: %d\n" (List.length all_issues);
  
  (* Test specific structure that should trigger DELIM-009 *)
  let nested_doc = {
    tokens = []; 
    expanded_tokens = Some [TBeginGroup; TText (s2c "("); TText (s2c "x"); TText (s2c ")"); TEndGroup];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let nested_issues = run_all_validators nested_doc in
  Printf.printf "  Issues on nested doc: %d\n" (List.length nested_issues);
  
  (* Check if any DELIM validators are working at all *)
  let delim_test_doc = {
    tokens = []; 
    expanded_tokens = Some [TBeginGroup; TText (s2c "test")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let delim_issues = run_all_validators delim_test_doc in
  let delim_001_found = List.exists (fun i -> c2s i.rule_id = "DELIM-001") delim_issues in
  Printf.printf "  DELIM-001 detection (unmatched {): %s\n" (if delim_001_found then "✅ WORKING" else "❌ NOT WORKING");
  
  (* List all validators that triggered on nested structure *)
  Printf.printf "\n  All validators triggered on nested structure:\n";
  List.iter (fun issue -> 
    Printf.printf "    - %s: %s\n" (c2s issue.rule_id) (c2s issue.message)
  ) nested_issues;
  
  Printf.printf "\n🎯 Debug complete!\n"

let () = debug_delim_009 ()