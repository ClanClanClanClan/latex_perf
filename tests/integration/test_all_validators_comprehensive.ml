(* Comprehensive test of ALL extracted validators *)

#use "extracted_types.ml";;
#use "extracted_validators.ml";;
#use "validator_runner.ml";;

(* Helpers *)
let s2c s = 
  let rec explode i acc =
    if i < 0 then acc else explode (i - 1) (s.[i] :: acc)
  in explode (String.length s - 1) []

let c2s chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

(* Test helper function *)
let test_doc name doc expected_rule =
  let issues = run_all_validators doc in
  let found = List.exists (fun i -> c2s i.rule_id = expected_rule) issues in
  Printf.printf "  %s %s: %s\n"
    (if found then "✅" else "❌")
    expected_rule
    (if found then "Detected" else "MISSED!")

(* Test each validator group *)
let test_delimiter_validators () =
  Printf.printf "\n🔍 Testing DELIMITER validators...\n";
  
  (* DELIM-001: Unmatched delimiters *)
  let doc1 = {
    tokens = [];
    expanded_tokens = Some [
      TBeginGroup;
      TText (s2c "test");
      (* Missing TEndGroup *)
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* DELIM-002: Extra closing *)
  let doc2 = {
    tokens = [];
    expanded_tokens = Some [
      TText (s2c "test");
      TEndGroup; (* Extra closing *)
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* DELIM-003: Unmatched \left-\right *)
  let doc3 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "left");
      TText (s2c "(");
      (* Missing \right *)
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* DELIM-004: \right without \left *)
  let doc4 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "right");
      TText (s2c ")");
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* DELIM-007: Unmatched angle brackets *)
  let doc7 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "langle");
      TText (s2c "x");
      (* Missing \rangle *)
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* DELIM-008: Empty \left\right *)
  let doc8 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "left");
      TCommand (s2c "right");
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  test_doc "Unmatched {" doc1 "DELIM-001";
  test_doc "Extra }" doc2 "DELIM-002";
  test_doc "Unmatched \\left" doc3 "DELIM-003";
  test_doc "\\right without \\left" doc4 "DELIM-004";
  test_doc "Unmatched \\langle" doc7 "DELIM-007";
  test_doc "Empty \\left\\right" doc8 "DELIM-008";;

let test_math_validators () =
  Printf.printf "\n🔢 Testing MATH validators...\n";
  
  (* MATH-009: Misplaced math command *)
  let doc9 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "frac");
      TBeginGroup;
      TText (s2c "1");
      TEndGroup;
      TBeginGroup;
      TText (s2c "2");
      TEndGroup;
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* MATH-010: · instead of \cdot *)
  let doc10 = {
    tokens = [];
    expanded_tokens = Some [
      TMathShift;
      TText (s2c "x");
      TText (s2c "·"); (* Unicode middle dot *)
      TText (s2c "y");
      TMathShift;
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  test_doc "Misplaced \\frac" doc9 "MATH-009";
  test_doc "· instead of \\cdot" doc10 "MATH-010";;

let test_ref_validators () =
  Printf.printf "\n📎 Testing REF validators...\n";
  
  (* REF-001: Undefined reference *)
  let doc_ref1 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "ref");
      TBeginGroup;
      TText (s2c "undefined_label");
      TEndGroup;
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* REF-002: Duplicate label *)
  let doc_ref2 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "label");
      TBeginGroup;
      TText (s2c "mylabel");
      TEndGroup;
      TCommand (s2c "label");
      TBeginGroup;
      TText (s2c "mylabel"); (* Duplicate *)
      TEndGroup;
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  (* REF-003: Invalid label format *)
  let doc_ref3 = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "label");
      TBeginGroup;
      TText (s2c "my label with spaces"); (* Invalid *)
      TEndGroup;
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  test_doc "Undefined ref" doc_ref1 "REF-001";
  test_doc "Duplicate label" doc_ref2 "REF-002";
  test_doc "Invalid label format" doc_ref3 "REF-003";;

let test_script_validators () =
  Printf.printf "\n📐 Testing SCRIPT validators...\n";
  
  (* SCRIPT-001: Multi-letter in subscript *)
  let doc_script = {
    tokens = [];
    expanded_tokens = Some [
      TText (s2c "x");
      TSubscript;
      TText (s2c "max"); (* Multi-letter without braces *)
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  test_doc "Multi-letter subscript" doc_script "SCRIPT-001";;

let test_cmd_validators () =
  Printf.printf "\n⚡ Testing CMD validators...\n";
  
  (* CMD-001: Obsolete command *)
  let doc_cmd = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "bf"); (* Obsolete - should use \textbf *)
      TText (s2c "bold text");
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  test_doc "Obsolete \\bf" doc_cmd "CMD-001";;

(* Main test runner *)
let () =
  Printf.printf "🚀 COMPREHENSIVE VALIDATOR TEST SUITE\n";
  Printf.printf "=====================================\n";
  
  test_delimiter_validators ();
  test_math_validators ();
  test_ref_validators ();
  test_script_validators ();
  test_cmd_validators ();
  
  Printf.printf "\n✨ All validators tested!\n"