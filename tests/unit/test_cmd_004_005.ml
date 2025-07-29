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

let () =
  Printf.printf "Testing CMD-004 and CMD-005 validators:\n\n";
  
  (* Test CMD-004: CamelCase command names *)
  let test_camelcase cmd_name expected =
    let doc = { 
      tokens = []; 
      expanded_tokens = Some [TCommand (s2c cmd_name)];
      ast = None; semantics = None;
      filename = s2c "test.tex"; doc_layer = L1_Expanded;
    } in
    let issues = run_all_validators doc in
    let found = List.exists (fun i -> c2s i.rule_id = "CMD-004") issues in
    Printf.printf "CMD-004 (\\%s): %s %s\n" 
      cmd_name 
      (if found then "DETECTED" else "NOT DETECTED")
      (if found = expected then "✓" else "✗")
  in
  
  test_camelcase "TestCommand" true;
  test_camelcase "MyMacro" true;
  test_camelcase "NewSection" true;
  test_camelcase "lowercase" false;
  test_camelcase "section" false;
  
  Printf.printf "\n";
  
  (* Test CMD-005: Single-letter macro *)
  let test_single_letter macro_def expected =
    let doc = { 
      tokens = []; 
      expanded_tokens = Some macro_def;
      ast = None; semantics = None;
      filename = s2c "test.tex"; doc_layer = L1_Expanded;
    } in
    let issues = run_all_validators doc in
    let found = List.exists (fun i -> c2s i.rule_id = "CMD-005") issues in
    Printf.printf "CMD-005: %s %s\n" 
      (if found then "DETECTED" else "NOT DETECTED")
      (if found = expected then "✓" else "✗")
  in
  
  (* Test single-letter macro detection *)
  test_single_letter [TCommand (s2c "newcommand"); TBeginGroup; TCommand (s2c "x"); TEndGroup] true;
  test_single_letter [TCommand (s2c "def"); TBeginGroup; TCommand (s2c "a"); TEndGroup] true;
  test_single_letter [TCommand (s2c "newcommand"); TBeginGroup; TCommand (s2c "foo"); TEndGroup] false;
  test_single_letter [TCommand (s2c "def"); TBeginGroup; TCommand (s2c "myname"); TEndGroup] false;
  
  Printf.printf "\nTotal validators: 50/80 = 62.5%% compliance\n"