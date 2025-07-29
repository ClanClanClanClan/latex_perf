(* Test DELIM-010 validator - display math delimiter sizing *)

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

let test_delim_010 () =
  Printf.printf "🧪 Testing DELIM-010 (display math delimiter sizing)\n";
  Printf.printf "===================================================\n\n";
  
  (* Test case 1: \big in math mode (should trigger info) *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TMathShift; TCommand (s2c "big"); TText (s2c "("); TText (s2c "x"); TText (s2c ")"); TMathShift];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let found1 = List.exists (fun i -> c2s i.rule_id = "DELIM-010") issues1 in
  Printf.printf "  $\\big(x)$ in math: %s\n" (if found1 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 2: \big outside math (should not trigger) *)
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "big"); TText (s2c "("); TText (s2c "x"); TText (s2c ")")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let found2 = List.exists (fun i -> c2s i.rule_id = "DELIM-010") issues2 in
  Printf.printf "  \\big(x) outside math: %s\n" (if found2 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  (* Test case 3: regular text in math (should not trigger) *)
  let doc3 = {
    tokens = []; 
    expanded_tokens = Some [TMathShift; TText (s2c "x"); TMathShift];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues3 = run_all_validators doc3 in
  let found3 = List.exists (fun i -> c2s i.rule_id = "DELIM-010") issues3 in
  Printf.printf "  $x$ regular math: %s\n" (if found3 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  Printf.printf "\n🎯 DELIM-010 validator test complete!\n"

let () = test_delim_010 ()