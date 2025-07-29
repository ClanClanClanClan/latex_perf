(* Test MATH-013 validator - differential d notation *)

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

let test_math_013 () =
  Printf.printf "🧪 Testing MATH-013 (differential d notation)\n";
  Printf.printf "==========================================\n\n";
  
  (* Test case 1: differential d followed by variable (should trigger) *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "d"); TText (s2c "x")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let found1 = List.exists (fun i -> c2s i.rule_id = "MATH-013") issues1 in
  Printf.printf "  d followed by variable: %s\n" (if found1 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 2: differential d in integration *)
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "∫"); TText (s2c "f"); TText (s2c "d"); TText (s2c "t")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let found2 = List.exists (fun i -> c2s i.rule_id = "MATH-013") issues2 in
  Printf.printf "  integral d notation: %s\n" (if found2 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 3: regular letter d (should not trigger) *)
  let doc3 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "distance"); TText (s2c "d")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues3 = run_all_validators doc3 in
  let found3 = List.exists (fun i -> c2s i.rule_id = "MATH-013") issues3 in
  Printf.printf "  regular letter d: %s\n" (if found3 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  Printf.printf "\n🎯 MATH-013 validator test complete!\n"

let () = test_math_013 ()