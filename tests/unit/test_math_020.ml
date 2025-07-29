(* Test MATH-020 validator - scalar-vector multiplication *)

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

let test_math_020 () =
  Printf.printf "🧪 Testing MATH-020 (scalar-vector multiplication)\n";
  Printf.printf "==============================================\n\n";
  
  (* Test case 1: scalar followed by mathbf vector (should suggest \\cdot) *)
  let doc1 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "5"); TCommand (s2c "mathbf"); TBeginGroup; TText (s2c "v"); TEndGroup];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues1 = run_all_validators doc1 in
  let found1 = List.exists (fun i -> c2s i.rule_id = "MATH-020") issues1 in
  Printf.printf "  scalar * vector: %s\n" (if found1 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 2: number followed by mathbf *)
  let doc2 = {
    tokens = []; 
    expanded_tokens = Some [TText (s2c "3"); TCommand (s2c "mathbf")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues2 = run_all_validators doc2 in
  let found2 = List.exists (fun i -> c2s i.rule_id = "MATH-020") issues2 in
  Printf.printf "  number mathbf: %s\n" (if found2 then "✅ DETECTED" else "❌ MISSED");
  
  (* Test case 3: just mathbf alone (should not trigger) *)
  let doc3 = {
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "mathbf"); TBeginGroup; TText (s2c "x"); TEndGroup];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues3 = run_all_validators doc3 in
  let found3 = List.exists (fun i -> c2s i.rule_id = "MATH-020") issues3 in
  Printf.printf "  mathbf alone: %s\n" (if found3 then "❌ FALSE POSITIVE" else "✅ CORRECTLY IGNORED");
  
  Printf.printf "\n🎯 MATH-020 validator test complete!\n"

let () = test_math_020 ()