(* Test additional validators beyond the basic 13 *)

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

let test_math_015 () =
  let doc = {
    tokens = [];
    expanded_tokens = Some [
      TCommand (s2c "stackrel");
      TBeginGroup;
      TText (s2c "above");
      TEndGroup;
      TBeginGroup;
      TText (s2c "below");
      TEndGroup;
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues = run_all_validators doc in
  let found = List.exists (fun i -> c2s i.rule_id = "MATH-015") issues in
  Printf.printf "MATH-015 (stackrel): %s\n" (if found then "✅ WORKS" else "❌ Missing")

let test_math_016 () =
  let doc = {
    tokens = [];
    expanded_tokens = Some [
      TText (s2c "x");
      TText (s2c "_");
      TText (s2c "i");
      TText (s2c "_");
      TText (s2c "j");
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues = run_all_validators doc in
  let found = List.exists (fun i -> c2s i.rule_id = "MATH-016") issues in
  Printf.printf "MATH-016 (nested subscripts): %s\n" (if found then "✅ WORKS" else "❌ Missing")

let test_math_018 () =
  let doc = {
    tokens = [];
    expanded_tokens = Some [
      TText (s2c "3.14");
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues = run_all_validators doc in
  let found = List.exists (fun i -> c2s i.rule_id = "MATH-018") issues in
  Printf.printf "MATH-018 (pi as 3.14): %s\n" (if found then "✅ WORKS" else "❌ Missing")

let () =
  Printf.printf "🧪 Testing Additional Validators\n";
  Printf.printf "================================\n\n";
  test_math_015 ();
  test_math_016 ();
  test_math_018 ();
  Printf.printf "\nTesting complete!\n"