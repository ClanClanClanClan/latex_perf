(* Test real extracted validators *)

(* Include type definitions first *)
#use "extracted_types.ml";;

(* Include extracted validator code *)
#use "extracted_validators.ml";;
#use "validator_runner.ml";;

(* Helper to convert OCaml strings to char lists for testing *)
let string_to_chars s =
  let rec explode i acc =
    if i < 0 then acc
    else explode (i - 1) (s.[i] :: acc)
  in
  explode (String.length s - 1) []

(* Helper to convert char lists back to strings for display *)
let chars_to_string chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

(* Test function *)
let test_validators () =
  Printf.printf "🧪 Testing REAL extracted validators...\n\n";
  
  (* Create test document with problematic LaTeX *)
  let test_doc = {
    tokens = [
      TCommand (string_to_chars "left");
      TText (string_to_chars "(");
      TText (string_to_chars "x");
      TCommand (string_to_chars "right");
      TText (string_to_chars ")");
      TCommand (string_to_chars "left");  (* Unmatched left *)
      TText (string_to_chars "[");
      TCommand (string_to_chars "cdot");  (* Middle dot instead of \cdot *)
      TCommand (string_to_chars "ref");
      TBeginGroup;
      TText (string_to_chars "undefined_label");
      TEndGroup;
    ];
    expanded_tokens = Some [
      TCommand (string_to_chars "left");
      TText (string_to_chars "(");
      TText (string_to_chars "x");
      TCommand (string_to_chars "right");
      TText (string_to_chars ")");
      TCommand (string_to_chars "left");  (* Unmatched left *)
      TText (string_to_chars "[");
      TCommand (string_to_chars "cdot");
      TCommand (string_to_chars "ref");
      TBeginGroup;
      TText (string_to_chars "undefined_label");
      TEndGroup;
    ];
    ast = None;
    semantics = None;
    filename = string_to_chars "test.tex";
    doc_layer = L1_Expanded;
  } in
  
  (* Run all validators *)
  let issues = run_all_validators test_doc in
  
  (* Display results *)
  Printf.printf "Found %d validation issues:\n\n" (List.length issues);
  List.iter (fun issue ->
    let severity_str = match issue.issue_severity with
      | Error -> "❌ ERROR"
      | Warning -> "⚠️  WARN"
      | Info -> "ℹ️  INFO"
    in
    Printf.printf "[%s] %s: %s\n" 
      (chars_to_string issue.rule_id)
      severity_str
      (chars_to_string issue.message);
    match issue.suggested_fix with
    | Some fix -> Printf.printf "   💡 Fix: %s\n" (chars_to_string fix)
    | None -> ()
  ) issues;
  
  Printf.printf "\n✅ Validators successfully extracted and running!\n"

(* Run the test *)
let () = test_validators ()