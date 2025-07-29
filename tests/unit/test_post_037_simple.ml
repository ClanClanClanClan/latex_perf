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
  Printf.printf "Testing POST-037:\n";
  
  let doc = { 
    tokens = []; 
    expanded_tokens = Some [TText (s2c "$$x^2$$")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues = run_all_validators doc in
  let found = List.exists (fun i -> c2s i.rule_id = "POST-037") issues in
  Printf.printf "POST-037: %s\n" (if found then "DETECTED" else "MISSED");
  
  List.iter (fun issue -> 
    Printf.printf "  %s: %s\n" (c2s issue.rule_id) (c2s issue.message)
  ) issues