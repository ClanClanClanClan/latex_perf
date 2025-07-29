(* Test POST-037 validator - obsolete $$ display math *)

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
  Printf.printf "Testing POST-037 (obsolete $$ display math):\n\n";
  
  (* POST-037: $$ display math *)
  let doc37 = { 
    tokens = []; 
    expanded_tokens = Some [TText (s2c "$$x^2$$")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues37 = run_all_validators doc37 in
  let found37 = List.exists (fun i -> c2s i.rule_id = "POST-037") issues37 in
  Printf.printf "POST-037 ($$x^2$$): %s\n" (if found37 then "DETECTED" else "MISSED");
  
  (* List all issues found */
  List.iter (fun issue -> 
    Printf.printf "  Found: %s - %s\n" (c2s issue.rule_id) (c2s issue.message)
  ) issues37;
  
  Printf.printf "\nDone.\n"