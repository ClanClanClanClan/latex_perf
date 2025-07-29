(* Test POST validators - simplified *)

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
  Printf.printf "Testing POST validators:\n\n";
  
  (* POST-029: lstlisting command *)
  let doc29 = { 
    tokens = []; 
    expanded_tokens = Some [TCommand (s2c "lstlisting")];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  let issues29 = run_all_validators doc29 in
  let found29 = List.exists (fun i -> c2s i.rule_id = "POST-029") issues29 in
  Printf.printf "POST-029 (lstlisting): %s\n" (if found29 then "DETECTED" else "MISSED");
  
  (* Check what the validator is actually producing *)
  List.iter (fun issue -> 
    Printf.printf "  Found: %s - %s\n" (c2s issue.rule_id) (c2s issue.message)
  ) issues29;
  
  Printf.printf "\nDone.\n"