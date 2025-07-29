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
  Printf.printf "=== COMPLETE 50 VALIDATOR AUDIT ===\n\n";
  
  (* Create a document with all possible issues to trigger validators *)
  let mega_doc = { 
    tokens = []; 
    expanded_tokens = Some [
      (* DELIM issues *)
      TBeginGroup; TBeginGroup; TEndGroup; (* DELIM-001: unmatched braces *)
      TEndGroup; (* DELIM-002: extra closing *)
      TBeginGroup; TBeginGroup; TBeginGroup; TBeginGroup; (* DELIM-003: too deep *)
      TMathShift; TBeginGroup; TMathShift; TEndGroup; (* DELIM-004: math mode brace *)
      TBeginGroup; TMathShift; TEndGroup; (* DELIM-005: math shift in group *)
      TCommand (s2c "begin"); TBeginGroup; TText (s2c "env"); TEndGroup; (* DELIM-006 *)
      TCommand (s2c "left"); TText (s2c "("); (* DELIM-007 *)
      TCommand (s2c "big"); TText (s2c "("); (* DELIM-008 *)
      TCommand (s2c "begin"); TBeginGroup; TEndGroup; (* DELIM-009: empty env *)
      TMathShift; TMathShift; (* DELIM-010: enter math *)
      
      (* MATH issues *)
      TMathShift; TCommand (s2c "matrix"); TMathShift; (* MATH-002 *)
      TMathShift; TCommand (s2c "choose"); TMathShift; (* MATH-003 *)
      TMathShift; TCommand (s2c "frac"); TMathShift; (* MATH-004 *)
      TMathShift; TCommand (s2c "sqrt"); TBeginGroup; TEndGroup; TMathShift; (* MATH-005 *)
      TMathShift; TCommand (s2c "text"); TMathShift; (* MATH-006 *)
      TMathShift; TCommand (s2c "mathbb"); TBeginGroup; TText (s2c "1"); TEndGroup; TMathShift; (* MATH-007 *)
      TMathShift; TCommand (s2c "limits"); TMathShift; (* MATH-009 *)
      TMathShift; TCommand (s2c "dots"); TMathShift; (* MATH-010 *)
      TMathShift; TText (s2c "sin"); TMathShift; (* MATH-012 *)
      TMathShift; TCommand (s2c "ln"); TText (s2c "x"); TMathShift; (* MATH-013 *)
      TMathShift; TCommand (s2c "left"); TMathShift; (* MATH-015 *)
      TMathShift; TCommand (s2c "eqref"); TMathShift; (* MATH-016 *)
      TMathShift; TCommand (s2c "tag"); TMathShift; (* MATH-018 *)
      TMathShift; TCommand (s2c "mathit"); TMathShift; (* MATH-020 *)
      
      (* REF issues *)
      TCommand (s2c "ref"); TBeginGroup; TEndGroup; (* REF-001 *)
      TCommand (s2c "label"); TBeginGroup; TText (s2c "eq:1"); TEndGroup; (* REF-002 *)
      TCommand (s2c "cite"); TBeginGroup; TEndGroup; (* REF-003 *)
      TCommand (s2c "label"); TBeginGroup; TText (s2c "bad name"); TEndGroup; (* REF-004 *)
      TCommand (s2c "ref"); TBeginGroup; TText (s2c "fig"); TEndGroup; (* REF-005 *)
      TCommand (s2c "eqref"); TBeginGroup; TText (s2c ""); TEndGroup; (* REF-006 *)
      
      (* SCRIPT issues *)
      TSuperscript; TSuperscript; (* SCRIPT-001 *)
      TSubscript; TBeginGroup; TEndGroup; (* SCRIPT-002 *)
      
      (* CMD issues *)
      TCommand (s2c "bf"); (* CMD-001 *)
      TCommand (s2c "tiny"); (* CMD-002 *)
      TCommand (s2c "def"); (* CMD-003 *)
      TCommand (s2c "MyCommand"); (* CMD-004 *)
      TCommand (s2c "newcommand"); TBeginGroup; TCommand (s2c "x"); TEndGroup; (* CMD-005 *)
      
      (* POST issues *)
      TText (s2c "$$equation$$"); (* POST-037 *)
      TText (s2c "  "); (* POST-034 *)
      TText (s2c "http://example.com"); (* POST-028 *)
      TText (s2c "e.g."); (* POST-029 *)
      TText (s2c "can not"); (* POST-030 *)
      TText (s2c " ,"); (* POST-031 *)
      TText (s2c " ."); (* POST-032 *)
      TText (s2c "("); (* POST-033 *)
      TText (s2c "!!"); (* POST-035 *)
      TText (s2c "??"); (* POST-036 *)
      TText (s2c "colour"); (* POST-038 *)
      TText (s2c "---"); (* POST-039 *)
      TText (s2c "..."); (* POST-040 *)
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  } in
  
  let issues = run_all_validators mega_doc in
  
  (* Count unique validators *)
  let unique_ids = ref [] in
  List.iter (fun issue ->
    let id = c2s issue.rule_id in
    if not (List.mem id !unique_ids) then
      unique_ids := id :: !unique_ids
  ) issues;
  
  unique_ids := List.sort compare !unique_ids;
  
  (* Group by category *)
  let delim = List.filter (fun id -> String.length id >= 5 && String.sub id 0 5 = "DELIM") !unique_ids in
  let math = List.filter (fun id -> String.length id >= 4 && String.sub id 0 4 = "MATH") !unique_ids in
  let ref = List.filter (fun id -> String.length id >= 3 && String.sub id 0 3 = "REF") !unique_ids in
  let script = List.filter (fun id -> String.length id >= 6 && String.sub id 0 6 = "SCRIPT") !unique_ids in
  let cmd = List.filter (fun id -> String.length id >= 3 && String.sub id 0 3 = "CMD") !unique_ids in
  let post = List.filter (fun id -> String.length id >= 4 && String.sub id 0 4 = "POST") !unique_ids in
  
  Printf.printf "VALIDATORS TRIGGERED:\n";
  Printf.printf "===================\n";
  Printf.printf "DELIM: %d validators\n" (List.length delim);
  List.iter (Printf.printf "  %s\n") delim;
  Printf.printf "MATH: %d validators\n" (List.length math);
  List.iter (Printf.printf "  %s\n") math;
  Printf.printf "REF: %d validators\n" (List.length ref);
  List.iter (Printf.printf "  %s\n") ref;
  Printf.printf "SCRIPT: %d validators\n" (List.length script);
  List.iter (Printf.printf "  %s\n") script;
  Printf.printf "CMD: %d validators\n" (List.length cmd);
  List.iter (Printf.printf "  %s\n") cmd;
  Printf.printf "POST: %d validators\n" (List.length post);
  List.iter (Printf.printf "  %s\n") post;
  
  let phase_1_5_total = (List.length delim) + (List.length math) + 
                        (List.length ref) + (List.length script) + (List.length cmd) in
  
  Printf.printf "\n=== SUMMARY ===\n";
  Printf.printf "Phase 1.5 validators triggered: %d/50\n" phase_1_5_total;
  Printf.printf "Total issues found: %d\n" (List.length issues);
  
  if phase_1_5_total >= 48 then
    Printf.printf "\n✅ AUDIT PASSED: Most validators are working!\n"
  else
    Printf.printf "\n❌ AUDIT INCOMPLETE: Only %d/50 validators triggered\n" phase_1_5_total