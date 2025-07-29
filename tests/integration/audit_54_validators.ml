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
  Printf.printf "=== COMPREHENSIVE 54 VALIDATOR AUDIT ===\n\n";
  
  (* Create comprehensive test document to trigger as many validators as possible *)
  let mega_doc = { 
    tokens = []; 
    expanded_tokens = Some [
      (* DELIM issues *)
      TBeginGroup; TBeginGroup; TEndGroup; (* unmatched braces *)
      TEndGroup; (* extra closing *)
      TBeginGroup; TBeginGroup; TBeginGroup; TBeginGroup; TBeginGroup; (* deep nesting *)
      TMathShift; TBeginGroup; TMathShift; TEndGroup; (* mixed contexts *)
      TCommand (s2c "begin"); TBeginGroup; TText (s2c "env"); TEndGroup;
      TCommand (s2c "left"); TText (s2c "(");
      TCommand (s2c "big"); TText (s2c "(");
      TCommand (s2c "begin"); TBeginGroup; TEndGroup; (* empty env *)
      TMathShift; TMathShift; (* enter math mode *)
      
      (* MATH issues - comprehensive coverage *)
      TMathShift; TCommand (s2c "matrix"); TMathShift; (* MATH-002 *)
      TMathShift; TCommand (s2c "choose"); TMathShift; (* MATH-003 *)
      TMathShift; TCommand (s2c "frac"); TBeginGroup; TText (s2c "a"); TEndGroup; TBeginGroup; TText (s2c "b"); TEndGroup; TMathShift; (* MATH-004 *)
      TMathShift; TCommand (s2c "sqrt"); TBeginGroup; TText (s2c "x"); TEndGroup; TMathShift; (* MATH-005 *)
      TMathShift; TCommand (s2c "text"); TBeginGroup; TText (s2c "word"); TEndGroup; TMathShift; (* MATH-006 *)
      TMathShift; TCommand (s2c "mathbb"); TBeginGroup; TText (s2c "R"); TEndGroup; TMathShift; (* MATH-007 *)
      TMathShift; TCommand (s2c "limits"); TMathShift; (* MATH-009 *)
      TMathShift; TCommand (s2c "dots"); TMathShift; (* MATH-010 *)
      TMathShift; TCommand (s2c "vec"); TBeginGroup; TText (s2c "v"); TEndGroup; TMathShift; (* MATH-011 *)
      TMathShift; TText (s2c "sin"); TText (s2c "x"); TMathShift; (* MATH-012 *)
      TMathShift; TCommand (s2c "ln"); TText (s2c "x"); TMathShift; (* MATH-013 *)
      TCommand (s2c "frac"); TBeginGroup; TText (s2c "1"); TEndGroup; TBeginGroup; TText (s2c "2"); TEndGroup; (* MATH-014 in text *)
      TMathShift; TCommand (s2c "left"); TText (s2c "("); TMathShift; (* MATH-015 *)
      TMathShift; TCommand (s2c "eqref"); TBeginGroup; TText (s2c "eq1"); TEndGroup; TMathShift; (* MATH-016 *)
      TMathShift; TCommand (s2c "left"); TText (s2c "{"); TCommand (s2c "right"); TText (s2c "]"); TMathShift; (* MATH-017 *)
      TMathShift; TCommand (s2c "tag"); TBeginGroup; TText (s2c "1"); TEndGroup; TMathShift; (* MATH-018 *)
      TMathShift; TText (s2c "x"); TSuperscript; TText (s2c "2"); TSubscript; TText (s2c "i"); TMathShift; (* MATH-019 *)
      TMathShift; TCommand (s2c "mathit"); TBeginGroup; TText (s2c "var"); TEndGroup; TMathShift; (* MATH-020 *)
      
      (* REF issues *)
      TCommand (s2c "ref"); TBeginGroup; TEndGroup; (* REF-001 empty *)
      TCommand (s2c "label"); TBeginGroup; TText (s2c "eq:test"); TEndGroup; (* REF-002 *)
      TCommand (s2c "cite"); TBeginGroup; TEndGroup; (* REF-003 empty *)
      TCommand (s2c "label"); TBeginGroup; TText (s2c "bad name"); TEndGroup; (* REF-004 *)
      TCommand (s2c "ref"); TBeginGroup; TText (s2c "fig"); TEndGroup; (* REF-005 *)
      TCommand (s2c "eqref"); TBeginGroup; TText (s2c ""); TEndGroup; (* REF-006 empty *)
      
      (* SCRIPT issues *)
      TSuperscript; TSuperscript; TText (s2c "2"); (* SCRIPT-001 double super *)
      TSubscript; TBeginGroup; TEndGroup; (* SCRIPT-002 empty *)
      
      (* CMD issues *)
      TCommand (s2c "bf"); (* CMD-001 obsolete *)
      TCommand (s2c "tiny"); (* CMD-002 obsolete size *)
      TCommand (s2c "def"); TCommand (s2c "mymacro"); (* CMD-003 plain TeX *)
      TCommand (s2c "MyCommand"); (* CMD-004 CamelCase *)
      TCommand (s2c "newcommand"); TBeginGroup; TCommand (s2c "x"); TEndGroup; (* CMD-005 single letter *)
      
      (* POST issues *)
      TText (s2c "$$x^2$$"); (* POST-037 display math *)
      TText (s2c "  "); (* POST-034 multiple spaces *)
      TText (s2c "http://example.com"); (* POST-028 raw URL *)
      TText (s2c "e.g."); (* POST-029 abbreviation *)
      TText (s2c "can not"); (* POST-030 spacing *)
      TText (s2c " ,"); (* POST-031 space before comma *)
      TText (s2c " ."); (* POST-032 space before period *)
      TText (s2c "("); TText (s2c "text"); (* POST-033 isolated paren *)
      TText (s2c "!!"); (* POST-035 double exclamation *)
      TText (s2c "??"); (* POST-036 double question *)
      TText (s2c "colour"); (* POST-038 British spelling *)
      TText (s2c "---"); (* POST-039 triple dash *)
      TText (s2c "..."); (* POST-040 triple dot *)
    ];
    ast = None; semantics = None;
    filename = s2c "comprehensive_test.tex"; doc_layer = L1_Expanded;
  } in
  
  let issues = run_all_validators mega_doc in
  
  (* Analyze results *)
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
  
  Printf.printf "VALIDATORS TRIGGERED IN AUDIT:\n";
  Printf.printf "==============================\n\n";
  
  Printf.printf "DELIM validators (%d triggered):\n" (List.length delim);
  List.iter (Printf.printf "  ✓ %s\n") delim;
  Printf.printf "\n";
  
  Printf.printf "MATH validators (%d triggered):\n" (List.length math);
  List.iter (Printf.printf "  ✓ %s\n") math;
  Printf.printf "\n";
  
  Printf.printf "REF validators (%d triggered):\n" (List.length ref);
  List.iter (Printf.printf "  ✓ %s\n") ref;
  Printf.printf "\n";
  
  Printf.printf "SCRIPT validators (%d triggered):\n" (List.length script);
  List.iter (Printf.printf "  ✓ %s\n") script;
  Printf.printf "\n";
  
  Printf.printf "CMD validators (%d triggered):\n" (List.length cmd);
  List.iter (Printf.printf "  ✓ %s\n") cmd;
  Printf.printf "\n";
  
  Printf.printf "POST validators (%d triggered):\n" (List.length post);
  List.iter (Printf.printf "  ✓ %s\n") post;
  Printf.printf "\n";
  
  let phase_1_5_triggered = (List.length delim) + (List.length math) + 
                           (List.length ref) + (List.length script) + (List.length cmd) in
  
  Printf.printf "=== AUDIT RESULTS ===\n";
  Printf.printf "Total issues detected: %d\n" (List.length issues);
  Printf.printf "Unique validators triggered: %d\n" (List.length !unique_ids);
  Printf.printf "Phase 1.5 validators triggered: %d/54\n" phase_1_5_triggered;
  Printf.printf "POST validators triggered: %d\n" (List.length post);
  Printf.printf "Triggering success rate: %.1f%%\n" 
    (float_of_int phase_1_5_triggered *. 100.0 /. 54.0);
  
  Printf.printf "\n=== IMPLEMENTATION STATUS ===\n";
  Printf.printf "📊 Total implemented: 54/80 validators (67.5%%)\n";
  Printf.printf "🎯 Functional validators: %d/54 (%.1f%%)\n" 
    phase_1_5_triggered 
    (float_of_int phase_1_5_triggered *. 100.0 /. 54.0);
  
  if phase_1_5_triggered >= 25 then
    Printf.printf "✅ AUDIT PASSED: Good validator coverage!\n"
  else
    Printf.printf "⚠️  AUDIT CONCERN: Low triggering rate - need investigation\n"