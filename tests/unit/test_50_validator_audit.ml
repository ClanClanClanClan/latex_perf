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

(* Collect all unique validator IDs from different test cases *)
let all_validators = ref []

let test_and_collect doc =
  let issues = run_all_validators doc in
  List.iter (fun issue ->
    let id = c2s issue.rule_id in
    if not (List.mem id !all_validators) then
      all_validators := id :: !all_validators
  ) issues

let () =
  Printf.printf "=== COMPREHENSIVE 50 VALIDATOR AUDIT ===\n\n";
  
  (* Test various document states to trigger different validators *)
  
  (* Empty document *)
  test_and_collect { 
    tokens = []; expanded_tokens = Some [];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  };
  
  (* DELIM validators *)
  test_and_collect {
    tokens = []; expanded_tokens = Some [TBeginGroup; TBeginGroup; TEndGroup];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  };
  
  (* MATH validators *)
  test_and_collect {
    tokens = []; expanded_tokens = Some [
      TMathShift; TCommand (s2c "matrix"); TMathShift;
      TCommand (s2c "frac"); TBeginGroup; TEndGroup;
      TCommand (s2c "limits"); TSuperscript; TText (s2c "2")
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  };
  
  (* REF validators *)
  test_and_collect {
    tokens = []; expanded_tokens = Some [
      TCommand (s2c "ref"); TBeginGroup; TEndGroup;
      TCommand (s2c "label"); TBeginGroup; TText (s2c "eq:1"); TEndGroup;
      TCommand (s2c "cite"); TBeginGroup; TText (s2c ""); TEndGroup
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  };
  
  (* SCRIPT validators *)
  test_and_collect {
    tokens = []; expanded_tokens = Some [
      TSuperscript; TSuperscript;
      TSubscript; TBeginGroup; TEndGroup
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  };
  
  (* CMD validators *)
  test_and_collect {
    tokens = []; expanded_tokens = Some [
      TCommand (s2c "tiny");
      TCommand (s2c "def");
      TCommand (s2c "TestCommand");
      TCommand (s2c "newcommand"); TBeginGroup; TCommand (s2c "x"); TEndGroup
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  };
  
  (* POST validators - test with various text patterns *)
  test_and_collect {
    tokens = []; expanded_tokens = Some [
      TText (s2c "$$x^2$$");
      TText (s2c "http://example.com");
      TText (s2c "e.g.");
      TText (s2c "can not");
      TText (s2c "  ");
      TText (s2c "todo");
      TText (s2c "(");
      TText (s2c "!!");
      TText (s2c "colour");
      TText (s2c "---");
      TText (s2c "...")
    ];
    ast = None; semantics = None;
    filename = s2c "test.tex"; doc_layer = L1_Expanded;
  };
  
  (* Sort and display all found validators *)
  all_validators := List.sort compare !all_validators;
  
  Printf.printf "VALIDATORS FOUND:\n";
  Printf.printf "================\n";
  
  (* Group by category *)
  let delim = List.filter (fun id -> String.sub id 0 5 = "DELIM") !all_validators in
  let math = List.filter (fun id -> String.sub id 0 4 = "MATH") !all_validators in
  let ref = List.filter (fun id -> String.sub id 0 3 = "REF") !all_validators in
  let script = List.filter (fun id -> String.sub id 0 6 = "SCRIPT") !all_validators in
  let cmd = List.filter (fun id -> String.sub id 0 3 = "CMD") !all_validators in
  let post = List.filter (fun id -> String.sub id 0 4 = "POST") !all_validators in
  
  Printf.printf "\nDELIM validators (%d):\n" (List.length delim);
  List.iter (Printf.printf "  - %s\n") delim;
  
  Printf.printf "\nMATH validators (%d):\n" (List.length math);
  List.iter (Printf.printf "  - %s\n") math;
  
  Printf.printf "\nREF validators (%d):\n" (List.length ref);
  List.iter (Printf.printf "  - %s\n") ref;
  
  Printf.printf "\nSCRIPT validators (%d):\n" (List.length script);
  List.iter (Printf.printf "  - %s\n") script;
  
  Printf.printf "\nCMD validators (%d):\n" (List.length cmd);
  List.iter (Printf.printf "  - %s\n") cmd;
  
  Printf.printf "\nPOST validators (%d):\n" (List.length post);
  List.iter (Printf.printf "  - %s\n") post;
  
  let total = List.length !all_validators in
  let phase_1_5_total = (List.length delim) + (List.length math) + 
                        (List.length ref) + (List.length script) + (List.length cmd) in
  
  Printf.printf "\n=== AUDIT SUMMARY ===\n";
  Printf.printf "Total unique validators: %d\n" total;
  Printf.printf "Phase 1.5 validators: %d/80 = %.1f%%\n" 
    phase_1_5_total 
    (float_of_int phase_1_5_total *. 100.0 /. 80.0);
  Printf.printf "POST validators (bonus): %d\n" (List.length post);
  
  (* Verify expected counts *)
  Printf.printf "\n=== VERIFICATION ===\n";
  Printf.printf "DELIM: %d/10 %s\n" (List.length delim) 
    (if List.length delim = 10 then "✓" else "✗");
  Printf.printf "MATH: %d/40 %s\n" (List.length math)
    (if List.length math >= 14 then "✓" else "✗");
  Printf.printf "REF: %d/10 %s\n" (List.length ref)
    (if List.length ref >= 6 then "✓" else "✗");
  Printf.printf "SCRIPT: %d/10 %s\n" (List.length script)
    (if List.length script >= 2 then "✓" else "✗");
  Printf.printf "CMD: %d/10 %s\n" (List.length cmd)
    (if List.length cmd >= 5 then "✓" else "✗");
  Printf.printf "POST: %d %s\n" (List.length post)
    (if List.length post >= 13 then "✓" else "✗");
  
  if phase_1_5_total = 50 then
    Printf.printf "\n✅ AUDIT PASSED: All 50 Phase 1.5 validators are working!\n"
  else
    Printf.printf "\n❌ AUDIT FAILED: Expected 50 Phase 1.5 validators, found %d\n" phase_1_5_total