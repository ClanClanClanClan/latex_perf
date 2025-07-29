(** Test all 76+ built-in macros *)

module L1_v25 = Layer1.L1_v25
module Types = Latex_perfectionist_core.Types
module CommonMacros = Common_macros

let test_macro_expansion () =
  Printf.printf "=== TESTING ALL BUILT-IN MACROS ===\n";
  Printf.printf "Total macros defined: %d\n\n" CommonMacros.macro_count;
  
  (* Test a sample from each category *)
  let test_macros = [
    (* Text formatting *)
    ("LaTeX", "LaTeX");
    ("TeX", "TeX");
    ("textbf", "[bold]");
    ("textit", "[italic]");
    ("texttt", "[monospace]");
    
    (* Greek letters *)
    ("alpha", "α");
    ("beta", "β");
    ("pi", "π");
    ("omega", "ω");
    
    (* Math symbols *)
    ("sum", "∑");
    ("int", "∫");
    ("infty", "∞");
    ("leq", "≤");
    ("rightarrow", "→");
    ("forall", "∀");
    
    (* Spacing *)
    ("ldots", "...");
    ("cdots", "⋯");
    
    (* Special characters *)
    ("copyright", "©");
    ("S", "§");
  ] in
  
  let l0_key = { Layer0.L0_v25.chunk_id = 0; hash = 0L } in
  let l1_env = L1_v25.initial_state l0_key in
  
  let passed = ref 0 in
  let failed = ref 0 in
  
  List.iter (fun (macro_name, expected) ->
    let tokens = [|Types.TCommand macro_name; Types.TBeginGroup; Types.TEndGroup|] in
    let delta = { 
      L1_v25.unexpanded = tokens; 
      expanded = [||]; 
      macros_used = [] 
    } in
    
    let fuel = 10 in
    let (expanded_delta, _) = L1_v25.expand_delta ~fuel ~env:l1_env delta in
    
    (* Check if expansion is correct *)
    if Array.length expanded_delta.L1_v25.expanded >= 1 then
      match expanded_delta.L1_v25.expanded.(0) with
      | Types.TText actual when actual = expected ->
          Printf.printf "✅ \\%s → %s\n" macro_name expected;
          incr passed
      | Types.TText actual ->
          Printf.printf "❌ \\%s → %s (expected %s)\n" macro_name actual expected;
          incr failed
      | _ ->
          Printf.printf "❌ \\%s → (not text)\n" macro_name;
          incr failed
    else begin
      Printf.printf "❌ \\%s → (no expansion)\n" macro_name;
      incr failed
    end
  ) test_macros;
  
  Printf.printf "\n=== SUMMARY ===\n";
  Printf.printf "Passed: %d\n" !passed;
  Printf.printf "Failed: %d\n" !failed;
  Printf.printf "Total tested: %d / %d macros\n" (!passed + !failed) CommonMacros.macro_count

let test_unknown_macro () =
  Printf.printf "\n=== TESTING UNKNOWN MACRO ===\n";
  
  let l0_key = { Layer0.L0_v25.chunk_id = 0; hash = 0L } in
  let l1_env = L1_v25.initial_state l0_key in
  
  let tokens = [|Types.TCommand "unknownmacro"; Types.TBeginGroup; Types.TEndGroup|] in
  let delta = { 
    L1_v25.unexpanded = tokens; 
    expanded = [||]; 
    macros_used = [] 
  } in
  
  let fuel = 10 in
  let (expanded_delta, _) = L1_v25.expand_delta ~fuel ~env:l1_env delta in
  
  (* Unknown macro should not be expanded *)
  if expanded_delta.L1_v25.expanded = tokens then
    Printf.printf "✅ Unknown macro preserved\n"
  else
    Printf.printf "❌ Unknown macro was modified\n"

let () =
  test_macro_expansion ();
  test_unknown_macro ()