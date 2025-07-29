(* test_checkpoint_fix.ml - Test that checkpoint manager is working correctly *)

open Latex_perfectionist_incremental

let test_checkpoint_manager () =
  Printf.printf "=== Testing Checkpoint Manager Fix ===\n\n";
  
  (* Create a realistic document with multiple sections *)
  let lines = Array.init 1000 (fun i ->
    if i mod 100 = 0 then
      Printf.sprintf "\\section{Section %d - Major heading at line %d}" (i/100) i
    else if i mod 50 = 0 then  
      Printf.sprintf "\\subsection{Subsection at line %d with math $x^2 + y^2 = z^2$}" i
    else if i mod 20 = 0 then
      Printf.sprintf "\\begin{equation} f(x) = \\int_0^x e^{-t^2} dt \\quad \\text{at line %d} \\end{equation}" i
    else
      Printf.sprintf "This is regular text content on line %d with some \\textbf{formatting} and references." i
  ) in
  
  let content = String.concat "\n" (Array.to_list lines) in
  Printf.printf "Created test document: %d lines, %.2f KB\n" 
    (Array.length lines) (float_of_int (String.length content) /. 1024.0);
  
  (* Create optimized lexer *)
  let lexer = Incremental_lexer_optimized.create_optimized () in
  
  (* Load document *)
  Printf.printf "Loading document...\n";
  Incremental_lexer_optimized.load_string lexer content;
  Printf.printf "Document loaded successfully\n\n";
  
  (* Test checkpoints at different edit locations *)
  let test_locations = [50; 100; 200; 300; 500; 750; 900] in
  
  Printf.printf "Testing checkpoint recovery points:\n";
  Printf.printf "%-10s %-15s %-15s %-10s\n" "Edit Line" "Checkpoint" "Relex Point" "Status";
  Printf.printf "%s\n" (String.make 50 '-');
  
  List.iter (fun edit_line ->
    if edit_line < Array.length lexer.document.lines then begin
      (* Test the checkpoint manager directly *)
      let checkpoint_line, checkpoint_state = 
        Checkpoint_manager_real.find_recovery_point_by_line 
          lexer.checkpoint_mgr lexer.document edit_line in
      
      let relex_point = 
        if checkpoint_state.in_verbatim || 
           checkpoint_state.math_mode <> NoMath ||
           checkpoint_state.group_level > 0 then
          max 0 (checkpoint_line - 10)
        else
          checkpoint_line in
      
      let status = 
        if checkpoint_line = 0 then "❌ BROKEN"
        else if checkpoint_line >= edit_line then "❌ INVALID" 
        else "✅ WORKING" in
      
      Printf.printf "%-10d %-15d %-15d %-10s\n" 
        edit_line checkpoint_line relex_point status
    end
  ) test_locations;
  
  Printf.printf "\n";
  
  (* Test actual edit performance *)
  Printf.printf "Testing actual edit performance:\n";
  Printf.printf "%-15s %-10s %-15s %-10s\n" "Edit Location" "Time (ms)" "Lines Processed" "Speedup";
  Printf.printf "%s\n" (String.make 55 '-');
  
  let baseline_time = lexer.document.last_full_lex_time *. 1000.0 in
  
  List.iter (fun edit_line ->
    if edit_line < Array.length lexer.document.lines then begin
      let new_text = "% Modified line at position " ^ string_of_int edit_line in
      let (lines_proc, _, time_ms) = 
        Incremental_lexer_optimized.edit_line lexer edit_line new_text in
      
      let speedup = if time_ms > 0.0 then baseline_time /. time_ms else 0.0 in
      
      Printf.printf "%-15d %-10.2f %-15d %-10.1fx\n" 
        edit_line time_ms lines_proc speedup
    end
  ) test_locations;
  
  Printf.printf "\nOverall Results:\n";
  let final_speedup = Incremental_lexer_optimized.calculate_achieved_speedup lexer in
  Printf.printf "Average achieved speedup: %.1fx\n" final_speedup;
  
  if final_speedup > 1.0 then
    Printf.printf "✅ Checkpoint manager is working - real incremental processing achieved!\n"
  else
    Printf.printf "❌ Still broken - no real speedup achieved\n";
  
  Printf.printf "\n=== Test Complete ===\n"

let () = test_checkpoint_manager ()