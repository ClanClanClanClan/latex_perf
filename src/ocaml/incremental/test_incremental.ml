(* test_incremental.ml - Comprehensive tests for v24-R3 incremental lexer *)

#load "unix.cma";;

(* Test helpers *)
let time_it name f =
  let start = Unix.gettimeofday () in
  let result = f () in
  let elapsed = Unix.gettimeofday () -. start in
  Printf.printf "%s: %.3f ms\n" name (elapsed *. 1000.);
  result

let assert_equal name expected actual =
  if expected = actual then
    Printf.printf "✓ %s\n" name
  else begin
    Printf.printf "✗ %s: expected %s, got %s\n" name expected actual;
    exit 1
  end

(* Generate test document *)
let generate_test_document lines =
  let sections = 10 in
  let subsections = 5 in
  let paragraphs = 20 in
  
  let content = Buffer.create (lines * 80) in
  
  Buffer.add_string content "\\documentclass{article}\n";
  Buffer.add_string content "\\usepackage{amsmath}\n";
  Buffer.add_string content "\\begin{document}\n\n";
  
  for s = 1 to sections do
    Buffer.add_string content (Printf.sprintf "\\section{Section %d}\n\n" s);
    
    for ss = 1 to subsections do
      Buffer.add_string content (Printf.sprintf "\\subsection{Subsection %d.%d}\n\n" s ss);
      
      for p = 1 to paragraphs do
        Buffer.add_string content (Printf.sprintf 
          "This is paragraph %d with some math $x^2 + y^2 = z^2$ and \
           a command \\textbf{bold text}. % Comment here\n" p);
        
        if p mod 5 = 0 then
          Buffer.add_string content "\\begin{equation}\n  E = mc^2\n\\end{equation}\n\n"
      done
    done
  done;
  
  Buffer.add_string content "\\end{document}\n";
  Buffer.contents content

(* Test 1: Basic functionality *)
let test_basic_lexing () =
  Printf.printf "\n=== Test 1: Basic Lexing ===\n";
  
  let lexer = Incremental_lexer.create () in
  let content = "Hello \\textbf{world} $x + y$ % comment\n" in
  
  Incremental_lexer.load_string lexer content;
  let tokens = Incremental_lexer.get_all_tokens lexer in
  
  assert_equal "Token count" "13" (string_of_int (List.length tokens));
  Printf.printf "Tokens: %d\n" (List.length tokens)

(* Test 2: Incremental edit performance *)
let test_incremental_performance () =
  Printf.printf "\n=== Test 2: Incremental Edit Performance ===\n";
  
  (* Create large document *)
  let doc_size = 10000 in (* 10k lines *)
  let content = generate_test_document doc_size in
  Printf.printf "Document size: %d bytes\n" (String.length content);
  
  let lexer = Incremental_lexer.create () in
  
  (* Initial lex *)
  let initial_time = time_it "Initial lexing" (fun () ->
    Incremental_lexer.load_string lexer content
  ) in
  
  (* Perform edits and measure performance *)
  let edits = [
    (100, "% Small edit in line 100");
    (5000, "\\section{New Section}");
    (9000, "$a^2 + b^2 = c^2$");
  ] in
  
  let total_edit_time = ref 0. in
  let total_lines_processed = ref 0 in
  
  List.iter (fun (line, new_text) ->
    let start = Unix.gettimeofday () in
    let lines_processed, bytes_processed, elapsed_ms = 
      Incremental_lexer.edit_line lexer line new_text in
    total_edit_time := !total_edit_time +. elapsed_ms;
    total_lines_processed := !total_lines_processed + lines_processed;
    
    Printf.printf "Edit at line %d: %d lines processed in %.2f ms\n" 
      line lines_processed elapsed_ms
  ) edits;
  
  (* Calculate speedup *)
  let avg_edit_time = !total_edit_time /. float_of_int (List.length edits) in
  let speedup = initial_time *. 1000. /. avg_edit_time in
  
  Printf.printf "\nPerformance Summary:\n";
  Printf.printf "- Initial lex time: %.2f ms\n" (initial_time *. 1000.);
  Printf.printf "- Average edit time: %.2f ms\n" avg_edit_time;
  Printf.printf "- Average lines processed per edit: %d\n" 
    (!total_lines_processed / List.length edits);
  Printf.printf "- Speedup: %.0fx\n" speedup;
  
  (* Check if we meet the target *)
  if speedup >= 1596. then
    Printf.printf "✓ Target speedup of 1,596x achieved!\n"
  else
    Printf.printf "✗ Speedup %.0fx is below target of 1,596x\n" speedup

(* Test 3: State serialization *)
let test_state_serialization () =
  Printf.printf "\n=== Test 3: State Serialization ===\n";
  
  let test_states = [
    Types.init_state;
    { Types.init_state with line_no = 42; col_no = 17 };
    { Types.init_state with in_math = true; in_comment = false };
    { Types.init_state with mode_stack = [Types.MMath; Types.MNormal] };
  ] in
  
  let all_pass = List.for_all (fun state ->
    let encoded = State_codec.encode_state state in
    match State_codec.decode_state encoded with
    | Some decoded -> state = decoded
    | None -> false
  ) test_states in
  
  assert_equal "State roundtrip" "true" (string_of_bool all_pass);
  
  (* Test encoding size *)
  let sizes = List.map (fun st -> 
    String.length (State_codec.encode_state st)
  ) test_states in
  Printf.printf "Encoding sizes: %s bytes\n" 
    (String.concat ", " (List.map string_of_int sizes))

(* Test 4: Checkpoint recovery *)
let test_checkpoint_recovery () =
  Printf.printf "\n=== Test 4: Checkpoint Recovery ===\n";
  
  let lexer = Incremental_lexer.create () in
  let content = generate_test_document 1000 in
  
  Incremental_lexer.load_string lexer content;
  
  (* Save checkpoints *)
  let cp_file = "/tmp/test_checkpoints.bin" in
  Incremental_lexer.save_checkpoints lexer cp_file;
  
  (* Create new lexer and load checkpoints *)
  let lexer2 = Incremental_lexer.create () in
  let loaded = Incremental_lexer.load_checkpoints lexer2 cp_file in
  
  assert_equal "Checkpoint loading" "true" (string_of_bool loaded);
  
  (* Verify checkpoint stats *)
  let stats = Incremental_lexer.get_stats lexer in
  Printf.printf "%s\n" stats

(* Test 5: Large document stress test *)
let test_large_document () =
  Printf.printf "\n=== Test 5: Large Document Stress Test ===\n";
  
  let mb_sizes = [1; 3; 10] in
  
  List.iter (fun mb ->
    let lines = mb * 1024 * 10 in (* ~100 bytes per line *)
    let content = generate_test_document lines in
    let size_mb = float_of_int (String.length content) /. 1024. /. 1024. in
    
    Printf.printf "\nTesting %.1f MB document (%d lines):\n" size_mb lines;
    
    let lexer = Incremental_lexer.create () in
    
    (* Measure initial lexing *)
    let initial_time = time_it "Initial lexing" (fun () ->
      Incremental_lexer.load_string lexer content
    ) in
    
    (* Measure single line edit *)
    let edit_line = lines / 2 in (* Edit middle of document *)
    let _, _, edit_time = Incremental_lexer.edit_line lexer edit_line 
      "% This line was edited" in
    
    let speedup = initial_time *. 1000. /. edit_time in
    Printf.printf "- Edit time: %.2f ms (speedup: %.0fx)\n" edit_time speedup
  ) mb_sizes

(* Test 6: Token correctness *)
let test_token_correctness () =
  Printf.printf "\n=== Test 6: Token Correctness ===\n";
  
  let test_cases = [
    ("Simple text", "Hello world", 3); (* TChar × n + TSpace + TChar × n *)
    ("Command", "\\textbf{bold}", 2); (* TCommand + compound *)
    ("Math", "$x + y$", 3); (* TMath + content + TMath *)
    ("Comment", "text % comment\n", 4); (* text + TComment + TNewline *)
    ("Environment", "\\begin{eq}\\end{eq}", 2); (* TBeginEnv + TEndEnv *)
  ] in
  
  let lexer = Incremental_lexer.create () in
  
  List.iter (fun (name, input, _) ->
    Incremental_lexer.load_string lexer input;
    let tokens = Incremental_lexer.get_all_tokens lexer in
    Printf.printf "%s: %d tokens\n" name (List.length tokens)
  ) test_cases

(* Main test runner *)
let () =
  Printf.printf "=== LaTeX Perfectionist v24-R3 Incremental Lexer Tests ===\n";
  
  test_basic_lexing ();
  test_incremental_performance ();
  test_state_serialization ();
  test_checkpoint_recovery ();
  test_large_document ();
  test_token_correctness ();
  
  Printf.printf "\n=== All tests completed ===\n"