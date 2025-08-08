(* Comprehensive L2 Parser Debug Analysis *)

open Lexer_v25
open L1_expander
open L2_parser

let tokenize_and_expand text =
  let tokens = L0_lexer_track_a_arena.tokenize text in
  let l1_state = L1_expander.initial_state () in
  let expanded = L1_expander.expand_tokens l1_state tokens in
  Array.of_list expanded.tokens

let debug_test name text expected_pattern =
  Printf.printf "\n🔍 %s\n" name;
  Printf.printf "Input: %s\n" text;
  
  let tokens = tokenize_and_expand text in
  Printf.printf "Tokens (%d): " (Array.length tokens);
  Array.iteri (fun i tok ->
    if i < 10 then Printf.printf "%s " (Lexer_v25.token_to_string tok)
    else if i = 10 then Printf.printf "..."
  ) tokens;
  Printf.printf "\n";
  
  let doc = L2_parser.parse tokens in
  Printf.printf "Parsed AST:\n";
  Format.printf "  %a@." L2_parser.pp_document doc;
  
  Printf.printf "Expected: %s\n" expected_pattern;
  Printf.printf "Status: %s\n" (if List.length doc.body > 0 then "✅ Parsed" else "❌ Failed");
  Printf.printf "---\n"

let () =
  Printf.printf "🧪 COMPREHENSIVE L2 PARSER ANALYSIS\n";
  Printf.printf "==================================\n";
  
  (* Test 1: Simple text - character coalescing *)
  debug_test "Simple Text" 
    "Hello world!"
    "Paragraph with coalesced text";
  
  (* Test 2: Section parsing *)
  debug_test "Section Parsing" 
    "\\section{Introduction}"
    "Section node with title";
  
  (* Test 3: Section with content *)
  debug_test "Section with Content"
    "\\section{Test}\\nSome text here."
    "Section containing paragraph";
  
  (* Test 4: Simple environment *)
  debug_test "Environment Parsing"
    "\\begin{itemize}\\n\\item First\\n\\end{itemize}"
    "Environment node with body";
  
  (* Test 5: Inline math *)
  debug_test "Inline Math"
    "The equation $x + y = z$ is simple."
    "Paragraph with inline math";
  
  (* Test 6: Display math *)
  debug_test "Display Math"
    "\\[E = mc^2\\]"
    "MathDisplay node";
  
  (* Test 7: Command with args *)
  debug_test "Command with Args"
    "\\textbf{bold text}"
    "Paragraph with command";
  
  (* Test 8: Mixed content *)
  debug_test "Mixed Content"
    "Normal text \\textit{italic} and $math$ here."
    "Paragraph with mixed inline content";
  
  Printf.printf "\n✅ Analysis complete!\n"