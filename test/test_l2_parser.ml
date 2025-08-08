(** L2 Parser Test Suite - LaTeX Perfectionist v25 *)

open Lexer_v25
open L1_expander
open L2_parser

(* Test utilities *)
let test name f =
  Printf.printf "  %s... %!" name;
  try
    f ();
    Printf.printf "✅\n%!"
  with e ->
    Printf.printf "❌\n";
    Printf.printf "    Error: %s\n" (Printexc.to_string e)

let tokenize_and_expand text =
  let tokens = L0_lexer_track_a_arena.tokenize text in
  let l1_state = L1_expander.initial_state () in
  let expanded = L1_expander.expand_tokens l1_state tokens in
  Array.of_list expanded.tokens

(* Test cases *)
let test_simple_paragraph () =
  test "Simple paragraph" (fun () ->
    let tokens = tokenize_and_expand "Hello world!" in
    let doc = L2_parser.parse tokens in
    
    match doc.body with
    | [Paragraph [Text "Hello"; Space; Text "world!"]] ->
        ()
    | _ ->
        failwith "Unexpected AST structure"
  )

let test_section_parsing () =
  test "Section parsing" (fun () ->
    let tokens = tokenize_and_expand "\\section{Introduction}\nSome text here." in
    let doc = L2_parser.parse tokens in
    
    match doc.body with
    | [Section { level = 1; title = [Text "Introduction"]; content = [Paragraph _] }] ->
        ()
    | _ ->
        failwith "Failed to parse section"
  )

let test_environment_parsing () =
  test "Environment parsing" (fun () ->
    let tokens = tokenize_and_expand "\\begin{itemize}\n\\item First\n\\item Second\n\\end{itemize}" in
    let doc = L2_parser.parse tokens in
    
    match doc.body with
    | [Environment { name = "itemize"; args = []; body = _ }] ->
        ()
    | _ ->
        failwith "Failed to parse environment"
  )

let test_math_inline () =
  test "Inline math" (fun () ->
    let tokens = tokenize_and_expand "The equation $x + y = z$ is simple." in
    let doc = L2_parser.parse tokens in
    
    match doc.body with
    | [Paragraph inlines] ->
        let has_math = List.exists (function MathInline _ -> true | _ -> false) inlines in
        if not has_math then failwith "No inline math found"
    | _ ->
        failwith "Failed to parse paragraph with math"
  )

let test_math_display () =
  test "Display math" (fun () ->
    let tokens = tokenize_and_expand "\\[\n  E = mc^2\n\\]" in
    let doc = L2_parser.parse tokens in
    
    match doc.body with
    | [MathDisplay _] ->
        ()
    | _ ->
        failwith "Failed to parse display math"
  )

let test_command_with_args () =
  test "Command with arguments" (fun () ->
    let tokens = tokenize_and_expand "\\textbf{bold} and \\emph{emphasis}" in
    let doc = L2_parser.parse tokens in
    
    match doc.body with
    | [Paragraph inlines] ->
        let commands = List.filter (function Command _ -> true | _ -> false) inlines in
        if List.length commands < 2 then failwith "Missing commands"
    | _ ->
        failwith "Failed to parse commands"
  )

let test_nested_structures () =
  test "Nested structures" (fun () ->
    let text = "\\section{Main}\n\\subsection{Sub}\n\\begin{enumerate}\n\\item One\n\\end{enumerate}" in
    let tokens = tokenize_and_expand text in
    let doc = L2_parser.parse tokens in
    
    match doc.body with
    | [Section { level = 1; content = [Section { level = 2; content = [Environment _] }] }] ->
        ()
    | _ ->
        failwith "Failed to parse nested structures"
  )

let test_error_recovery () =
  test "Error recovery" (fun () ->
    let tokens = tokenize_and_expand "\\begin{missing}\nSome text\n\\section{Next}" in
    let doc = L2_parser.parse ~options:{ default_options with max_errors = 10 } tokens in
    
    (* Should have parsed the section despite the unclosed environment *)
    let has_section = List.exists (function Section _ -> true | _ -> false) doc.body in
    if not has_section then failwith "Error recovery failed"
  )

let test_performance () =
  test "Parser performance" (fun () ->
    (* Generate a large document *)
    let sections = 50 in
    let text = Buffer.create 10000 in
    for i = 1 to sections do
      Buffer.add_string text (Printf.sprintf "\\section{Section %d}\n" i);
      Buffer.add_string text "This is some paragraph text with \\textbf{formatting}.\n\n";
      Buffer.add_string text "\\begin{itemize}\n";
      for j = 1 to 5 do
        Buffer.add_string text (Printf.sprintf "\\item Item %d\n" j)
      done;
      Buffer.add_string text "\\end{itemize}\n\n"
    done;
    
    let tokens = tokenize_and_expand (Buffer.contents text) in
    let start = Unix.gettimeofday () in
    let doc = L2_parser.parse tokens in
    let elapsed = (Unix.gettimeofday () -. start) *. 1000. in
    
    Printf.printf "\n    Parsed %d tokens in %.2fms (%.0f tokens/ms)" 
      doc.stats.total_tokens elapsed 
      (float doc.stats.total_tokens /. elapsed);
    
    if elapsed > 10. then
      Printf.printf " ⚠️  SLOW"
  )

let test_l0_l1_l2_pipeline () =
  test "L0→L1→L2 pipeline" (fun () ->
    let text = "\\newcommand{\\hello}{Hello}\n\\hello{} world!" in
    
    (* L0: Tokenize *)
    let l0_tokens = L0_lexer_track_a_arena.tokenize text in
    
    (* L1: Expand macros *)
    let l1_state = L1_expander.initial_state () in
    let expanded = L1_expander.expand_tokens l1_state l0_tokens in
    
    (* L2: Parse to AST *)
    let doc = L2_parser.parse (Array.of_list expanded.tokens) in
    
    (* Verify the macro was expanded and parsed *)
    match doc.body with
    | [Paragraph inlines] ->
        let text_count = List.length (List.filter (function Text _ -> true | _ -> false) inlines) in
        if text_count < 5 then failwith "Macro not properly expanded"
    | _ ->
        failwith "Pipeline failed"
  )

(* Main test runner *)
let () =
  Printf.printf "🧪 L2 Parser Test Suite\n";
  Printf.printf "======================\n\n";
  
  test_simple_paragraph ();
  test_section_parsing ();
  test_environment_parsing ();
  test_math_inline ();
  test_math_display ();
  test_command_with_args ();
  test_nested_structures ();
  test_error_recovery ();
  test_performance ();
  test_l0_l1_l2_pipeline ();
  
  Printf.printf "\n✅ L2 Parser tests complete!\n"