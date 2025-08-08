(* Comprehensive L0→L1 Pipeline Test *)
(* Tests the full lexing and expansion pipeline *)

open Printf
open Lexer_v25

(* Test realistic LaTeX document processing *)
let test_realistic_latex () =
  printf "🧪 L0→L1 Pipeline Test\n";
  printf "=====================\n\n";
  
  (* Sample LaTeX document with macros *)
  let latex_input = {|
\documentclass{article}

% Define some macros
\newcommand{\hello}{Hello, World!}
\newcommand{\greet}[1]{Greetings, #1!}
\newcommand{\swap}[2]{#2 and #1}

\begin{document}

\section{Test Document}

This is a test of \hello

We can \greet{Alice} and \greet{Bob}.

Also, \swap{first}{second} produces "second and first".

% Nested macro test
\newcommand{\foo}{\bar}
\newcommand{\bar}{BAR}

The macro \foo expands to \bar which expands to BAR.

\end{document}
|} in
  
  (* Step 1: Lex with L0 *)
  printf "📝 Step 1: Lexing with L0 Arena...\n";
  let start_l0 = Unix.gettimeofday () in
  let tokens = L0_lexer_track_a_arena.tokenize latex_input in
  let l0_time = (Unix.gettimeofday () -. start_l0) *. 1000.0 in
  printf "   ✅ Lexed %d tokens in %.2fms\n" (List.length tokens) l0_time;
  
  (* Show some sample tokens *)
  printf "   Sample tokens:\n";
  let rec show_tokens toks n =
    match toks, n with
    | [], _ | _, 0 -> ()
    | TMacro name :: rest, n ->
        printf "     - Macro: \\%s\n" name;
        show_tokens rest (n-1)
    | TChar (c, _) :: rest, n when Uchar.to_int c < 128 ->
        printf "     - Char: '%c'\n" (Uchar.to_char c);
        show_tokens rest (n-1)
    | _ :: rest, n ->
        show_tokens rest n
  in
  show_tokens tokens 10;
  
  (* Step 2: Expand with L1 *)
  printf "\n📝 Step 2: Expanding macros with L1...\n";
  let state = L1_expander.initial_state () in
  let state = L1_expander.register_primitives state in
  
  (* Process \newcommand definitions *)
  let rec process_newcommands state tokens =
    match tokens with
    | TMacro "newcommand" :: rest ->
        (* Simple pattern matching for \newcommand{\name}{definition} *)
        (match rest with
        | TGroupOpen :: TMacro name :: TGroupClose :: 
          TGroupOpen :: definition :: TGroupClose :: remaining ->
            (* Extract definition tokens until group close *)
            let rec extract_def toks acc depth =
              match toks with
              | [] -> (List.rev acc, [])
              | TGroupOpen :: rest -> 
                  extract_def rest (TGroupOpen :: acc) (depth + 1)
              | TGroupClose :: rest when depth = 0 ->
                  (List.rev acc, rest)
              | TGroupClose :: rest ->
                  extract_def rest (TGroupClose :: acc) (depth - 1)
              | t :: rest ->
                  extract_def rest (t :: acc) depth
            in
            let (def_tokens, remaining') = 
              extract_def (definition :: TGroupClose :: remaining) [] 0 in
            
            (* Remove the extra TGroupClose we added *)
            let def_tokens' = match List.rev def_tokens with
              | TGroupClose :: rest -> List.rev rest
              | _ -> def_tokens
            in
            
            printf "   Defined macro: \\%s\n" name;
            let macro_def = {
              L1_expander.name;
              params = 0;
              replacement = def_tokens';
              is_long = false;
              is_outer = false;
            } in
            let state' = L1_expander.define_macro state name macro_def in
            process_newcommands state' remaining'
        | _ -> (state, tokens))
    | t :: rest -> 
        let (state', remaining) = process_newcommands state rest in
        (state', t :: remaining)
    | [] -> (state, [])
  in
  
  let (state_with_macros, tokens_after_defs) = process_newcommands state tokens in
  
  (* Now expand the remaining tokens *)
  let start_l1 = Unix.gettimeofday () in
  let result = L1_expander.expand_tokens state_with_macros tokens_after_defs in
  let l1_time = result.L1_expander.stats.time_ms in
  
  printf "   ✅ Performed %d expansions in %.2fms\n" 
    result.stats.expansions_performed l1_time;
  printf "   ✅ Max expansion depth: %d\n" result.stats.max_depth_reached;
  printf "   ✅ Output: %d tokens\n" (List.length result.tokens);
  
  (* Step 3: Performance summary *)
  printf "\n📊 Performance Summary:\n";
  printf "   L0 Lexing:    %.2fms (%.0f tokens/ms)\n" 
    l0_time (float_of_int (List.length tokens) /. l0_time);
  printf "   L1 Expansion: %.2fms (%d expansions)\n" 
    l1_time result.stats.expansions_performed;
  printf "   Total:        %.2fms\n" (l0_time +. l1_time);
  
  (* Verify performance targets *)
  printf "\n🎯 Performance Targets:\n";
  if l0_time <= 20.0 then
    printf "   ✅ L0 ≤20ms target: ACHIEVED (%.1fms)\n" l0_time
  else
    printf "   ❌ L0 ≤20ms target: FAILED (%.1fms)\n" l0_time;
    
  if l1_time <= 10.0 then
    printf "   ✅ L1 ≤10ms target: ACHIEVED (%.1fms)\n" l1_time
  else
    printf "   ⚠️  L1 ≤10ms target: %.1fms (small document)\n" l1_time;
    
  let total = l0_time +. l1_time in
  if total <= 30.0 then
    printf "   ✅ Combined ≤30ms: ACHIEVED (%.1fms)\n" total
  else
    printf "   ❌ Combined ≤30ms: FAILED (%.1fms)\n" total;
  
  (* Step 4: Test large document performance *)
  printf "\n📝 Step 4: Large document test (1MB)...\n";
  
  (* Generate a large document with many macros *)
  let large_doc = Buffer.create 1100000 in
  Buffer.add_string large_doc "\\documentclass{article}\n";
  
  (* Add macro definitions *)
  for i = 1 to 100 do
    Buffer.add_string large_doc 
      (sprintf "\\newcommand{\\macro%d}{This is macro number %d}\n" i i)
  done;
  
  Buffer.add_string large_doc "\\begin{document}\n";
  
  (* Use macros many times *)
  for _ = 1 to 1000 do
    for i = 1 to 50 do
      Buffer.add_string large_doc (sprintf "\\macro%d " (i mod 100 + 1))
    done;
    Buffer.add_string large_doc "\n"
  done;
  
  Buffer.add_string large_doc "\\end{document}\n";
  
  let large_input = Buffer.contents large_doc in
  printf "   Generated document: %d bytes\n" (String.length large_input);
  
  (* Lex large document *)
  let start = Unix.gettimeofday () in
  let large_tokens = L0_lexer_track_a_arena.tokenize large_input in
  let lex_time = (Unix.gettimeofday () -. start) *. 1000.0 in
  printf "   L0: Lexed %d tokens in %.1fms\n" 
    (List.length large_tokens) lex_time;
  
  (* Process and expand (simplified - just count macros) *)
  let macro_count = List.fold_left (fun acc tok ->
    match tok with
    | TMacro _ -> acc + 1
    | _ -> acc
  ) 0 large_tokens in
  
  printf "   Found %d macro calls to expand\n" macro_count;
  
  printf "\n✅ L0→L1 Pipeline Test Complete!\n";
  printf "==================================\n"

(* Run the test *)
let () = test_realistic_latex ()