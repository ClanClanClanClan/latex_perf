open Printf

(* Test L2 parser with manually created correct tokens *)

let test_display_math_parsing () =
  printf "=== L2 PARSER TEST WITH CORRECT TOKENS ===\n";
  
  (* Manually create the correct token sequence for \[x^2\] *)
  let tokens = [
    L2_parser.TMacro "[";      (* Display math begin *)
    L2_parser.TChar ('x', Other);
    L2_parser.TChar ('^', Superscript);
    L2_parser.TChar ('2', Other);
    L2_parser.TMacro "]";      (* Display math end *)
  ] in
  
  printf "Manual tokens:\n";
  tokens |> List.iteri (fun i tok ->
    match tok with
    | L2_parser.TMacro name -> printf "  [%d] TMacro(\"%s\")\n" i name
    | L2_parser.TChar (c, cat) -> 
        printf "  [%d] TChar('%c', %s)\n" i c 
          (match cat with
           | Space -> "Space" | EndLine -> "EndLine" | MathShift -> "MathShift"
           | Superscript -> "Superscript" | Letter -> "Letter" | Other -> "Other"
           | _ -> "?")
    | _ -> printf "  [%d] Other token\n" i
  );
  
  printf "\nParsing with L2...\n";
  
  try
    let ast = L2_parser.parse_tokens tokens in
    printf "Parse result:\n";
    match ast with
    | [L2_parser.MathDisplay content] ->
        printf "✅ SUCCESS: Parsed as MathDisplay with %d elements\n" (List.length content);
        printf "Content: %s\n" (L2_parser.ast_to_string ast)
    | _ ->
        printf "❌ UNEXPECTED: Got different AST structure\n";
        printf "AST: %s\n" (L2_parser.ast_to_string ast)
  with e ->
    printf "❌ ERROR: %s\n" (Printexc.to_string e)

let test_inline_math_parsing () =
  printf "\n=== INLINE MATH TEST ===\n";
  
  (* Test inline math $x^2$ *)
  let tokens = [
    L2_parser.TChar ('$', MathShift);
    L2_parser.TChar ('x', Letter);
    L2_parser.TChar ('^', Superscript);
    L2_parser.TChar ('2', Other);
    L2_parser.TChar ('$', MathShift);
  ] in
  
  try
    let ast = L2_parser.parse_tokens tokens in
    match ast with
    | [L2_parser.MathInline _] ->
        printf "✅ SUCCESS: Inline math parsed correctly\n"
    | _ ->
        printf "Parsed as: %s\n" (L2_parser.ast_to_string ast)
  with e ->
    printf "ERROR: %s\n" (Printexc.to_string e)

let test_complete_pipeline () =
  printf "\n=== IDEAL L0→L2 PIPELINE TEST ===\n";
  
  (* What the pipeline SHOULD produce *)
  printf "If L0 produced correct tokens for '\\[E=mc^2\\]', L2 would parse:\n";
  
  let correct_tokens = [
    L2_parser.TMacro "[";
    L2_parser.TChar ('E', Letter);
    L2_parser.TChar ('=', Other);
    L2_parser.TChar ('m', Letter);
    L2_parser.TChar ('c', Letter);
    L2_parser.TChar ('^', Superscript);
    L2_parser.TChar ('2', Other);
    L2_parser.TMacro "]";
  ] in
  
  try
    let ast = L2_parser.parse_tokens correct_tokens in
    match ast with
    | [L2_parser.MathDisplay _] ->
        printf "✅ L2 parser works perfectly when given correct tokens!\n";
        printf "AST: %s\n" (L2_parser.ast_to_string ast)
    | _ ->
        printf "Unexpected result\n"
  with e ->
    printf "Error: %s\n" (Printexc.to_string e)

let () =
  test_display_math_parsing ();
  test_inline_math_parsing ();
  test_complete_pipeline ()