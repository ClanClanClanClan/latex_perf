open Printf

let test_empty_input () =
  printf "Testing empty input:\n";
  let tokens = Lexer_v25.lex_string "" in
  let count = List.length tokens in
  printf "  Empty string -> %d tokens\n" count;
  match tokens with
  | [{ Lexer_v25.token = TEOF; _ }] -> printf "  ✓ Only TEOF token\n"
  | _ -> printf "  ❌ Expected only TEOF\n"

let test_single_char () =
  printf "\nTesting single characters:\n";
  let test_char c expected =
    let tokens = Lexer_v25.lex_string (String.make 1 c) in
    match tokens with
    | [{ Lexer_v25.token = TChar (_, _); _ }; { Lexer_v25.token = TEOF; _ }] -> 
        printf "  '%c' -> TChar + TEOF ✓\n" c
    | _ -> printf "  '%c' -> unexpected tokens ❌\n" c
  in
  test_char 'a' "Letter";
  test_char '1' "Other";
  test_char ' ' "Space"

let test_macro_edge_cases () =
  printf "\nTesting macro edge cases:\n";
  (* Single backslash *)
  let tokens1 = Lexer_v25.lex_string "\\" in
  printf "  Single backslash: %d tokens\n" (List.length tokens1);
  
  (* Backslash followed by non-letter *)
  let tokens2 = Lexer_v25.lex_string "\\1" in
  printf "  \\1: %d tokens\n" (List.length tokens2);
  
  (* Very long macro name *)
  let long_macro = "\\" ^ String.make 100 'a' in
  let tokens3 = Lexer_v25.lex_string long_macro in
  printf "  Long macro (100 chars): %d tokens\n" (List.length tokens3)

let test_parameter_edge_cases () =
  printf "\nTesting parameter edge cases:\n";
  let test_param input expected_count =
    let tokens = Lexer_v25.lex_string input in
    let param_count = List.fold_left (fun acc tok ->
      match tok.Lexer_v25.token with
      | Lexer_v25.TParam _ -> acc + 1
      | _ -> acc
    ) 0 tokens in
    printf "  '%s' -> %d params (expected %d) %s\n" 
      input param_count expected_count 
      (if param_count = expected_count then "✓" else "❌")
  in
  test_param "#1" 1;
  test_param "#9" 1;
  test_param "#0" 0;  (* Should be TChar *)
  test_param "##" 0;  (* Should be TChar tokens *)
  test_param "#a" 0   (* Should be TChar tokens *)

let () =
  test_empty_input ();
  test_single_char ();
  test_macro_edge_cases ();
  test_parameter_edge_cases ();
  printf "\n✅ Edge case testing complete\n"