(** Simple debug to check tokenization and parsing *)

let test_simple () =
  Printf.printf "=== Testing 'Hello world!' ===\n";
  
  (* Step 1: L0 tokenization *)
  Printf.printf "\n1. L0 TOKENIZATION:\n";
  let tokens = L0_lexer_track_a_arena.tokenize "Hello world!" in
  Printf.printf "Produced %d tokens:\n" (List.length tokens);
  List.iteri (fun i token ->
    Printf.printf "  [%d] %s\n" i (Lexer_v25.token_to_string token)
  ) tokens;
  
  (* Step 2: L1 expansion *)
  Printf.printf "\n2. L1 EXPANSION:\n";
  let l1_state = L1_expander.initial_state () in
  let expanded = L1_expander.expand_tokens l1_state tokens in
  Printf.printf "Produced %d expanded tokens:\n" (List.length expanded.tokens);
  List.iteri (fun i token ->
    Printf.printf "  [%d] %s\n" i (Lexer_v25.token_to_string token)
  ) expanded.tokens;
  
  (* Step 3: L2 parsing *)
  Printf.printf "\n3. L2 PARSING:\n";
  let token_array = Array.of_list expanded.tokens in
  Printf.printf "Parsing array of %d tokens...\n" (Array.length token_array);
  
  try
    let doc = L2_parser.parse token_array in
    Printf.printf "SUCCESS: Parsed document\n";
    Printf.printf "  preamble: %d items\n" (List.length doc.preamble);
    Printf.printf "  body: %d items\n" (List.length doc.body);
    
    match doc.body with
    | [L2_parser.Paragraph inlines] ->
        Printf.printf "  Found paragraph with %d inlines:\n" (List.length inlines);
        List.iteri (fun i inline ->
          match inline with
          | L2_parser.Text s -> Printf.printf "    [%d] Text \"%s\"\n" i s
          | L2_parser.Space -> Printf.printf "    [%d] Space\n" i
          | _ -> Printf.printf "    [%d] Other inline\n" i
        ) inlines
    | _ ->
        Printf.printf "  Document structure not a single paragraph\n"
  with e ->
    Printf.printf "ERROR: %s\n" (Printexc.to_string e)

let () = test_simple ()