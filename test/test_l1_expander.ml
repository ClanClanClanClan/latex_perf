(* Test suite for L1 Expander *)

open Printf

let test_count = ref 0
let pass_count = ref 0

let test name f =
  incr test_count;
  try
    f ();
    incr pass_count;
    printf "✅ %s\n" name
  with e ->
    printf "❌ %s: %s\n" name (Printexc.to_string e)

(* Test basic macro expansion *)
let test_basic_expansion () =
  test "Basic macro expansion" (fun () ->
    let state = L1_expander.initial_state () in
    
    (* Define a simple macro *)
    let macro_def = {
      L1_expander.name = "foo";
      params = 0;
      replacement = [Lexer_v25.TChar (Uchar.of_char 'b', Catcode.Letter);
                     Lexer_v25.TChar (Uchar.of_char 'a', Catcode.Letter);
                     Lexer_v25.TChar (Uchar.of_char 'r', Catcode.Letter)];
      is_long = false;
      is_outer = false;
    } in
    let state = L1_expander.define_macro state "foo" macro_def in
    
    (* Expand macro *)
    let tokens = [Lexer_v25.TMacro "foo"] in
    let result = L1_expander.expand_tokens state tokens in
    
    assert (List.length result.tokens = 3);
    assert (result.stats.expansions_performed = 1);
  )

(* Test macro with parameters *)
let test_parameterized_macro () =
  test "Parameterized macro" (fun () ->
    let state = L1_expander.initial_state () in
    
    (* Define macro with 2 parameters *)
    let macro_def = {
      L1_expander.name = "swap";
      params = 2;
      replacement = [Lexer_v25.TParam 2; 
                     Lexer_v25.TChar (Uchar.of_char ' ', Catcode.Space);
                     Lexer_v25.TParam 1];
      is_long = false;
      is_outer = false;
    } in
    let state = L1_expander.define_macro state "swap" macro_def in
    
    (* Test: \swap{A}{B} should expand to "B A" *)
    let tokens = [
      Lexer_v25.TMacro "swap";
      Lexer_v25.TGroupOpen;
      Lexer_v25.TChar (Uchar.of_char 'A', Catcode.Letter);
      Lexer_v25.TGroupClose;
      Lexer_v25.TGroupOpen;
      Lexer_v25.TChar (Uchar.of_char 'B', Catcode.Letter);
      Lexer_v25.TGroupClose;
    ] in
    
    let result = L1_expander.expand_tokens state tokens in
    
    (* Should get: B <space> A *)
    assert (List.length result.tokens = 3);
    match result.tokens with
    | [t1; t2; t3] ->
        assert (t1 = Lexer_v25.TChar (Uchar.of_char 'B', Catcode.Letter));
        assert (t2 = Lexer_v25.TChar (Uchar.of_char ' ', Catcode.Space));
        assert (t3 = Lexer_v25.TChar (Uchar.of_char 'A', Catcode.Letter));
    | _ -> failwith "Unexpected expansion result"
  )

(* Test nested macro expansion *)
let test_nested_expansion () =
  test "Nested macro expansion" (fun () ->
    let state = L1_expander.initial_state () in
    
    (* Define two macros *)
    let state = L1_expander.define_macro state "foo" {
      L1_expander.name = "foo";
      params = 0;
      replacement = [Lexer_v25.TMacro "bar"];
      is_long = false;
      is_outer = false;
    } in
    
    let state = L1_expander.define_macro state "bar" {
      L1_expander.name = "bar";
      params = 0;
      replacement = [Lexer_v25.TChar (Uchar.of_char 'X', Catcode.Letter)];
      is_long = false;
      is_outer = false;
    } in
    
    (* \foo should expand to \bar, which expands to X *)
    let tokens = [Lexer_v25.TMacro "foo"] in
    let result = L1_expander.expand_tokens state tokens in
    
    assert (List.length result.tokens = 1);
    assert (result.stats.expansions_performed = 2);
    assert (result.stats.max_depth_reached = 1);
  )

(* Test environment tracking *)
let test_environments () =
  test "Environment tracking" (fun () ->
    let state = L1_expander.initial_state () in
    
    (* Begin environment *)
    let state = L1_expander.begin_environment state "document" in
    assert (L1_expander.in_environment state "document");
    
    (* Begin nested environment *)
    let state = L1_expander.begin_environment state "itemize" in
    assert (L1_expander.in_environment state "itemize");
    assert (L1_expander.in_environment state "document");
    
    (* End inner environment *)
    let state = L1_expander.end_environment state "itemize" in
    assert (not (L1_expander.in_environment state "itemize"));
    assert (L1_expander.in_environment state "document");
    
    (* End outer environment *)
    let state = L1_expander.end_environment state "document" in
    assert (not (L1_expander.in_environment state "document"));
  )

(* Test counter management *)
let test_counters () =
  test "Counter management" (fun () ->
    let state = L1_expander.initial_state () in
    
    (* Create counter *)
    let state = L1_expander.new_counter state "section" in
    assert (L1_expander.get_counter state "section" = Some 0);
    
    (* Step counter *)
    let state = L1_expander.step_counter state "section" in
    assert (L1_expander.get_counter state "section" = Some 1);
    
    (* Set counter *)
    let state = L1_expander.set_counter state "section" 42 in
    assert (L1_expander.get_counter state "section" = Some 42);
  )

(* Test performance *)
let test_performance () =
  test "Expansion performance" (fun () ->
    let state = L1_expander.initial_state () in
    
    (* Define a macro that expands to 100 tokens *)
    let replacement = List.init 100 (fun i ->
      Lexer_v25.TChar (Uchar.of_char 'a', Catcode.Letter)
    ) in
    
    let state = L1_expander.define_macro state "big" {
      L1_expander.name = "big";
      params = 0;
      replacement;
      is_long = false;
      is_outer = false;
    } in
    
    (* Create input with 100 macro calls *)
    let tokens = List.init 100 (fun _ -> Lexer_v25.TMacro "big") in
    
    let result = L1_expander.expand_tokens state tokens in
    
    (* Should expand to 10,000 tokens *)
    assert (List.length result.tokens = 10000);
    assert (result.stats.expansions_performed = 100);
    
    (* Performance check - should be fast *)
    assert (result.stats.time_ms < 10.0);
    printf "  Expansion time: %.2fms for 100 macros -> 10,000 tokens\n" 
      result.stats.time_ms;
  )

(* Test L0 integration *)
let test_l0_integration () =
  test "L0→L1 integration" (fun () ->
    (* First, lex some input with L0 *)
    let input = "\\newcommand{\\hello}{Hello, world!}" in
    let tokens = L0_lexer_track_a_arena.tokenize input in
    
    (* Expand with L1 *)
    let state = L1_expander.initial_state () in
    let state = L1_expander.register_primitives state in
    let result = L1_expander.expand_tokens state tokens in
    
    (* Just verify it doesn't crash for now *)
    assert (List.length result.tokens > 0);
  )

(* Run all tests *)
let () =
  printf "🧪 L1 Expander Test Suite\n";
  printf "========================\n\n";
  
  test_basic_expansion ();
  test_parameterized_macro ();
  test_nested_expansion ();
  test_environments ();
  test_counters ();
  test_performance ();
  test_l0_integration ();
  
  printf "\n📊 Results: %d/%d tests passed\n" !pass_count !test_count;
  
  if !pass_count = !test_count then
    printf "✅ All tests passed!\n"
  else
    printf "❌ Some tests failed\n"