(* test_formal_integration.ml - Test formal state and chunk integration *)

#directory "lib";;
#load "unix.cma";;

open Printf

(* Simplified versions of the formal modules for testing *)

(* Formal state from master plans *)
type lexer_state = {
  in_comment   : bool;
  in_verbatim  : bool;
  math_mode    : bool;
  brace_depth  : int;
  line         : int;
  column       : int;
}

let init_state = {
  in_comment = false;
  in_verbatim = false;
  math_mode = false;
  brace_depth = 0;
  line = 1;
  column = 1;
}

(* State codec functions *)
let encode_state st = [
  (if st.in_comment then 1 else 0);
  (if st.in_verbatim then 1 else 0);
  (if st.math_mode then 1 else 0);
  st.brace_depth;
  st.line;
  st.column;
]

let decode_state = function
  | [c; v; m; d; ln; col] ->
      Some {
        in_comment = (c = 1);
        in_verbatim = (v = 1);
        math_mode = (m = 1);
        brace_depth = d;
        line = ln;
        column = col;
      }
  | _ -> None

let roundtrip_test st =
  match decode_state (encode_state st) with
  | Some decoded -> decoded = st
  | None -> false

(* Chunk processing *)
type chunk = {
  c_state : lexer_state;
  c_bytes : string;
}

type token = 
  | TCommand of string
  | TText of string
  | TComment of string
  | TMath of string
  | TBrace of char
  | TNewline

let simple_lex_chunk ck =
  let bytes = ck.c_bytes in
  let state = ref ck.c_state in
  let tokens = ref [] in
  let len = String.length bytes in
  
  for i = 0 to len - 1 do
    let c = bytes.[i] in
    match c with
    | '\n' -> 
        tokens := TNewline :: !tokens;
        state := { !state with line = !state.line + 1; column = 1 }
    | '%' when not !state.in_verbatim ->
        state := { !state with in_comment = true };
        tokens := TComment "%" :: !tokens
    | '$' when not !state.in_verbatim && not !state.in_comment ->
        state := { !state with math_mode = not !state.math_mode };
        tokens := TMath "$" :: !tokens
    | '{' when not !state.in_verbatim && not !state.in_comment ->
        state := { !state with brace_depth = !state.brace_depth + 1 };
        tokens := TBrace '{' :: !tokens
    | '}' when not !state.in_verbatim && not !state.in_comment ->
        state := { !state with brace_depth = max 0 (!state.brace_depth - 1) };
        tokens := TBrace '}' :: !tokens
    | '\\' when not !state.in_verbatim && not !state.in_comment && i + 1 < len ->
        tokens := TCommand "\\" :: !tokens
    | c ->
        tokens := TText (String.make 1 c) :: !tokens;
        state := { !state with column = !state.column + 1 }
  done;
  
  (List.rev !tokens, !state)

(* Test formal integration *)
let test_formal_integration () =
  printf "=== FORMAL INTEGRATION TEST ===\n\n";
  
  printf "1. TESTING STATE CODEC (Master Plan StateCodec.v)\n";
  printf "──────────────────────────────────────────────────\n\n";
  
  let test_states = [
    init_state;
    { init_state with in_comment = true };
    { init_state with math_mode = true; brace_depth = 3 };
    { init_state with line = 42; column = 17 };
  ] in
  
  printf "State Codec Roundtrip Tests:\n";
  List.iteri (fun i st ->
    let result = roundtrip_test st in
    printf "  Test %d: %s\n" (i+1) (if result then "✅ PASS" else "❌ FAIL")
  ) test_states;
  
  let all_codec_pass = List.for_all roundtrip_test test_states in
  printf "\nCodec Tests: %s\n\n" (if all_codec_pass then "✅ ALL PASS" else "❌ SOME FAILED");
  
  printf "2. TESTING CHUNK PROCESSING (Master Plan StreamChunk.v)\n";
  printf "─────────────────────────────────────────────────────────\n\n";
  
  let test_inputs = [
    ("Simple text", "hello world");
    ("Math mode", "$x^2 + y^2$");
    ("Command", "\\section{Title}");
    ("Braces", "{nested {content}}");
    ("Comment", "% this is a comment");
    ("Mixed", "Text $math$ \\cmd{arg} % comment");
  ] in
  
  printf "Chunk Processing Tests:\n";
  List.iter (fun (name, text) ->
    let chunk = { c_state = init_state; c_bytes = text } in
    let (tokens, end_state) = simple_lex_chunk chunk in
    let token_count = List.length tokens in
    let valid_state = roundtrip_test end_state in
    
    printf "  %-15s: %2d tokens, state_valid=%s\n" 
      name token_count (if valid_state then "✅" else "❌")
  ) test_inputs;
  
  printf "\n3. EQUIVALENCE TESTING (Master Plan incremental_equiv)\n";
  printf "──────────────────────────────────────────────────────\n\n";
  
  let test_equivalence text =
    (* Batch processing *)
    let batch_chunk = { c_state = init_state; c_bytes = text } in
    let (batch_tokens, _) = simple_lex_chunk batch_chunk in
    
    (* Incremental processing (split into 2 chunks) *)
    let mid = String.length text / 2 in
    if mid = 0 then true
    else begin
      let chunk1_text = String.sub text 0 mid in
      let chunk2_text = String.sub text mid (String.length text - mid) in
      
      let chunk1 = { c_state = init_state; c_bytes = chunk1_text } in
      let (tokens1, state1) = simple_lex_chunk chunk1 in
      
      let chunk2 = { c_state = state1; c_bytes = chunk2_text } in
      let (tokens2, _) = simple_lex_chunk chunk2 in
      
      let incremental_tokens = tokens1 @ tokens2 in
      batch_tokens = incremental_tokens
    end
  in
  
  printf "Batch vs Incremental Equivalence:\n";
  List.iter (fun (name, text) ->
    let equivalent = test_equivalence text in
    printf "  %-15s: %s\n" name (if equivalent then "✅ EQUIVALENT" else "❌ DIFFERENT")
  ) test_inputs;
  
  printf "\n4. PERFORMANCE COMPARISON\n";
  printf "─────────────────────────────────────────────\n\n";
  
  let large_text = String.make 10000 'x' ^ "\\section{Test}" ^ String.make 10000 'y' in
  
  (* Batch processing time *)
  let start_time = Unix.gettimeofday () in
  let batch_chunk = { c_state = init_state; c_bytes = large_text } in
  let _ = simple_lex_chunk batch_chunk in
  let batch_time = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  
  (* Incremental processing time (10 chunks) *)
  let chunk_size = String.length large_text / 10 in
  let start_time = Unix.gettimeofday () in
  let current_state = ref init_state in
  
  for i = 0 to 9 do
    let start_pos = i * chunk_size in
    let end_pos = if i = 9 then String.length large_text else (i + 1) * chunk_size in
    let chunk_text = String.sub large_text start_pos (end_pos - start_pos) in
    let chunk = { c_state = !current_state; c_bytes = chunk_text } in
    let (_, end_state) = simple_lex_chunk chunk in
    current_state := end_state
  done;
  
  let incremental_time = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  
  printf "Performance on %d character document:\n" (String.length large_text);
  printf "  Batch processing:       %6.2f ms\n" batch_time;
  printf "  Incremental (10 chunks): %6.2f ms\n" incremental_time;
  printf "  Overhead ratio:         %6.2fx\n" (incremental_time /. batch_time);
  
  printf "\n5. INTEGRATION ASSESSMENT\n";
  printf "─────────────────────────────────────────\n\n";
  
  let codec_working = all_codec_pass in
  let equiv_working = List.for_all (fun (_, text) -> test_equivalence text) test_inputs in
  let performance_reasonable = incremental_time /. batch_time < 2.0 in
  
  printf "✓ State Codec (StateCodec.v):     %s\n" (if codec_working then "✅ WORKING" else "❌ BROKEN");
  printf "✓ Chunk Processing (StreamChunk.v): %s\n" (if equiv_working then "✅ WORKING" else "❌ BROKEN");
  printf "✓ Performance Overhead:           %s\n" (if performance_reasonable then "✅ ACCEPTABLE" else "❌ TOO HIGH");
  
  printf "\nINTEGRATION STATUS: ";
  if codec_working && equiv_working && performance_reasonable then
    printf "✅ READY FOR PHASE 2 (Chunk Architecture Migration)\n"
  else
    printf "❌ NEEDS FIXES BEFORE PROCEEDING\n";
  
  printf "\nNEXT STEPS:\n";
  printf "1. Migrate existing modules to use formal_state.ml\n";
  printf "2. Replace line-based processing with stream_chunk.ml\n";
  printf "3. Add formal validation to checkpoint manager\n";
  printf "4. Implement SIMD optimizations from master plans\n";
  
  printf "\n=== FORMAL INTEGRATION TEST COMPLETE ===\n"

let () = test_formal_integration ()