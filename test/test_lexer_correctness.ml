(* Comprehensive correctness test for L0 lexers *)

open Data

let test_cases = [
  (* Basic text *)
  ("Hello world", 11);
  
  (* Commands *)
  ("\\command", 1);
  ("\\cmd{arg}", 6);  (* \cmd + { + arg + } *)
  
  (* Math *)
  ("$x^2$", 5);  (* $ + x + ^ + 2 + $ *)
  
  (* Comments *)
  ("text % comment\nmore", 10);  (* text + space + % skips to \n + more *)
  
  (* Groups *)
  ("{a}{b}", 6);  (* { + a + } + { + b + } *)
  
  (* Parameters *)
  ("#1 #2", 4);  (* #1 + space + #2 *)
  ("#9#0", 3);   (* #9 + # + 0 (not param) *)
  
  (* Special chars *)
  ("a&b_c^d", 7);
  
  (* Edge cases *)
  ("", 0);
  ("\\", 0);  (* Backslash at EOF *)
  ("%", 0);  (* Comment at EOF *)
  ("#", 1);  (* Hash at EOF *)
  ("\\cmd", 1); (* Command at EOF *)
]

let token_to_string = function
  | Lexer_v25.TChar (u, cat) -> 
    Printf.sprintf "TChar('%s', %d)" 
      (try String.make 1 (Char.chr (Uchar.to_int u)) with _ -> "?")
      (Obj.magic cat : int)
  | Lexer_v25.TMacro s -> Printf.sprintf "TMacro(%s)" s
  | Lexer_v25.TParam n -> Printf.sprintf "TParam(%d)" n
  | Lexer_v25.TGroupOpen -> "TGroupOpen"
  | Lexer_v25.TGroupClose -> "TGroupClose"
  | Lexer_v25.TEOF -> "TEOF"

let test_lexer name lexer_func =
  Printf.printf "\n=== Testing %s ===\n" name;
  
  let all_pass = ref true in
  List.iter (fun (input, expected) ->
    try
      let tokens = lexer_func input in
      let count = List.length tokens in
      
      if count = expected then
        Printf.printf "✅ %S -> %d tokens\n" input count
      else (
        Printf.printf "❌ %S -> %d tokens (expected %d)\n" input count expected;
        all_pass := false;
        (* Show tokens for debugging *)
        if String.length input < 20 then (
          Printf.printf "   Tokens: ";
          List.iter (fun tok -> Printf.printf "%s " (token_to_string tok)) tokens;
          Printf.printf "\n"
        )
      )
    with e ->
      Printf.printf "💥 %S -> ERROR: %s\n" input (Printexc.to_string e);
      all_pass := false
  ) test_cases;
  
  !all_pass

let compare_lexers lexer1 name1 lexer2 name2 =
  Printf.printf "\n=== Comparing %s vs %s ===\n" name1 name2;
  
  let test_input = "\\documentclass{article}\n\\begin{document}\nHello $x^2$ % comment\n#1 test\n\\end{document}" in
  
  let tokens1 = lexer1 test_input in
  let tokens2 = lexer2 test_input in
  
  Printf.printf "%s: %d tokens\n" name1 (List.length tokens1);
  Printf.printf "%s: %d tokens\n" name2 (List.length tokens2);
  
  if List.length tokens1 = List.length tokens2 then (
    Printf.printf "✅ Token counts match\n";
    
    (* Check if tokens are identical *)
    let mismatch = ref false in
    List.iter2 (fun t1 t2 ->
      if t1 <> t2 && not !mismatch then (
        Printf.printf "❌ First mismatch: %s vs %s\n" 
          (token_to_string t1) (token_to_string t2);
        mismatch := true
      )
    ) tokens1 tokens2;
    
    if not !mismatch then
      Printf.printf "✅ All tokens identical\n"
  ) else
    Printf.printf "❌ Token count mismatch\n"

let () =
  Printf.printf "L0 Lexer Correctness Test Suite\n";
  Printf.printf "================================\n";
  
  (* Test individual lexers *)
  let baseline_ok = test_lexer "L0_lexer (baseline)" L0_lexer.tokenize in
  let simple_ok = test_lexer "L0_lexer_track_a_simple" L0_lexer_track_a_simple.tokenize in
  let final_ok = test_lexer "L0_lexer_track_a_final" L0_lexer_track_a_final.tokenize in
  
  (* Compare implementations *)
  compare_lexers L0_lexer.tokenize "baseline" L0_lexer_track_a_final.tokenize "final";
  
  (* Summary *)
  Printf.printf "\n=== SUMMARY ===\n";
  Printf.printf "Baseline: %s\n" (if baseline_ok then "✅ PASS" else "❌ FAIL");
  Printf.printf "Simple: %s\n" (if simple_ok then "✅ PASS" else "❌ FAIL");
  Printf.printf "Final: %s\n" (if final_ok then "✅ PASS" else "❌ FAIL");
  
  (* Performance test on 1MB *)
  Printf.printf "\n=== Quick Performance Test ===\n";
  match L0_lexer_correctness_utils.load_file "corpora/perf/perf_smoke_big.tex" with
  | None -> Printf.printf "Could not load performance test file\n"
  | Some content ->
    Printf.printf "Testing on %.2f MB file...\n" 
      (float_of_int (String.length content) /. 1_048_576.0);
    
    let time_it name f =
      let start = Unix.gettimeofday () in
      let tokens = f content in
      let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
      Printf.printf "%s: %.2f ms (%d tokens)\n" name elapsed (List.length tokens);
      tokens
    in
    
    let t1 = time_it "Baseline" L0_lexer.tokenize in
    let t2 = time_it "Final" L0_lexer_track_a_final.tokenize in
    
    if List.length t1 = List.length t2 then
      Printf.printf "✅ Token counts match on large file\n"
    else
      Printf.printf "❌ Token mismatch: %d vs %d\n" (List.length t1) (List.length t2)

(* Utility module *)
module L0_lexer_correctness_utils = struct
  let load_file filename =
    try
      let ic = open_in filename in
      let content = really_input_string ic (in_channel_length ic) in
      close_in ic;
      Some content
    with _ -> None
end