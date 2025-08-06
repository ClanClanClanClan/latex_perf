open Core

(* Utility functions for debugging - prefixed with _ to indicate intentionally unused *)
let rec _take n lst = match n, lst with
  | 0, _ | _, [] -> []
  | n, x::xs -> x :: _take (n-1) xs

let _load_file filename =
  let ic = open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  content

let test_correct_behavior () =
  let tests = [
    ("simple_group", "{hello}");
    ("documentclass", "\\documentclass{article}");
    ("nested", "\\begin{document} text \\end{document}");
    ("math", "$x = y + z$");
  ] in
  
  Printf.printf "=== Testing CORRECT LaTeX Tokenization ===\n";
  
  List.iter (fun (name, input) ->
    Printf.printf "\n--- %s: %S ---\n" name input;
    
    let baseline_tokens = Core.Lexer_optimized_v25.tokenize_to_list input in
    let correct_tokens = Core.L0_lexer_track_a_simple.tokenize input in
    
    Printf.printf "Broken baseline: ";
    List.iter (fun tok ->
      Printf.printf "%s " (match tok with
      | Lexer_v25.TChar (u, _) -> Printf.sprintf "TChar('%c')" (try Uchar.to_char u with _ -> '?')
      | Lexer_v25.TMacro s -> Printf.sprintf "TMacro(%s)" s
      | Lexer_v25.TGroupOpen -> "{"
      | Lexer_v25.TGroupClose -> "}"
      | Lexer_v25.TParam _ -> "TParam"
      | Lexer_v25.TEOF -> "EOF")
    ) baseline_tokens;
    Printf.printf "\n";
    
    Printf.printf "Correct output:  ";
    List.iter (fun tok ->
      Printf.printf "%s " (match tok with
      | Lexer_v25.TChar (u, _) -> Printf.sprintf "TChar('%c')" (try Uchar.to_char u with _ -> '?')
      | Lexer_v25.TMacro s -> Printf.sprintf "TMacro(%s)" s
      | Lexer_v25.TGroupOpen -> "{"
      | Lexer_v25.TGroupClose -> "}"
      | Lexer_v25.TParam _ -> "TParam"
      | Lexer_v25.TEOF -> "EOF")
    ) correct_tokens;
    Printf.printf "\n";
    
    Printf.printf "Analysis: %s\n" (
      if baseline_tokens = correct_tokens then "Same (baseline might be correct here)"
      else "Different (baseline appears broken)"
    )
  ) tests
    


let () = test_correct_behavior ()