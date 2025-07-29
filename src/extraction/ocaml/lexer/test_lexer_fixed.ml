(** Test suite for the extracted LaTeX lexer *)

open Latex_tokenize

(* Convert extracted string to OCaml string *)
let rec string_to_ocaml s =
  match s with
  | EmptyString -> ""
  | String (c, rest) -> 
      let c_str = String.make 1 (Char.chr (nat_to_int (nat_of_ascii c))) in
      c_str ^ (string_to_ocaml rest)

and nat_to_int n =
  match n with
  | O -> 0
  | S n' -> 1 + nat_to_int n'

(* Convert OCaml string to extracted string *)
let string_of_ocaml s =
  let rec aux i =
    if i >= String.length s then EmptyString
    else String (ascii_of_nat (Char.code s.[i]), aux (i + 1))
  in aux 0

(* Helper to convert token to string for display *)
let token_to_string = function
  | TText s -> Printf.sprintf "TText(%S)" (string_to_ocaml s)
  | TCommand s -> Printf.sprintf "TCommand(%S)" (string_to_ocaml s)
  | TMathShift -> "TMathShift"
  | TBeginGroup -> "TBeginGroup"
  | TEndGroup -> "TEndGroup"
  | TParameter n -> Printf.sprintf "TParameter(%d)" (nat_to_int n)
  | TSpace -> "TSpace"
  | TNewline -> "TNewline"
  | TVerbatim s -> Printf.sprintf "TVerbatim(%S)" (string_to_ocaml s)

(* Print token list *)
let print_tokens tokens =
  List.iter (fun t -> Printf.printf "  %s\n" (token_to_string t)) tokens

(* Simple test *)
let test_simple () =
  Printf.printf "Testing simple tokenization...\n\n";
  
  let test_cases = [
    "Hello world";
    "$x + y$";
    "\\section{Title}";
    "The equation $E = mc^2$ is famous.";
  ] in
  
  List.iter (fun input ->
    Printf.printf "Input: %S\n" input;
    Printf.printf "Tokens:\n";
    let tokens = latex_tokenize (string_of_ocaml input) in
    print_tokens tokens;
    Printf.printf "\n"
  ) test_cases

(* Check specific tokenization that was causing false positives *)
let test_false_positive_case () =
  Printf.printf "Testing false positive case...\n";
  let input = "By examining arithmetic operations between numbers expressed in base $m\\ge 2$, we uncover new families." in
  Printf.printf "Input: %S\n" input;
  
  let tokens = latex_tokenize (string_of_ocaml input) in
  Printf.printf "Number of tokens: %d\n" (List.length tokens);
  Printf.printf "Tokens:\n";
  print_tokens tokens;
  
  (* Check if we have TMathShift tokens *)
  let math_shifts = List.filter (fun t -> match t with TMathShift -> true | _ -> false) tokens in
  Printf.printf "\nMath shift tokens found: %d\n" (List.length math_shifts);
  
  (* Check if dollar signs are in text tokens *)
  let has_dollar_in_text = List.exists (fun t ->
    match t with
    | TText s -> String.contains (string_to_ocaml s) '$'
    | _ -> false
  ) tokens in
  
  Printf.printf "Dollar signs in text tokens: %b (should be false)\n" has_dollar_in_text;
  Printf.printf "\n"

(* Main *)
let () =
  test_simple ();
  test_false_positive_case ()