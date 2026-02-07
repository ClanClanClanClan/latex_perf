(* Lexer_v25 - Core Token Definitions for LaTeX Perfectionist v25 *)
(* This is the MISSING MODULE that L1 and L2 depend on *)

(* Import core data types *)
type token = Data.Types.token
type located_token = Data.Types.located_token

(* Token to string for debugging *)
let token_to_string = function
  | Data.Types.TChar (uc, cat) ->
      Printf.sprintf "TChar(%C,%s)" (Uchar.to_char uc)
        (Data.Types.Catcode.catcode_to_string cat)
  | Data.Types.TMacro name -> Printf.sprintf "TMacro(%s)" name
  | Data.Types.TParam n -> Printf.sprintf "TParam(%d)" n
  | Data.Types.TGroupOpen -> "TGroupOpen"
  | Data.Types.TGroupClose -> "TGroupClose"
  | Data.Types.TEOF -> "TEOF"

(* Create a located token *)
let make_located_token token location = { token; location }

(* Token equality *)
let token_equal t1 t2 =
  match (t1, t2) with
  | TChar (u1, c1), TChar (u2, c2) -> Uchar.equal u1 u2 && catcode_eq c1 c2
  | TMacro s1, TMacro s2 -> String.equal s1 s2
  | TParam n1, TParam n2 -> n1 = n2
  | TGroupOpen, TGroupOpen -> true
  | TGroupClose, TGroupClose -> true
  | TEOF, TEOF -> true
  | _ -> false

(* Check if token is a space *)
let is_space_token = function
  | TChar (_, Space) -> true
  | TChar (uc, EndLine) when Uchar.to_int uc = 10 || Uchar.to_int uc = 13 ->
      true
  | _ -> false

(* Check if token is a letter *)
let is_letter_token = function TChar (_, Letter) -> true | _ -> false

(* Check if token is a digit *)
let is_digit_token = function
  | TChar (uc, Other) ->
      let code = Uchar.to_int uc in
      code >= 48 && code <= 57 (* '0' to '9' *)
  | _ -> false

(* Check if token is math shift *)
let is_math_shift = function TChar (_, MathShift) -> true | _ -> false

(* Extract character from token *)
let get_char_opt = function TChar (uc, _) -> Some uc | _ -> None

(* Extract macro name from token *)
let get_macro_opt = function TMacro name -> Some name | _ -> None

(* Check if token is a specific character *)
let is_char_token tok ch =
  match tok with TChar (uc, _) -> Uchar.to_int uc = Char.code ch | _ -> false

(* Token list utilities *)
module TokenList = struct
  (* Convert token list to string (for debugging) *)
  let to_string tokens = String.concat " " (List.map token_to_string tokens)

  (* Count tokens of specific type *)
  let count_type pred tokens =
    List.fold_left (fun acc tok -> if pred tok then acc + 1 else acc) 0 tokens

  (* Filter tokens by predicate *)
  let filter pred tokens = List.filter pred tokens

  (* Find first token matching predicate *)
  let find_opt pred tokens = List.find_opt pred tokens

  (* Split on delimiter token *)
  let split_on delim_pred tokens =
    let rec split acc current = function
      | [] -> List.rev (List.rev current :: acc)
      | tok :: rest ->
          if delim_pred tok then split (List.rev current :: acc) [] rest
          else split acc (tok :: current) rest
    in
    split [] [] tokens
end

(* Export key types and functions *)
type t = token
