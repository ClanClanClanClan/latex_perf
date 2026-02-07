(* Lexer_v25 - Core Token Definitions Interface *)

open Data.Catcode

(* Core token type *)
type token =
  | TChar of Uchar.t * catcode
  | TMacro of string
  | TParam of int
  | TGroupOpen
  | TGroupClose
  | TEOF

(* Located token with position information *)
type located_token = { token : token; location : Data.Location.t }

(* Token constructors and utilities *)
val token_to_string : token -> string
val make_located_token : token -> Data.Location.t -> located_token
val token_equal : token -> token -> bool

(* Token predicates *)
val is_space_token : token -> bool
val is_letter_token : token -> bool
val is_digit_token : token -> bool
val is_math_shift : token -> bool
val is_char_token : token -> char -> bool

(* Token extractors *)
val get_char_opt : token -> Uchar.t option
val get_macro_opt : token -> string option

(* Token list utilities *)
module TokenList : sig
  val to_string : token list -> string
  val count_type : (token -> bool) -> token list -> int
  val filter : (token -> bool) -> token list -> token list
  val find_opt : (token -> bool) -> token list -> token option
  val split_on : (token -> bool) -> token list -> token list list
end

(* Type alias for compatibility *)
type t = token
