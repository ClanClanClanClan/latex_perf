(* Lexer Types Module - Week 3-6 Deliverable - v25 COMPLIANT *)
(* LaTeX Perfectionist v25 - Core types and utilities only *)
(* LEXING IMPLEMENTATION REMOVED: Use lexer_optimized_v25 for production *)

open Data

(** Token type - EXACT v25 specification *)
type token =
  | TChar      of Uchar.t * Catcode.catcode  (* Character with its catcode *)
  | TMacro     of string                    (* Macro name without backslash *)
  | TParam     of int                       (* Parameter #1 .. #9 *)
  | TGroupOpen                              (* Begin group { *)
  | TGroupClose                             (* End group } *)
  | TEOF                                    (* End of file *)
(* 6 constructors total as per v25 specification *)

(** Lexer state for FSM - v25 specification *)
type lexer_state = 
  | S0_Normal    (* Normal processing state *)
  | SComment     (* Inside comment until EOL - skip chars *)
  | SMacroAcc    (* Accumulating macro name *)

(** Token with location information *)
type located_token = {
  token: token;
  loc: Location.t;
}

(** Token to string for debugging - v25 format *)
let token_to_string = function
  | TChar (uchar, cat) -> 
      let code = Uchar.to_int uchar in
      let char_str = if code >= 32 && code <= 126 then 
        String.make 1 (Char.chr code) 
      else 
        Printf.sprintf "\\x%02X" code 
      in
      Printf.sprintf "TChar(%s,%s)" char_str (Catcode.catcode_to_string cat)
  | TMacro s -> Printf.sprintf "TMacro(%s)" s
  | TParam n -> Printf.sprintf "TParam(%d)" n
  | TGroupOpen -> "TGroupOpen"
  | TGroupClose -> "TGroupClose"
  | TEOF -> "TEOF"

(** Pretty print a located token *)
let pp_located_token fmt tok =
  Format.fprintf fmt "@%d-%d %s" 
    tok.loc.byte_start tok.loc.byte_end (token_to_string tok.token)