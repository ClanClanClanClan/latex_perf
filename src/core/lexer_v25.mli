(* Lexer Types Module Interface - Week 3-6 Deliverable - v25 COMPLIANT *)
(* LaTeX Perfectionist v25 - Core types and utilities only *)
(* LEXING IMPLEMENTATION REMOVED: Use lexer_optimized_v25 for production *)

open Data

(** Token type - EXACT v25 specification 
    6 constructors total as specified *)
type token =
  | TChar      of Uchar.t * Catcode.catcode  (* Character with its catcode *)
  | TMacro     of string                          (* Macro name without backslash *)
  | TParam     of int                             (* Parameter #1 .. #9 *)
  | TGroupOpen                                    (* Begin group { *)
  | TGroupClose                                   (* End group } *)
  | TEOF                                          (* End of file *)

(** Lexer state for FSM *)
type lexer_state = 
  | S0_Normal    (* Normal processing state *)
  | SComment     (* Inside comment until EOL *)
  | SMacroAcc    (* Accumulating macro name *)

(** Token with location information *)
type located_token = {
  token: token;
  loc: Location.t;
}

(** Convert token to string for debugging *)
val token_to_string : token -> string

(** Pretty print a located token *)
val pp_located_token : Format.formatter -> located_token -> unit