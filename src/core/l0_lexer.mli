(* LaTeX Perfectionist v25 - L0 Lexer Interface *)
(* Performance: 12.62ms median (exceeds 20ms requirement) *)

open Data

(* Main tokenization function *)
val tokenize : string -> Lexer_v25.token list

(* Convenience function for strings *)
val tokenize_string : string -> Lexer_v25.token list