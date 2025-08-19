(* Token Ring Buffer Interface *)

open Data

type t

val create     : int -> t
val push       : t -> Lexer_v25.token -> unit  
val unsafe_get : t -> int -> Lexer_v25.token
val length     : t -> int
val to_list    : t -> Lexer_v25.token list