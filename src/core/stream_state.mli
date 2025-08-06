(* Stream State Module Interface - Week 3-6 *)
(* LaTeX Perfectionist v25 - PLANNER.yaml Section 3.1.1 *)

open Data

(** Stream state for chunk-based lexing
    
    From Section 3.1.1:
    - Manages current chunk being processed
    - Tracks lexer FSM state across chunks
    - Maintains token queue as strict deque *)
type t

(** Create initial stream state *)
val create : unit -> t

(** Set current chunk being processed *)
val set_chunk : t -> Chunk.t -> t

(** Get current lexer FSM state *)
val get_lexer_state : t -> Lexer_v25.lexer_state

(** Update lexer FSM state *)
val set_lexer_state : t -> Lexer_v25.lexer_state -> t

(** Add token to rear of queue *)
val emit_token : t -> Lexer_v25.located_token -> t

(** Add multiple tokens to queue *)
val emit_tokens : t -> Lexer_v25.located_token list -> t

(** Take token from front of queue *)
val take_token : t -> Lexer_v25.located_token option * t

(** Get all tokens as list (for non-incremental mode) *)
val get_all_tokens : t -> Lexer_v25.located_token list

(** Check if tokens are available *)
val has_tokens : t -> bool

(** Clear token queue *)
val clear_tokens : t -> t