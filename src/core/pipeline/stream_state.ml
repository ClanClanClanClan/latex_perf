(* Stream State Module - Week 3-6 *)
(* LaTeX Perfectionist v25 - PLANNER.yaml Section 3.1.1 *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

(** Stream state for chunk-based lexing *)
type t = {
  pending   : Chunk.t option;         (* Current chunk being processed *)
  lex_state : lexer_state;                 (* Current lexer FSM state *)
  tokens    : located_token Dlist.t;  (* Token queue (strict deque) *)
}

(** Create initial stream state *)
let create () = {
  pending = None;
  lex_state = S0_Normal;
  tokens = Dlist.empty;
}

(** Set current chunk *)
let set_chunk stream chunk =
  { stream with pending = Some chunk }

(** Get current lexer state *)
let get_lexer_state stream = stream.lex_state

(** Update lexer state *)
let set_lexer_state stream state =
  { stream with lex_state = state }

(** Add token to rear of queue *)
let emit_token stream token =
  { stream with tokens = Dlist.snoc stream.tokens token }

(** Add multiple tokens *)
let emit_tokens stream token_list =
  List.fold_left emit_token stream token_list

(** Take token from front of queue *)
let take_token stream =
  match Dlist.uncons stream.tokens with
  | None -> None, stream
  | Some (tok, rest) -> 
      Some tok, { stream with tokens = rest }

(** Get all tokens as list *)
let get_all_tokens stream =
  Dlist.to_list stream.tokens

(** Check if tokens available *)
let has_tokens stream =
  not (Dlist.is_empty stream.tokens)

(** Clear token queue *)
let clear_tokens stream =
  { stream with tokens = Dlist.empty }