(* types.ml - Core types for v24-R3 incremental lexer *)

(** Token types matching Coq specification *)
type token =
  | TChar of char
  | TCommand of string
  | TNewline
  | TSpace
  | TMath
  | TComment of string
  | TBeginEnv of string
  | TEndEnv of string
  | TError of string

(** Lexer modes *)
type mode =
  | MNormal
  | MMath
  | MComment
  | MVerbatim

(** Lexer state - compact representation for serialization *)
type lexer_state = {
  line_no : int;
  col_no : int;
  in_math : bool;
  in_comment : bool;
  in_verbatim : bool;
  mode_stack : mode list;
}

(** Initial state *)
let init_state = {
  line_no = 0;
  col_no = 0;
  in_math = false;
  in_comment = false;
  in_verbatim = false;
  mode_stack = [];
}

(** Line information for incremental processing *)
type line_info = {
  li_hash : int64;           (* xxHash of this line *)
  li_end_state : lexer_state; (* state after the line *)
  li_tokens : token list;     (* tokens of the line *)
  li_start_pos : int;         (* byte position in document *)
  li_end_pos : int;           (* end byte position *)
}

(** Checkpoint for recovery *)
type checkpoint = {
  cp_offset : int;            (* byte offset *)
  cp_state : lexer_state;     (* lexer state at this point *)
  cp_line_no : int;           (* line number *)
}

(** Edit operation *)
type edit_op =
  | Insert of int * string    (* position, text *)
  | Delete of int * int       (* start, length *)
  | Replace of int * int * string (* start, length, new_text *)

(** Performance statistics *)
type perf_stats = {
  mutable total_bytes : int;
  mutable incremental_bytes : int;
  mutable cache_hits : int;
  mutable cache_misses : int;
  mutable parse_time_us : int;
}

let make_perf_stats () = {
  total_bytes = 0;
  incremental_bytes = 0;
  cache_hits = 0;
  cache_misses = 0;
  parse_time_us = 0;
}