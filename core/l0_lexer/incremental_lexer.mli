(* incremental_lexer.mli - Interface for incremental lexing with 16KB windows *)

type edit_window = {
  start_offset : int;  (** Start position of edit in bytes *)
  end_offset : int;  (** End position of edit in bytes *)
  old_length : int;  (** Length of text being replaced *)
  new_length : int;  (** Length of new text *)
}
(** Edit window represents a region of change in the document *)

type positioned_token = {
  token : Tok.t;  (** The actual token *)
  start_pos : int;  (** Start byte position in document *)
  end_pos : int;  (** End byte position in document *)
  line : int;  (** Line number (1-based) *)
  column : int;  (** Column number (0-based) *)
}
(** Token with position information for incremental updates *)

type incremental_state = {
  tokens : positioned_token array;  (** Current token array *)
  content : string;  (** Current document content *)
  dirty_start : int;  (** Start of last dirty region *)
  dirty_end : int;  (** End of last dirty region *)
}
(** State for incremental lexing *)

val max_dirty_window : int
(** Maximum dirty window size (16KB per planner spec) *)

val create_initial_state : string -> incremental_state
(** Create initial lexer state from full content *)

val lex_incremental :
  previous_state:incremental_state ->
  edit_window:edit_window ->
  new_content:string ->
  incremental_state
(** Perform incremental lexing after an edit
    @param previous_state The state before the edit
    @param edit_window Description of the edit
    @param new_content The content after the edit
    @return Updated incremental state with re-lexed tokens *)

val apply_edit :
  state:incremental_state ->
  edit_window:edit_window ->
  new_text:string ->
  incremental_state
(** Apply an edit and perform incremental lexing (convenience function) *)

val test_edit_window_performance : unit -> unit
(** Performance test for edit-window compliance *)

val prepare_for_edit_window : unit -> unit
(** Prepare incremental lexer for edit-window harness *)
