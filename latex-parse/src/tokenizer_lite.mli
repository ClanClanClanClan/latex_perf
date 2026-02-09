(** Lightweight tokeniser for LaTeX-like syntax. *)

type kind =
  | Word
  | Space
  | Newline
  | Command
  | Bracket_open
  | Bracket_close
  | Quote
  | Symbol

type tok = { kind : kind; s : int; e : int; ch : char option }

val is_letter : char -> bool
(** [true] for ASCII letters and digits. *)

val tokenize : string -> tok list
(** Tokenise a source string into a flat list of tokens. *)
