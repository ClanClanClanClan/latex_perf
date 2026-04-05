(** Unicode-aware text segmentation using Uutf (spec W66-67).
    Supports CJK, Arabic, mixed-script documents.
    Property: concat(split(s)) preserves content order. *)

type uchar_category =
  | Letter
  | Digit
  | Whitespace
  | Punctuation
  | CJK
  | Arabic
  | Other

type word_segment = { w_text : string; w_start : int; w_end : int }
type sentence_segment = { s_text : string; s_start : int; s_end : int }

val classify_uchar : Uchar.t -> uchar_category
val decode_uchars : string -> Uchar.t list
val split_words : string -> word_segment list
val split_sentences : string -> sentence_segment list
val concat_words : word_segment list -> string
val words_preserve_content : string -> bool
