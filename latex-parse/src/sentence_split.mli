(** High-throughput sentence boundary detection (spec W68-70). *)

type sentence = {
  text : string;
  start_pos : int;
  end_pos : int;
  word_count : int;
}

val split : string -> sentence list
val count_words : string -> int
val sentences_to_strings : sentence list -> string list
