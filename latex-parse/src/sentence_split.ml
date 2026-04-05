(* ══════════════════════════════════════════════════════════════════════
   Sentence_split — high-throughput sentence boundary detection (spec W68-70,
   target: 50 MiB/s)

   Splits LaTeX text into sentences using period + uppercase heuristic. Designed
   for high throughput on large documents.
   ══════════════════════════════════════════════════════════════════════ *)

type sentence = {
  text : string;
  start_pos : int;
  end_pos : int;
  word_count : int;
}

let split (s : string) : sentence list =
  let len = String.length s in
  let sentences = ref [] in
  let buf = Buffer.create 256 in
  let sent_start = ref 0 in
  let word_count = ref 0 in
  let in_word = ref false in
  let i = ref 0 in
  while !i < len do
    let c = String.unsafe_get s !i in
    Buffer.add_char buf c;
    (* Word counting *)
    if c = ' ' || c = '\t' || c = '\n' then (
      if !in_word then (
        incr word_count;
        in_word := false))
    else in_word := true;
    (* Sentence boundary: ". " followed by uppercase *)
    if
      c = '.'
      && !i + 2 < len
      && String.unsafe_get s (!i + 1) = ' '
      &&
      let nc = String.unsafe_get s (!i + 2) in
      nc >= 'A' && nc <= 'Z'
    then (
      Buffer.add_char buf ' ';
      if !in_word then incr word_count;
      let text = Buffer.contents buf in
      sentences :=
        {
          text;
          start_pos = !sent_start;
          end_pos = !i + 1;
          word_count = !word_count;
        }
        :: !sentences;
      Buffer.clear buf;
      sent_start := !i + 2;
      word_count := 0;
      in_word := false;
      i := !i + 2)
    else incr i
  done;
  (* Flush remaining *)
  if Buffer.length buf > 0 then (
    if !in_word then incr word_count;
    let text = Buffer.contents buf in
    if String.length (String.trim text) > 0 then
      sentences :=
        {
          text;
          start_pos = !sent_start;
          end_pos = len;
          word_count = !word_count;
        }
        :: !sentences);
  List.rev !sentences

let count_words (s : string) : int =
  let s = String.trim s in
  if String.length s = 0 then 0
  else
    let cnt = ref 1 in
    let in_ws = ref false in
    String.iter
      (fun c ->
        if c = ' ' || c = '\t' || c = '\n' then (
          if not !in_ws then incr cnt;
          in_ws := true)
        else in_ws := false)
      s;
    !cnt

let sentences_to_strings (sents : sentence list) : string list =
  List.map (fun s -> s.text) sents
