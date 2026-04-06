(** Tests for sentence_split — high-throughput sentence boundary detection (spec
    W68-70). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_sentence_split]\n%!";

  (* Test 1: basic 2-sentence split *)
  let sents =
    Latex_parse_lib.Sentence_split.split "Hello world. Goodbye world."
  in
  check "2 sentences" (List.length sents = 2);

  (* Test 2: single sentence no period *)
  let sents2 = Latex_parse_lib.Sentence_split.split "Just one sentence" in
  check "1 sentence no period" (List.length sents2 = 1);

  (* Test 3: empty input *)
  let sents3 = Latex_parse_lib.Sentence_split.split "" in
  check "empty = 0 sentences" (List.length sents3 = 0);

  (* Test 4: sentence positions *)
  let sents4 = Latex_parse_lib.Sentence_split.split "First. Second. Third." in
  check "3 sentences" (List.length sents4 = 3);
  let s1 = List.nth sents4 0 in
  check "first start_pos = 0" (s1.start_pos = 0);

  (* Test 5: word count *)
  let sents5 =
    Latex_parse_lib.Sentence_split.split "One two three. Four five."
  in
  let s1 = List.nth sents5 0 in
  check "first sentence word_count >= 3" (s1.word_count >= 3);

  (* Test 6: period not followed by uppercase = no split *)
  let sents6 =
    Latex_parse_lib.Sentence_split.split "e.g. this should not split"
  in
  check "abbreviation: 1 sentence" (List.length sents6 = 1);

  (* Test 7: count_words *)
  check "count_words 'hello world' = 2"
    (Latex_parse_lib.Sentence_split.count_words "hello world" = 2);
  check "count_words '' = 0" (Latex_parse_lib.Sentence_split.count_words "" = 0);
  check "count_words 'one' = 1"
    (Latex_parse_lib.Sentence_split.count_words "one" = 1);

  (* Test 8: sentences_to_strings *)
  let sents7 = Latex_parse_lib.Sentence_split.split "A. B." in
  let strs = Latex_parse_lib.Sentence_split.sentences_to_strings sents7 in
  check "sentences_to_strings length" (List.length strs = List.length sents7);

  (* Test 9: period followed by space + uppercase *)
  let sents8 =
    Latex_parse_lib.Sentence_split.split "Hello world. Next sentence here."
  in
  check "standard 2-sentence split" (List.length sents8 = 2);

  Printf.printf "[test_sentence_split] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_sentence_split] %d failures\n%!" !fails;
    exit 1)
