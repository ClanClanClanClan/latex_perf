(** Tests for Unicode_split — Unicode-aware text segmentation (spec W66-67). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_unicode_split]\n%!";

  (* Test 1: basic ASCII word split *)
  let words = Latex_parse_lib.Unicode_split.split_words "hello world" in
  check "ascii 2 words" (List.length words = 2);
  check "first word" ((List.nth words 0).w_text = "hello");
  check "second word" ((List.nth words 1).w_text = "world");

  (* Test 2: CJK characters are individual words *)
  let cjk = Latex_parse_lib.Unicode_split.split_words "中文测试" in
  check "CJK 4 words" (List.length cjk = 4);

  (* Test 3: mixed script *)
  let mixed = Latex_parse_lib.Unicode_split.split_words "hello 世界 test" in
  check "mixed 4 words" (List.length mixed = 4);
  check "mixed first" ((List.nth mixed 0).w_text = "hello");
  check "mixed last" ((List.nth mixed 3).w_text = "test");

  (* Test 4: sentence split *)
  let sents =
    Latex_parse_lib.Unicode_split.split_sentences
      "First sentence. Second sentence. Third."
  in
  check "3 sentences" (List.length sents = 3);

  (* Test 5: CJK sentence split with 。 *)
  let cjk_sents =
    Latex_parse_lib.Unicode_split.split_sentences
      "第一句。第二句。"
  in
  check "CJK sentences >= 1" (List.length cjk_sents >= 1);

  (* Test 6: empty string *)
  let empty_words = Latex_parse_lib.Unicode_split.split_words "" in
  check "empty words" (List.length empty_words = 0);
  let empty_sents = Latex_parse_lib.Unicode_split.split_sentences "" in
  check "empty sentences" (List.length empty_sents = 0);

  (* Test 7: Unicode classification *)
  let open Latex_parse_lib.Unicode_split in
  check "A is letter" (classify_uchar (Uchar.of_int 0x41) = Letter);
  check "0 is digit" (classify_uchar (Uchar.of_int 0x30) = Digit);
  check "space is whitespace" (classify_uchar (Uchar.of_int 0x20) = Whitespace);
  check "CJK char" (classify_uchar (Uchar.of_int 0x4E2D) = CJK);
  check "Arabic char" (classify_uchar (Uchar.of_int 0x0627) = Arabic);

  (* Test 8: decode_uchars *)
  let uchars = Latex_parse_lib.Unicode_split.decode_uchars "abc" in
  check "decode 3 chars" (List.length uchars = 3);

  (* Test 9: concat_words roundtrip *)
  let words2 = Latex_parse_lib.Unicode_split.split_words "hello world" in
  let joined = Latex_parse_lib.Unicode_split.concat_words words2 in
  check "concat_words" (joined = "helloworld");

  (* Test 10: Latin extended characters *)
  let latin_ext = Latex_parse_lib.Unicode_split.split_words "café résumé" in
  check "latin extended 2 words" (List.length latin_ext = 2);

  (* Test 11: punctuation doesn't create words *)
  let punct = Latex_parse_lib.Unicode_split.split_words "hello, world!" in
  check "punct 2 words" (List.length punct = 2);

  (* Test 12: multiple whitespace *)
  let multi_ws = Latex_parse_lib.Unicode_split.split_words "a   b\t\tc" in
  check "multi whitespace 3 words" (List.length multi_ws = 3);

  Printf.printf "[test_unicode_split] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_unicode_split] %d failures\n%!" !fails;
    exit 1)
