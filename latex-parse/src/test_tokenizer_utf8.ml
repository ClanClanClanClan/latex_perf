(** Tests for L0 tokenizer UTF-8 support. *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let token_texts (src : string) (toks : Latex_parse_lib.Tokenizer_lite.tok list)
    : string list =
  List.map
    (fun (t : Latex_parse_lib.Tokenizer_lite.tok) ->
      String.sub src t.s (t.e - t.s))
    toks

let words_only (toks : Latex_parse_lib.Tokenizer_lite.tok list) :
    Latex_parse_lib.Tokenizer_lite.tok list =
  List.filter
    (fun (t : Latex_parse_lib.Tokenizer_lite.tok) ->
      t.kind = Latex_parse_lib.Tokenizer_lite.Word)
    toks

let () =
  Printf.printf "[test_tokenizer_utf8]\n%!";

  (* Test 1: plain ASCII unchanged *)
  let src1 = "hello world" in
  let toks1 = Latex_parse_lib.Tokenizer_lite.tokenize src1 in
  let w1 = words_only toks1 in
  check "ascii 2 words" (List.length w1 = 2);
  let texts1 = token_texts src1 w1 in
  check "ascii first = hello" (List.nth texts1 0 = "hello");
  check "ascii second = world" (List.nth texts1 1 = "world");

  (* Test 2: French accented word *)
  let src2 = "caf\xC3\xA9" in
  (* café in UTF-8 *)
  let toks2 = Latex_parse_lib.Tokenizer_lite.tokenize src2 in
  let w2 = words_only toks2 in
  check "café = 1 word" (List.length w2 = 1);
  let texts2 = token_texts src2 w2 in
  check "café text" (List.nth texts2 0 = "caf\xC3\xA9");

  (* Test 3: German umlaut *)
  let src3 = "\xC3\xBC" in
  (* ü in UTF-8 *)
  let toks3 = Latex_parse_lib.Tokenizer_lite.tokenize src3 in
  let w3 = words_only toks3 in
  check "ü = 1 word" (List.length w3 = 1);

  (* Test 4: mixed ASCII and accented *)
  let src4 = "r\xC3\xA9sum\xC3\xA9 test" in
  (* résumé test *)
  let toks4 = Latex_parse_lib.Tokenizer_lite.tokenize src4 in
  let w4 = words_only toks4 in
  check "résumé test = 2 words" (List.length w4 = 2);

  (* Test 5: CJK characters = individual words *)
  let src5 = "\xE4\xB8\xAD\xE6\x96\x87" in
  (* 中文 in UTF-8 *)
  let toks5 = Latex_parse_lib.Tokenizer_lite.tokenize src5 in
  let w5 = words_only toks5 in
  check "中文 = 2 words" (List.length w5 = 2);

  (* Test 6: LaTeX command with accented argument *)
  let src6 = "\\textbf{n\xC3\xB1o}" in
  let toks6 = Latex_parse_lib.Tokenizer_lite.tokenize src6 in
  let cmds =
    List.filter
      (fun (t : Latex_parse_lib.Tokenizer_lite.tok) ->
        t.kind = Latex_parse_lib.Tokenizer_lite.Command)
      toks6
  in
  check "command preserved" (List.length cmds = 1);
  let w6 = words_only toks6 in
  check "ño is word" (List.length w6 >= 1);

  (* Test 7: Greek text *)
  let src7 = "\xCE\xB1\xCE\xB2\xCE\xB3" in
  (* αβγ *)
  let toks7 = Latex_parse_lib.Tokenizer_lite.tokenize src7 in
  let w7 = words_only toks7 in
  check "αβγ = 1 word" (List.length w7 = 1);

  (* Test 8: Cyrillic text *)
  let src8 = "\xD0\xBF\xD1\x80\xD0\xB8\xD0\xB2\xD0\xB5\xD1\x82" in
  (* привет *)
  let toks8 = Latex_parse_lib.Tokenizer_lite.tokenize src8 in
  let w8 = words_only toks8 in
  check "привет = 1 word" (List.length w8 = 1);

  (* Test 9: mixed CJK and ASCII *)
  let src9 = "hello \xE4\xB8\x96\xE7\x95\x8C test" in
  (* hello 世界 test *)
  let toks9 = Latex_parse_lib.Tokenizer_lite.tokenize src9 in
  let w9 = words_only toks9 in
  check "hello 世界 test = 4 words" (List.length w9 = 4);

  (* Test 10: Arabic script *)
  let src10 = "\xD8\xB3\xD9\x84\xD8\xA7\xD9\x85" in
  (* سلام *)
  let toks10 = Latex_parse_lib.Tokenizer_lite.tokenize src10 in
  let w10 = words_only toks10 in
  check "Arabic = 1 word" (List.length w10 = 1);

  Printf.printf "[test_tokenizer_utf8] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_tokenizer_utf8] %d failures\n%!" !fails;
    exit 1)
