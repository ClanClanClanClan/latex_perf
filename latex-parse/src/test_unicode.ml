(** Unit tests for Unicode detection utilities. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[unicode] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

(* UTF-8 byte sequences for special characters *)
let en_dash = "\xE2\x80\x93" (* U+2013 *)
let em_dash = "\xE2\x80\x94" (* U+2014 *)
let left_single_quote = "\xE2\x80\x98" (* U+2018 *)
let right_single_quote = "\xE2\x80\x99" (* U+2019 *)
let left_double_quote = "\xE2\x80\x9C" (* U+201C *)
let right_double_quote = "\xE2\x80\x9D" (* U+201D *)
let ellipsis = "\xE2\x80\xA6" (* U+2026 *)

let () =
  (* --- has_curly_quote --- *)
  run "curly: left single" (fun tag ->
      expect (Unicode.has_curly_quote ("text" ^ left_single_quote ^ "more")) tag);

  run "curly: right single" (fun tag ->
      expect (Unicode.has_curly_quote right_single_quote) tag);

  run "curly: left double" (fun tag ->
      expect (Unicode.has_curly_quote left_double_quote) tag);

  run "curly: right double" (fun tag ->
      expect (Unicode.has_curly_quote right_double_quote) tag);

  run "curly: absent" (fun tag ->
      expect (not (Unicode.has_curly_quote "plain ASCII text")) tag);

  run "curly: empty" (fun tag -> expect (not (Unicode.has_curly_quote "")) tag);

  (* --- has_en_dash --- *)
  run "en dash: present" (fun tag ->
      expect (Unicode.has_en_dash ("pages 1" ^ en_dash ^ "10")) tag);

  run "en dash: absent" (fun tag ->
      expect (not (Unicode.has_en_dash "pages 1-10")) tag);

  run "en dash: not em dash" (fun tag ->
      expect (not (Unicode.has_en_dash em_dash)) tag);

  (* --- has_em_dash --- *)
  run "em dash: present" (fun tag ->
      expect (Unicode.has_em_dash ("word" ^ em_dash ^ "word")) tag);

  run "em dash: absent" (fun tag ->
      expect (not (Unicode.has_em_dash "word--word")) tag);

  run "em dash: not en dash" (fun tag ->
      expect (not (Unicode.has_em_dash en_dash)) tag);

  (* --- has_ellipsis_char --- *)
  run "ellipsis: present" (fun tag ->
      expect (Unicode.has_ellipsis_char ("wait" ^ ellipsis)) tag);

  run "ellipsis: absent" (fun tag ->
      expect (not (Unicode.has_ellipsis_char "wait...")) tag);

  (* --- count_en_dash --- *)
  run "count en dash: zero" (fun tag ->
      expect (Unicode.count_en_dash "no dashes here" = 0) tag);

  run "count en dash: one" (fun tag ->
      expect (Unicode.count_en_dash ("a" ^ en_dash ^ "b") = 1) tag);

  run "count en dash: multiple" (fun tag ->
      let s = en_dash ^ "x" ^ en_dash ^ "y" ^ en_dash in
      expect
        (Unicode.count_en_dash s = 3)
        (tag ^ Printf.sprintf ": got %d" (Unicode.count_en_dash s)));

  (* --- count_em_dash --- *)
  run "count em dash: zero" (fun tag ->
      expect (Unicode.count_em_dash "no dashes" = 0) tag);

  run "count em dash: two" (fun tag ->
      let s = em_dash ^ " pause " ^ em_dash in
      expect
        (Unicode.count_em_dash s = 2)
        (tag ^ Printf.sprintf ": got %d" (Unicode.count_em_dash s)));

  (* --- edge cases --- *)
  run "malformed utf8" (fun tag ->
      (* Malformed bytes should not crash *)
      expect (not (Unicode.has_curly_quote "\xFF\xFE")) tag);

  run "mixed content" (fun tag ->
      let s =
        "He said "
        ^ left_double_quote
        ^ "hello"
        ^ right_double_quote
        ^ " "
        ^ em_dash
        ^ " then left"
        ^ ellipsis
      in
      expect (Unicode.has_curly_quote s) tag;
      expect (Unicode.has_em_dash s) tag;
      expect (Unicode.has_ellipsis_char s) tag;
      expect (not (Unicode.has_en_dash s)) tag);

  if !fails > 0 then (
    Printf.eprintf "[unicode] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[unicode] PASS %d cases\n%!" !cases
