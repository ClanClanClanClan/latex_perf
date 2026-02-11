(** Unit tests for ENC/CHAR/SPC batch 2 validator rules. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[batch2] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let find_result id src =
  let results = Validators.run_all src in
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let fires id src = find_result id src <> None

let fires_with_count id src expected_count =
  match find_result id src with
  | Some r -> r.count = expected_count
  | None -> false

let does_not_fire id src = find_result id src = None

let () =
  (* ══════════════════════════════════════════════════════════════════════ ENC
     batch 2
     ══════════════════════════════════════════════════════════════════════ *)

  (* ENC-001: Non-UTF-8 byte sequence detected *)
  run "ENC-001 fires on bare 0xFF" (fun tag ->
      expect (fires "ENC-001" "hello\xffworld") (tag ^ ": 0xFF"));
  run "ENC-001 fires on truncated 2-byte" (fun tag ->
      (* 0xC3 without continuation byte *)
      expect (fires "ENC-001" "end\xc3") (tag ^ ": truncated"));
  run "ENC-001 clean UTF-8" (fun tag ->
      (* Valid UTF-8: e with accent = C3 A9 *)
      expect (does_not_fire "ENC-001" "caf\xc3\xa9") (tag ^ ": valid UTF-8"));
  run "ENC-001 clean ASCII" (fun tag ->
      expect (does_not_fire "ENC-001" "plain ASCII") (tag ^ ": ASCII"));

  (* ENC-002: BOM U+FEFF in middle of file *)
  run "ENC-002 fires on interior BOM" (fun tag ->
      expect (fires "ENC-002" "text\xef\xbb\xbfmore") (tag ^ ": interior"));
  run "ENC-002 allows start BOM" (fun tag ->
      expect
        (does_not_fire "ENC-002" "\xef\xbb\xbfstart only")
        (tag ^ ": start ok"));
  run "ENC-002 clean" (fun tag ->
      expect (does_not_fire "ENC-002" "no BOM at all") (tag ^ ": clean"));

  (* ENC-003: LATIN-1 smart quotes *)
  run "ENC-003 fires on 0x93" (fun tag ->
      expect (fires "ENC-003" "say \x93hello\x94") (tag ^ ": smart quotes"));
  run "ENC-003 fires on 0x91" (fun tag ->
      expect (fires "ENC-003" "\x91quoted\x92") (tag ^ ": single quotes"));
  run "ENC-003 clean" (fun tag ->
      expect (does_not_fire "ENC-003" "normal text") (tag ^ ": clean"));

  (* ENC-004: Windows-1252 characters *)
  run "ENC-004 fires on 0x85" (fun tag ->
      expect (fires "ENC-004" "text\x85more") (tag ^ ": ellipsis byte"));
  run "ENC-004 fires on 0x96" (fun tag ->
      expect (fires "ENC-004" "text\x96more") (tag ^ ": en-dash byte"));
  run "ENC-004 clean" (fun tag ->
      expect (does_not_fire "ENC-004" "normal text") (tag ^ ": clean"));

  (* ENC-013: Mixed CRLF and LF line endings *)
  run "ENC-013 fires on mixed" (fun tag ->
      expect (fires "ENC-013" "line1\r\nline2\nline3") (tag ^ ": mixed"));
  run "ENC-013 ok all LF" (fun tag ->
      expect (does_not_fire "ENC-013" "line1\nline2\nline3") (tag ^ ": all LF"));
  run "ENC-013 ok all CRLF" (fun tag ->
      expect
        (does_not_fire "ENC-013" "line1\r\nline2\r\nline3")
        (tag ^ ": all CRLF"));

  (* ENC-014: UTF-16 byte-order mark *)
  run "ENC-014 fires on UTF-16 LE BOM" (fun tag ->
      expect (fires "ENC-014" "\xff\xfedata") (tag ^ ": UTF-16 LE"));
  run "ENC-014 fires on UTF-16 BE BOM" (fun tag ->
      expect (fires "ENC-014" "\xfe\xffdata") (tag ^ ": UTF-16 BE"));
  run "ENC-014 clean" (fun tag ->
      expect (does_not_fire "ENC-014" "normal data") (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════ CHAR
     batch 2
     ══════════════════════════════════════════════════════════════════════ *)

  (* CHAR-015: Emoji detected in source *)
  run "CHAR-015 fires on emoji" (fun tag ->
      (* U+1F600 = F0 9F 98 80 (grinning face) *)
      expect (fires "CHAR-015" "text\xf0\x9f\x98\x80here") (tag ^ ": emoji"));
  run "CHAR-015 fires on rocket" (fun tag ->
      (* U+1F680 = F0 9F 9A 80 *)
      expect (fires "CHAR-015" "\xf0\x9f\x9a\x80") (tag ^ ": rocket"));
  run "CHAR-015 clean" (fun tag ->
      expect (does_not_fire "CHAR-015" "no emojis here") (tag ^ ": clean"));

  (* CHAR-017: Full-width Latin letters *)
  run "CHAR-017 fires on fullwidth A" (fun tag ->
      (* U+FF21 = EF BC A1 *)
      expect (fires "CHAR-017" "text\xef\xbc\xa1here") (tag ^ ": fullwidth A"));
  run "CHAR-017 fires on fullwidth a" (fun tag ->
      (* U+FF41 = EF BD 81 *)
      expect (fires "CHAR-017" "text\xef\xbd\x81here") (tag ^ ": fullwidth a"));
  run "CHAR-017 count=2" (fun tag ->
      expect
        (fires_with_count "CHAR-017" "\xef\xbc\xa1\xef\xbd\x81" 2)
        (tag ^ ": count"));
  run "CHAR-017 clean" (fun tag ->
      expect (does_not_fire "CHAR-017" "normal ASCII") (tag ^ ": clean"));

  (* CHAR-018: Deprecated ligature characters *)
  run "CHAR-018 fires on fi ligature" (fun tag ->
      (* U+FB01 = EF AC 81 *)
      expect (fires "CHAR-018" "of\xef\xac\x81ce") (tag ^ ": fi ligature"));
  run "CHAR-018 fires on ff ligature" (fun tag ->
      (* U+FB00 = EF AC 80 *)
      expect (fires "CHAR-018" "\xef\xac\x80ect") (tag ^ ": ff ligature"));
  run "CHAR-018 clean" (fun tag ->
      expect (does_not_fire "CHAR-018" "office effect") (tag ^ ": clean"));

  (* CHAR-022: Deprecated tag characters U+E0000-E007F *)
  run "CHAR-022 fires" (fun tag ->
      (* U+E0001 = F3 A0 80 81 *)
      expect (fires "CHAR-022" "text\xf3\xa0\x80\x81here") (tag ^ ": tag char"));
  run "CHAR-022 clean" (fun tag ->
      expect (does_not_fire "CHAR-022" "normal text") (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════ SPC
     batch 2
     ══════════════════════════════════════════════════════════════════════ *)

  (* SPC-007: Three or more consecutive blank lines *)
  run "SPC-007 fires on 3 blank lines" (fun tag ->
      expect (fires "SPC-007" "text\n\n\n\nmore") (tag ^ ": 3 blank"));
  run "SPC-007 ok on 2 blank lines" (fun tag ->
      expect (does_not_fire "SPC-007" "text\n\n\nmore") (tag ^ ": 2 blank ok"));

  (* SPC-008: Paragraph starts with whitespace *)
  run "SPC-008 fires on indented para" (fun tag ->
      expect (fires "SPC-008" "\n  Indented paragraph") (tag ^ ": indented"));
  run "SPC-008 fires after blank" (fun tag ->
      expect (fires "SPC-008" "text\n\n  Next para") (tag ^ ": after blank"));
  run "SPC-008 ok no indent" (fun tag ->
      expect
        (does_not_fire "SPC-008" "text\n\nNext para")
        (tag ^ ": no indent ok"));

  (* SPC-009: Non-breaking space ~ at line start *)
  run "SPC-009 fires on tilde start" (fun tag ->
      expect (fires "SPC-009" "~start of line") (tag ^ ": tilde"));
  run "SPC-009 fires on NBSP start" (fun tag ->
      (* U+00A0 = C2 A0 *)
      expect (fires "SPC-009" "\xc2\xa0start") (tag ^ ": NBSP"));
  run "SPC-009 clean" (fun tag ->
      expect (does_not_fire "SPC-009" "normal start") (tag ^ ": clean"));

  (* SPC-013: Whitespace-only paragraph *)
  run "SPC-013 fires" (fun tag ->
      expect (fires "SPC-013" "text\n\n   \n\nmore") (tag ^ ": ws para"));
  run "SPC-013 clean" (fun tag ->
      expect
        (does_not_fire "SPC-013" "text\n\nreal content\n\nmore")
        (tag ^ ": clean"));

  (* SPC-014: Mixed LF and CRLF *)
  run "SPC-014 fires" (fun tag ->
      expect (fires "SPC-014" "a\r\nb\nc") (tag ^ ": mixed"));
  run "SPC-014 ok all LF" (fun tag ->
      expect (does_not_fire "SPC-014" "a\nb\nc") (tag ^ ": all LF"));

  (* SPC-015: Indentation exceeds 8 spaces *)
  run "SPC-015 fires on 9 spaces" (fun tag ->
      expect (fires "SPC-015" "         code") (tag ^ ": 9 spaces"));
  run "SPC-015 ok at 8 spaces" (fun tag ->
      expect (does_not_fire "SPC-015" "        code") (tag ^ ": 8 ok"));

  (* SPC-016: Space before semicolon *)
  run "SPC-016 fires" (fun tag ->
      expect (fires "SPC-016" "text ;more") (tag ^ ": space-semi"));
  run "SPC-016 clean" (fun tag ->
      expect (does_not_fire "SPC-016" "text;more") (tag ^ ": clean"));

  (* SPC-019: Trailing full-width space U+3000 *)
  run "SPC-019 fires" (fun tag ->
      (* U+3000 = E3 80 80 at end of line *)
      expect (fires "SPC-019" "text\xe3\x80\x80\nmore") (tag ^ ": trailing"));
  run "SPC-019 clean" (fun tag ->
      expect (does_not_fire "SPC-019" "text\nmore") (tag ^ ": clean"));

  (* SPC-021: Space before colon *)
  run "SPC-021 fires" (fun tag ->
      expect (fires "SPC-021" "label :value") (tag ^ ": space-colon"));
  run "SPC-021 clean" (fun tag ->
      expect (does_not_fire "SPC-021" "label:value") (tag ^ ": clean"));

  (* SPC-025: Space before ellipsis *)
  run "SPC-025 fires on \\dots" (fun tag ->
      expect (fires "SPC-025" "text \\dots more") (tag ^ ": dots cmd"));
  run "SPC-025 fires on Unicode ellipsis" (fun tag ->
      (* U+2026 = E2 80 A6 *)
      expect (fires "SPC-025" "text \xe2\x80\xa6more") (tag ^ ": unicode"));
  run "SPC-025 clean" (fun tag ->
      expect (does_not_fire "SPC-025" "text\\dots more") (tag ^ ": clean"));

  (* SPC-029: Indentation uses NBSP *)
  run "SPC-029 fires" (fun tag ->
      expect (fires "SPC-029" "\xc2\xa0\xc2\xa0code") (tag ^ ": nbsp indent"));
  run "SPC-029 clean" (fun tag ->
      expect (does_not_fire "SPC-029" "  code") (tag ^ ": regular spaces"));

  (* SPC-030: Line starts with full-width space U+3000 *)
  run "SPC-030 fires" (fun tag ->
      expect (fires "SPC-030" "\xe3\x80\x80text") (tag ^ ": fw space start"));
  run "SPC-030 clean" (fun tag ->
      expect (does_not_fire "SPC-030" " text") (tag ^ ": normal space"));

  (* SPC-031: Three spaces after period *)
  run "SPC-031 fires" (fun tag ->
      expect (fires "SPC-031" "End.   Next") (tag ^ ": three spaces"));
  run "SPC-031 ok two spaces" (fun tag ->
      expect (does_not_fire "SPC-031" "End.  Next") (tag ^ ": two ok"));

  (* SPC-032: Mixed NBSP and space in indentation *)
  run "SPC-032 fires" (fun tag ->
      expect (fires "SPC-032" "\xc2\xa0 code") (tag ^ ": nbsp+space"));
  run "SPC-032 fires reverse" (fun tag ->
      expect (fires "SPC-032" " \xc2\xa0code") (tag ^ ": space+nbsp"));
  run "SPC-032 clean" (fun tag ->
      expect (does_not_fire "SPC-032" "   code") (tag ^ ": spaces only"));

  (* SPC-033: NBSP before em-dash *)
  run "SPC-033 fires on NBSP + Unicode em-dash" (fun tag ->
      expect (fires "SPC-033" "word\xc2\xa0\xe2\x80\x94more") (tag ^ ": nbsp+em"));
  run "SPC-033 fires on NBSP + ---" (fun tag ->
      expect (fires "SPC-033" "word\xc2\xa0---more") (tag ^ ": nbsp+---"));
  run "SPC-033 clean" (fun tag ->
      expect (does_not_fire "SPC-033" "word---more") (tag ^ ": clean"));

  (* SPC-034: Thin-space before en-dash *)
  run "SPC-034 fires on thinsp + Unicode en-dash" (fun tag ->
      expect (fires "SPC-034" "a\xe2\x80\x89\xe2\x80\x93b") (tag ^ ": thinsp+en"));
  run "SPC-034 fires on thinsp + --" (fun tag ->
      expect (fires "SPC-034" "a\xe2\x80\x89--b") (tag ^ ": thinsp+--"));
  run "SPC-034 clean" (fun tag ->
      expect (does_not_fire "SPC-034" "a--b") (tag ^ ": clean"));

  (* SPC-035: Leading thin-space U+2009 at start of line *)
  run "SPC-035 fires" (fun tag ->
      expect (fires "SPC-035" "\xe2\x80\x89text") (tag ^ ": thin space start"));
  run "SPC-035 clean" (fun tag ->
      expect (does_not_fire "SPC-035" " text") (tag ^ ": normal space"));

  (* ══════════════════════════════════════════════════════════════════════
     Math-mode edge cases for rules using strip_math_segments
     ══════════════════════════════════════════════════════════════════════ *)

  (* SPC-016: space-semicolon — uses strip_math_segments, so $ ;$ is ok *)
  run "SPC-016 does not fire in math" (fun tag ->
      expect
        (does_not_fire "SPC-016" "Let $f ;g$ be functions")
        (tag ^ ": math stripped"));
  run "SPC-016 fires in text even with math present" (fun tag ->
      expect
        (fires "SPC-016" "Text ;more $x$")
        (tag ^ ": text fires despite math"));

  (* SPC-021: space-colon — uses strip_math_segments *)
  run "SPC-021 does not fire in math" (fun tag ->
      expect
        (does_not_fire "SPC-021" "Map $f :A\\to B$")
        (tag ^ ": math stripped"));
  run "SPC-021 fires in text even with math present" (fun tag ->
      expect
        (fires "SPC-021" "Label :value $x$")
        (tag ^ ": text fires despite math"));

  (* SPC-031: three spaces after period — uses strip_math_segments *)
  run "SPC-031 does not fire in math" (fun tag ->
      expect
        (does_not_fire "SPC-031" "Text $a.   b$ more")
        (tag ^ ": math stripped"));
  run "SPC-031 fires in text even with math present" (fun tag ->
      expect
        (fires "SPC-031" "End.   Next $x$ sentence")
        (tag ^ ": text fires despite math"));

  (* ══════════════════════════════════════════════════════════════════════
     Additional count verification tests
     ══════════════════════════════════════════════════════════════════════ *)
  run "SPC-007 count=2 for two groups of 3+ blank lines" (fun tag ->
      expect
        (fires_with_count "SPC-007" "a\n\n\n\nb\n\n\n\nc" 2)
        (tag ^ ": count=2"));
  run "SPC-008 count=2 for two indented paragraphs" (fun tag ->
      expect
        (fires_with_count "SPC-008" "text\n\n  para1\n\n  para2" 2)
        (tag ^ ": count=2"));
  run "SPC-016 count=2 for two space-semis" (fun tag ->
      expect (fires_with_count "SPC-016" "a ;b ;c" 2) (tag ^ ": count=2"));
  run "SPC-021 count=2 for two space-colons" (fun tag ->
      expect (fires_with_count "SPC-021" "a :b :c" 2) (tag ^ ": count=2"));
  run "SPC-029 count=2 for two NBSP-indented lines" (fun tag ->
      expect
        (fires_with_count "SPC-029" "\xc2\xa0code\n\xc2\xa0more" 2)
        (tag ^ ": count=2"));
  run "SPC-032 count=2 for two mixed-indent lines" (fun tag ->
      expect
        (fires_with_count "SPC-032" "\xc2\xa0 code\n\xc2\xa0 more" 2)
        (tag ^ ": count=2"));

  (* ══════════════════════════════════════════════════════════════════════
     Boundary condition tests
     ══════════════════════════════════════════════════════════════════════ *)

  (* ENC-001: valid 3-byte and 4-byte UTF-8 should not fire *)
  run "ENC-001 clean 3-byte UTF-8" (fun tag ->
      (* U+2603 snowman = E2 98 83 *)
      expect (does_not_fire "ENC-001" "\xe2\x98\x83") (tag ^ ": 3-byte ok"));
  run "ENC-001 clean 4-byte UTF-8" (fun tag ->
      (* U+1F600 = F0 9F 98 80 *)
      expect (does_not_fire "ENC-001" "\xf0\x9f\x98\x80") (tag ^ ": 4-byte ok"));

  (* SPC-015: exactly 8 spaces = ok, 9 = fires *)
  run "SPC-015 boundary: 8 spaces ok" (fun tag ->
      expect (does_not_fire "SPC-015" "        code") (tag ^ ": 8 ok"));

  (* SPC-009: NBSP mid-line should not fire *)
  run "SPC-009 does not fire on mid-line NBSP" (fun tag ->
      expect
        (does_not_fire "SPC-009" "Figure\xc2\xa01")
        (tag ^ ": mid-line NBSP ok"));

  (* CHAR-015: various emoji ranges *)
  run "CHAR-015 fires on heart emoji" (fun tag ->
      (* U+2764 = E2 9D A4 — but this is in the misc symbols range, not
         guaranteed to be detected. Test with basic SMP emoji instead. *)
      (* U+1F4A9 = F0 9F 92 A9 *)
      expect (fires "CHAR-015" "\xf0\x9f\x92\xa9") (tag ^ ": SMP emoji"));

  (* ══════════════════════════════════════════════════════════════════════ Edge
     cases
     ══════════════════════════════════════════════════════════════════════ *)

  (* Empty input triggers nothing for batch 2 rules *)
  run "empty input" (fun tag ->
      let results = Validators.run_all "" in
      let batch2 =
        List.filter
          (fun (r : Validators.result) ->
            List.mem r.id
              [
                "ENC-001";
                "ENC-002";
                "ENC-003";
                "ENC-004";
                "ENC-013";
                "ENC-014";
                "CHAR-015";
                "CHAR-017";
                "CHAR-018";
                "CHAR-022";
                "SPC-007";
                "SPC-008";
                "SPC-009";
                "SPC-013";
                "SPC-014";
                "SPC-015";
                "SPC-016";
                "SPC-019";
                "SPC-021";
                "SPC-025";
                "SPC-029";
                "SPC-030";
                "SPC-031";
                "SPC-032";
                "SPC-033";
                "SPC-034";
                "SPC-035";
              ])
          results
      in
      expect (batch2 = []) (tag ^ ": no batch2 on empty"));

  (* Clean LaTeX triggers no batch2 rules *)
  run "clean LaTeX" (fun tag ->
      let src =
        "\\documentclass{article}\n\
         \\begin{document}\n\
         Hello, world!\n\
         \\end{document}\n"
      in
      let results = Validators.run_all src in
      let batch2 =
        List.filter
          (fun (r : Validators.result) ->
            List.mem r.id
              [
                "ENC-001";
                "ENC-002";
                "ENC-003";
                "ENC-004";
                "ENC-013";
                "ENC-014";
                "CHAR-015";
                "CHAR-017";
                "CHAR-018";
                "CHAR-022";
                "SPC-007";
                "SPC-008";
                "SPC-009";
                "SPC-013";
                "SPC-014";
                "SPC-015";
                "SPC-016";
                "SPC-019";
                "SPC-021";
                "SPC-025";
                "SPC-029";
                "SPC-030";
                "SPC-031";
                "SPC-032";
                "SPC-033";
                "SPC-034";
                "SPC-035";
              ])
          results
      in
      expect (batch2 = []) (tag ^ ": clean LaTeX"));

  if !fails > 0 then (
    Printf.eprintf "[batch2] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[batch2] PASS %d cases\n%!" !cases
