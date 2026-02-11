(** Unit tests for ENC, CHAR, SPC, and TYPO-062 validator rules. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[enc-char-spc] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

(* Helper: run all validators and find result for a specific rule ID *)
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
     rules
     ══════════════════════════════════════════════════════════════════════ *)

  (* ENC-007: Zero-width space U+200B *)
  run "ENC-007 fires on ZWS" (fun tag ->
      expect (fires "ENC-007" "hello\xe2\x80\x8bworld") (tag ^ ": should fire"));
  run "ENC-007 count=2" (fun tag ->
      expect
        (fires_with_count "ENC-007" "a\xe2\x80\x8bb\xe2\x80\x8bc" 2)
        (tag ^ ": count"));
  run "ENC-007 clean" (fun tag ->
      expect (does_not_fire "ENC-007" "hello world") (tag ^ ": clean"));

  (* ENC-012: C1 control characters U+0080-009F *)
  run "ENC-012 fires on C1" (fun tag ->
      (* U+0085 = NEXT LINE = \xC2\x85 *)
      expect (fires "ENC-012" "text\xc2\x85here") (tag ^ ": should fire"));
  run "ENC-012 fires U+0080" (fun tag ->
      expect (fires "ENC-012" "\xc2\x80") (tag ^ ": U+0080"));
  run "ENC-012 fires U+009F" (fun tag ->
      expect (fires "ENC-012" "\xc2\x9f") (tag ^ ": U+009F"));
  run "ENC-012 does not fire on U+00A0" (fun tag ->
      (* U+00A0 = NBSP = \xC2\xA0, outside the C1 range *)
      expect (does_not_fire "ENC-012" "text\xc2\xa0here") (tag ^ ": U+00A0"));
  run "ENC-012 clean" (fun tag ->
      expect (does_not_fire "ENC-012" "normal ascii text") (tag ^ ": clean"));

  (* ENC-017: Soft hyphen U+00AD *)
  run "ENC-017 fires" (fun tag ->
      expect (fires "ENC-017" "hyphen\xc2\xadated") (tag ^ ": should fire"));
  run "ENC-017 clean" (fun tag ->
      expect (does_not_fire "ENC-017" "no soft hyphens") (tag ^ ": clean"));

  (* ENC-020: Invisible formatting marks LRM/RLM *)
  run "ENC-020 fires on LRM" (fun tag ->
      (* U+200E = LRM = \xe2\x80\x8e *)
      expect (fires "ENC-020" "a\xe2\x80\x8eb") (tag ^ ": LRM"));
  run "ENC-020 fires on RLM" (fun tag ->
      (* U+200F = RLM = \xe2\x80\x8f *)
      expect (fires "ENC-020" "a\xe2\x80\x8fb") (tag ^ ": RLM"));
  run "ENC-020 clean" (fun tag ->
      expect (does_not_fire "ENC-020" "normal text") (tag ^ ": clean"));

  (* ENC-021: Word joiner U+2060 *)
  run "ENC-021 fires" (fun tag ->
      expect (fires "ENC-021" "join\xe2\x81\xa0ed") (tag ^ ": should fire"));
  run "ENC-021 clean" (fun tag ->
      expect (does_not_fire "ENC-021" "no word joiner") (tag ^ ": clean"));

  (* ENC-022: Interlinear annotation U+FFF9-FFFB *)
  run "ENC-022 fires on FFF9" (fun tag ->
      expect (fires "ENC-022" "x\xef\xbf\xb9y") (tag ^ ": U+FFF9"));
  run "ENC-022 fires on FFFA" (fun tag ->
      expect (fires "ENC-022" "x\xef\xbf\xbay") (tag ^ ": U+FFFA"));
  run "ENC-022 fires on FFFB" (fun tag ->
      expect (fires "ENC-022" "x\xef\xbf\xbby") (tag ^ ": U+FFFB"));
  run "ENC-022 clean" (fun tag ->
      expect (does_not_fire "ENC-022" "normal") (tag ^ ": clean"));

  (* ENC-023: Narrow no-break space U+202F *)
  run "ENC-023 fires" (fun tag ->
      expect (fires "ENC-023" "a\xe2\x80\xafb") (tag ^ ": should fire"));
  run "ENC-023 clean" (fun tag ->
      expect (does_not_fire "ENC-023" "plain text") (tag ^ ": clean"));

  (* ENC-024: Bidirectional embeddings U+202A-202E *)
  run "ENC-024 fires on LRE U+202A" (fun tag ->
      expect (fires "ENC-024" "\xe2\x80\xaa") (tag ^ ": U+202A"));
  run "ENC-024 fires on RLE U+202B" (fun tag ->
      expect (fires "ENC-024" "\xe2\x80\xab") (tag ^ ": U+202B"));
  run "ENC-024 fires on PDF U+202C" (fun tag ->
      expect (fires "ENC-024" "\xe2\x80\xac") (tag ^ ": U+202C"));
  run "ENC-024 fires on LRO U+202D" (fun tag ->
      expect (fires "ENC-024" "\xe2\x80\xad") (tag ^ ": U+202D"));
  run "ENC-024 fires on RLO U+202E" (fun tag ->
      expect (fires "ENC-024" "\xe2\x80\xae") (tag ^ ": U+202E"));
  run "ENC-024 count=2" (fun tag ->
      expect
        (fires_with_count "ENC-024" "a\xe2\x80\xaab\xe2\x80\xaec" 2)
        (tag ^ ": count"));
  run "ENC-024 clean" (fun tag ->
      expect (does_not_fire "ENC-024" "normal text") (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════ CHAR
     rules
     ══════════════════════════════════════════════════════════════════════ *)

  (* CHAR-006: Backspace U+0008 *)
  run "CHAR-006 fires" (fun tag ->
      expect (fires "CHAR-006" "ab\x08c") (tag ^ ": should fire"));
  run "CHAR-006 count=3" (fun tag ->
      expect (fires_with_count "CHAR-006" "\x08\x08\x08" 3) (tag ^ ": count"));
  run "CHAR-006 clean" (fun tag ->
      expect (does_not_fire "CHAR-006" "no backspace") (tag ^ ": clean"));

  (* CHAR-007: Bell/alert U+0007 *)
  run "CHAR-007 fires" (fun tag ->
      expect (fires "CHAR-007" "bell\x07here") (tag ^ ": should fire"));
  run "CHAR-007 clean" (fun tag ->
      expect (does_not_fire "CHAR-007" "silence") (tag ^ ": clean"));

  (* CHAR-008: Form feed U+000C *)
  run "CHAR-008 fires" (fun tag ->
      expect (fires "CHAR-008" "page\x0cbreak") (tag ^ ": should fire"));
  run "CHAR-008 clean" (fun tag ->
      expect (does_not_fire "CHAR-008" "no form feed") (tag ^ ": clean"));

  (* CHAR-009: Delete U+007F *)
  run "CHAR-009 fires" (fun tag ->
      expect (fires "CHAR-009" "del\x7fete") (tag ^ ": should fire"));
  run "CHAR-009 clean" (fun tag ->
      expect (does_not_fire "CHAR-009" "normal text") (tag ^ ": clean"));

  (* CHAR-013: Bidirectional isolate chars U+2066-2069 *)
  run "CHAR-013 fires on LRI U+2066" (fun tag ->
      expect (fires "CHAR-013" "\xe2\x81\xa6") (tag ^ ": U+2066"));
  run "CHAR-013 fires on RLI U+2067" (fun tag ->
      expect (fires "CHAR-013" "\xe2\x81\xa7") (tag ^ ": U+2067"));
  run "CHAR-013 fires on FSI U+2068" (fun tag ->
      expect (fires "CHAR-013" "\xe2\x81\xa8") (tag ^ ": U+2068"));
  run "CHAR-013 fires on PDI U+2069" (fun tag ->
      expect (fires "CHAR-013" "\xe2\x81\xa9") (tag ^ ": U+2069"));
  run "CHAR-013 clean" (fun tag ->
      expect (does_not_fire "CHAR-013" "normal text") (tag ^ ": clean"));

  (* CHAR-014: Unicode replacement character U+FFFD *)
  run "CHAR-014 fires" (fun tag ->
      expect (fires "CHAR-014" "bad\xef\xbf\xbdbyte") (tag ^ ": should fire"));
  run "CHAR-014 count=2" (fun tag ->
      expect
        (fires_with_count "CHAR-014" "\xef\xbf\xbd\xef\xbf\xbd" 2)
        (tag ^ ": count"));
  run "CHAR-014 clean" (fun tag ->
      expect (does_not_fire "CHAR-014" "normal text") (tag ^ ": clean"));

  (* CHAR-021: Stray BOM U+FEFF inside paragraph *)
  run "CHAR-021 fires on interior BOM" (fun tag ->
      expect (fires "CHAR-021" "text\xef\xbb\xbfmore") (tag ^ ": should fire"));
  run "CHAR-021 allows BOM at start" (fun tag ->
      (* A single BOM at the very start is legitimate *)
      expect
        (does_not_fire "CHAR-021" "\xef\xbb\xbflegitimate start")
        (tag ^ ": start BOM ok"));
  run "CHAR-021 fires on second BOM even with start BOM" (fun tag ->
      expect
        (fires "CHAR-021" "\xef\xbb\xbfstart\xef\xbb\xbfmiddle")
        (tag ^ ": second BOM fires"));
  run "CHAR-021 clean" (fun tag ->
      expect (does_not_fire "CHAR-021" "no BOM at all") (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════ SPC
     rules
     ══════════════════════════════════════════════════════════════════════ *)

  (* SPC-001: Line longer than 120 characters *)
  run "SPC-001 fires on long line" (fun tag ->
      let long = String.make 121 'x' in
      expect (fires "SPC-001" long) (tag ^ ": 121 chars"));
  run "SPC-001 ok at 120" (fun tag ->
      let exact = String.make 120 'x' in
      expect (does_not_fire "SPC-001" exact) (tag ^ ": 120 ok"));
  run "SPC-001 multiline counts" (fun tag ->
      let input =
        "short\n" ^ String.make 130 'a' ^ "\nshort\n" ^ String.make 200 'b'
      in
      expect (fires_with_count "SPC-001" input 2) (tag ^ ": 2 long lines"));

  (* SPC-002: Whitespace-only line *)
  run "SPC-002 fires on space line" (fun tag ->
      expect (fires "SPC-002" "text\n   \nmore") (tag ^ ": spaces"));
  run "SPC-002 fires on tab line" (fun tag ->
      expect (fires "SPC-002" "text\n\t\nmore") (tag ^ ": tab"));
  run "SPC-002 does not fire on empty line" (fun tag ->
      expect (does_not_fire "SPC-002" "text\n\nmore") (tag ^ ": empty line ok"));
  run "SPC-002 clean" (fun tag ->
      expect (does_not_fire "SPC-002" "all content\nhere") (tag ^ ": clean"));

  (* SPC-003: Mixed tab/space indent *)
  run "SPC-003 fires" (fun tag ->
      expect (fires "SPC-003" "\t code") (tag ^ ": tab then space"));
  run "SPC-003 fires reverse" (fun tag ->
      expect (fires "SPC-003" " \tcode") (tag ^ ": space then tab"));
  run "SPC-003 clean tabs only" (fun tag ->
      expect (does_not_fire "SPC-003" "\t\tcode") (tag ^ ": tabs only"));
  run "SPC-003 clean spaces only" (fun tag ->
      expect (does_not_fire "SPC-003" "    code") (tag ^ ": spaces only"));

  (* SPC-004: Bare CR without LF *)
  run "SPC-004 fires on bare CR" (fun tag ->
      expect (fires "SPC-004" "line1\rline2") (tag ^ ": bare CR"));
  run "SPC-004 ok with CRLF" (fun tag ->
      expect (does_not_fire "SPC-004" "line1\r\nline2") (tag ^ ": CRLF ok"));
  run "SPC-004 clean" (fun tag ->
      expect (does_not_fire "SPC-004" "line1\nline2") (tag ^ ": LF only"));

  (* SPC-005: Trailing tab at end of line *)
  run "SPC-005 fires" (fun tag ->
      expect (fires "SPC-005" "text\t\nmore") (tag ^ ": trailing tab"));
  run "SPC-005 fires at EOF" (fun tag ->
      expect (fires "SPC-005" "text\t") (tag ^ ": trailing tab at EOF"));
  run "SPC-005 clean" (fun tag ->
      expect (does_not_fire "SPC-005" "text\nmore") (tag ^ ": clean"));

  (* SPC-006: Indentation mixes spaces and tabs (specifically tab then space) *)
  run "SPC-006 fires on tab-then-space" (fun tag ->
      expect (fires "SPC-006" "\t code") (tag ^ ": tab then space"));
  run "SPC-006 clean on space-then-tab" (fun tag ->
      (* SPC-006 specifically detects space AFTER tab, not space BEFORE tab *)
      expect
        (does_not_fire "SPC-006" "  \tcode")
        (tag ^ ": space-tab ok for 006"));

  (* SPC-012: BOM not at file start *)
  run "SPC-012 fires on interior BOM" (fun tag ->
      expect (fires "SPC-012" "text\xef\xbb\xbfmore") (tag ^ ": interior BOM"));
  run "SPC-012 ok at start" (fun tag ->
      expect
        (does_not_fire "SPC-012" "\xef\xbb\xbffile start")
        (tag ^ ": start BOM ok"));
  run "SPC-012 fires on extra BOM after start" (fun tag ->
      expect
        (fires "SPC-012" "\xef\xbb\xbfstart\xef\xbb\xbfextra")
        (tag ^ ": extra fires"));

  (* SPC-024: Leading spaces on blank line *)
  run "SPC-024 fires" (fun tag ->
      expect (fires "SPC-024" "text\n   \nmore") (tag ^ ": spaces on blank"));
  run "SPC-024 clean" (fun tag ->
      expect (does_not_fire "SPC-024" "text\n\nmore") (tag ^ ": empty line ok"));

  (* SPC-028: Multiple consecutive ~~ (non-breaking spaces) *)
  run "SPC-028 fires" (fun tag ->
      expect (fires "SPC-028" "use~~here") (tag ^ ": double tilde"));
  run "SPC-028 fires triple" (fun tag ->
      expect (fires "SPC-028" "use~~~here") (tag ^ ": triple tilde"));
  run "SPC-028 clean single" (fun tag ->
      expect (does_not_fire "SPC-028" "use~single") (tag ^ ": single ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-062: Literal backslash in text
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-062 fires on \\\\ in text" (fun tag ->
      expect (fires "TYPO-062" "text \\\\ more") (tag ^ ": should fire"));
  run "TYPO-062 does not fire on \\\\[ at line start" (fun tag ->
      (* \\[2pt] is a linebreak with optional arg; the \\ before [ should not
         fire. However, strip_math_segments sees \[ as display math. So we test
         the pattern in isolation: backslash-backslash-bracket at end. *)
      expect
        (does_not_fire "TYPO-062" "end of line\\\\[2pt]")
        (tag ^ ": \\\\[ ok"));
  run "TYPO-062 does not fire on \\\\*" (fun tag ->
      expect (does_not_fire "TYPO-062" "end of line\\\\*") (tag ^ ": \\\\* ok"));
  run "TYPO-062 does not fire in math" (fun tag ->
      expect
        (does_not_fire "TYPO-062" "$a \\\\ b$")
        (tag ^ ": math mode excluded"));
  run "TYPO-062 clean" (fun tag ->
      expect (does_not_fire "TYPO-062" "no backslashes here") (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════
     Additional count verification and edge case tests
     ══════════════════════════════════════════════════════════════════════ *)

  (* ENC-007: count verification *)
  run "ENC-007 count=3" (fun tag ->
      expect
        (fires_with_count "ENC-007" "\xe2\x80\x8b\xe2\x80\x8b\xe2\x80\x8b" 3)
        (tag ^ ": three ZWS"));

  (* ENC-017: count for multiple soft hyphens *)
  run "ENC-017 count=2" (fun tag ->
      expect
        (fires_with_count "ENC-017" "hy\xc2\xadphen\xc2\xadated" 2)
        (tag ^ ": count=2"));

  (* ENC-021: count for multiple word joiners *)
  run "ENC-021 count=2" (fun tag ->
      expect
        (fires_with_count "ENC-021" "\xe2\x81\xa0a\xe2\x81\xa0b" 2)
        (tag ^ ": count=2"));

  (* CHAR-006: boundary — only backspace, not other control chars *)
  run "CHAR-006 does not fire on tab" (fun tag ->
      expect
        (does_not_fire "CHAR-006" "text\there")
        (tag ^ ": tab is not backspace"));

  (* CHAR-007: boundary — bell only *)
  run "CHAR-007 count=2" (fun tag ->
      expect (fires_with_count "CHAR-007" "\x07\x07" 2) (tag ^ ": count=2"));

  (* CHAR-009: boundary — only DEL, not other high ASCII *)
  run "CHAR-009 count=2" (fun tag ->
      expect (fires_with_count "CHAR-009" "\x7f\x7f" 2) (tag ^ ": count=2"));

  (* CHAR-021: BOM at very start = ok, anywhere else = fires *)
  run "CHAR-021 count for 2 interior BOMs" (fun tag ->
      expect
        (fires_with_count "CHAR-021"
           "\xef\xbb\xbfstart\xef\xbb\xbfmid\xef\xbb\xbfend" 2)
        (tag ^ ": 2 interior BOMs"));

  (* SPC-001: very long line with multiple normal lines *)
  run "SPC-001 count=1 for one long line" (fun tag ->
      let input = "short\n" ^ String.make 130 'x' ^ "\nshort" in
      expect (fires_with_count "SPC-001" input 1) (tag ^ ": count=1"));

  (* SPC-002: count verification *)
  run "SPC-002 count=2 for two ws lines" (fun tag ->
      expect
        (fires_with_count "SPC-002" "text\n   \nmore\n  \t  \nend" 2)
        (tag ^ ": count=2"));

  (* SPC-003: boundary — tab only indent should NOT fire *)
  run "SPC-003 does not fire on pure tab indent" (fun tag ->
      expect (does_not_fire "SPC-003" "\t\tcode") (tag ^ ": pure tabs ok"));

  (* SPC-004: count for multiple bare CRs *)
  run "SPC-004 count=2" (fun tag ->
      expect (fires_with_count "SPC-004" "a\rb\rc" 2) (tag ^ ": count=2"));

  (* SPC-005: count for multiple trailing tab lines *)
  run "SPC-005 count=2" (fun tag ->
      expect (fires_with_count "SPC-005" "a\t\nb\t\nc" 2) (tag ^ ": count=2"));

  (* SPC-012: count for multiple interior BOMs *)
  run "SPC-012 count for 2 interior BOMs" (fun tag ->
      expect
        (fires_with_count "SPC-012"
           "\xef\xbb\xbfstart\xef\xbb\xbfmid\xef\xbb\xbfend" 2)
        (tag ^ ": count=2"));

  (* SPC-028: count for ~~~ (3 tildes = 2 occurrences of ~~) *)
  run "SPC-028 count for ~~~" (fun tag ->
      expect
        (fires_with_count "SPC-028" "use~~~here" 2)
        (tag ^ ": triple tilde count=2"));

  (* ══════════════════════════════════════════════════════════════════════ Edge
     cases
     ══════════════════════════════════════════════════════════════════════ *)

  (* Empty input triggers nothing *)
  run "empty input" (fun tag ->
      let results = Validators.run_all "" in
      let enc_char_spc =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            (String.length id >= 4 && String.sub id 0 4 = "ENC-")
            || (String.length id >= 5 && String.sub id 0 5 = "CHAR-")
            || (String.length id >= 4 && String.sub id 0 4 = "SPC-")
            || id = "TYPO-062")
          results
      in
      expect (enc_char_spc = []) (tag ^ ": no ENC/CHAR/SPC on empty"));

  (* Clean LaTeX triggers no ENC/CHAR/SPC rules *)
  run "clean LaTeX" (fun tag ->
      let src =
        "\\documentclass{article}\n\
         \\begin{document}\n\
         Hello, world!\n\
         \\end{document}\n"
      in
      let results = Validators.run_all src in
      let enc_char_spc =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            (String.length id >= 4 && String.sub id 0 4 = "ENC-")
            || (String.length id >= 5 && String.sub id 0 5 = "CHAR-")
            || (String.length id >= 4 && String.sub id 0 4 = "SPC-"))
          results
      in
      expect (enc_char_spc = []) (tag ^ ": clean LaTeX"));

  (* precondition_of_rule_id dispatches correctly *)
  run "layer dispatch ENC" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "ENC-007" = L0)
        (tag ^ ": ENC -> L0"));
  run "layer dispatch CHAR" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CHAR-006" = L0)
        (tag ^ ": CHAR -> L0"));
  run "layer dispatch SPC" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "SPC-001" = L0)
        (tag ^ ": SPC -> L0"));

  if !fails > 0 then (
    Printf.eprintf "[enc-char-spc] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[enc-char-spc] PASS %d cases\n%!" !cases
