(** Unit tests for all TYPO validator rules (TYPO-001 through TYPO-063). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[typo] FAIL: %s\n%!" msg;
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
  (* Enable pilot validators so TYPO rules are loaded *)
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-001: ASCII straight double quotes
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-001 fires on straight quote" (fun tag ->
      expect (fires "TYPO-001" "The \"quick\" fox") (tag ^ ": should fire"));
  run "TYPO-001 count" (fun tag ->
      expect
        (fires_with_count "TYPO-001" "He said \"hi\" and \"bye\"" 4)
        (tag ^ ": count=4"));
  run "TYPO-001 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-001" "The quick brown fox")
        (tag ^ ": no quotes"));
  run "TYPO-001 in math ignored" (fun tag ->
      expect (does_not_fire "TYPO-001" "$x = \"y\"$") (tag ^ ": math stripped"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-002: Double hyphen --
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-002 fires on --" (fun tag ->
      expect (fires "TYPO-002" "This--that") (tag ^ ": should fire"));
  run "TYPO-002 count" (fun tag ->
      expect (fires_with_count "TYPO-002" "a--b c--d" 2) (tag ^ ": count=2"));
  run "TYPO-002 clean" (fun tag ->
      expect (does_not_fire "TYPO-002" "This is normal text") (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-003: Triple hyphen ---
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-003 fires on ---" (fun tag ->
      expect (fires "TYPO-003" "This---that") (tag ^ ": should fire"));
  run "TYPO-003 clean" (fun tag ->
      expect (does_not_fire "TYPO-003" "Normal text here") (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-004: TeX double back-tick quotes `` and ''
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-004 fires on backtick quotes" (fun tag ->
      expect (fires "TYPO-004" "``quoted''") (tag ^ ": should fire"));
  run "TYPO-004 fires on '' alone" (fun tag ->
      expect (fires "TYPO-004" "He said ''hello''") (tag ^ ": single-quotes"));
  run "TYPO-004 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-004" "Normal text without TeX quotes")
        (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-005: Ellipsis as three periods ...
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-005 fires on ..." (fun tag ->
      expect (fires "TYPO-005" "Wait... and see") (tag ^ ": should fire"));
  run "TYPO-005 clean" (fun tag ->
      expect (does_not_fire "TYPO-005" "Wait\\dots and see") (tag ^ ": clean"));
  run "TYPO-005 in math ignored" (fun tag ->
      expect (does_not_fire "TYPO-005" "$a + ... + z$") (tag ^ ": math stripped"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-006: Tab character U+0009
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-006 fires on tab" (fun tag ->
      expect (fires "TYPO-006" "hello\tworld") (tag ^ ": should fire"));
  run "TYPO-006 count" (fun tag ->
      expect (fires_with_count "TYPO-006" "a\tb\tc" 2) (tag ^ ": count=2"));
  run "TYPO-006 clean" (fun tag ->
      expect (does_not_fire "TYPO-006" "hello world") (tag ^ ": no tabs"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-007: Trailing spaces at end of line
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-007 fires on trailing space" (fun tag ->
      expect (fires "TYPO-007" "text   \nmore") (tag ^ ": should fire"));
  run "TYPO-007 clean" (fun tag ->
      expect (does_not_fire "TYPO-007" "text\nmore\n") (tag ^ ": no trailing"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-008: Multiple consecutive blank lines (>2)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-008 fires on 3 newlines" (fun tag ->
      expect (fires "TYPO-008" "text\n\n\nmore") (tag ^ ": should fire"));
  run "TYPO-008 clean with 2 newlines" (fun tag ->
      expect
        (does_not_fire "TYPO-008" "text\n\nmore")
        (tag ^ ": two newlines ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-009: Non-breaking space ~ at line start
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-009 fires on ~ at start" (fun tag ->
      expect (fires "TYPO-009" "~Text here") (tag ^ ": start of string"));
  run "TYPO-009 fires on newline tilde" (fun tag ->
      expect (fires "TYPO-009" "line\n~next") (tag ^ ": after newline"));
  run "TYPO-009 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-009" "some~text here")
        (tag ^ ": mid-line tilde ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-010: Space before punctuation
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-010 fires on space-comma" (fun tag ->
      expect (fires "TYPO-010" "Text , here") (tag ^ ": should fire"));
  run "TYPO-010 fires on space-period" (fun tag ->
      expect (fires "TYPO-010" "End . Next") (tag ^ ": period"));
  run "TYPO-010 fires on space-semicolon" (fun tag ->
      expect (fires "TYPO-010" "A ; B") (tag ^ ": semicolon"));
  run "TYPO-010 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-010" "Text, here. Next; more: things? ok!")
        (tag ^ ": no space before punct"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-011: Missing thin space before differential d in integrals
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-011 fires on integral without \\," (fun tag ->
      expect (fires "TYPO-011" "$\\int f(x)dx$") (tag ^ ": should fire"));
  run "TYPO-011 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-011" "$\\int f(x)\\,dx$")
        (tag ^ ": has thin space"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-012: Straight apostrophe for minutes/feet
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-012 fires on digit-apostrophe" (fun tag ->
      expect (fires "TYPO-012" "The board is 6' long") (tag ^ ": should fire"));
  run "TYPO-012 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-012" "The word 'hello' is common")
        (tag ^ ": no digit before quote"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-013: ASCII back-tick as opening quote
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-013 fires on single backtick" (fun tag ->
      expect (fires "TYPO-013" "He said `hello' to me") (tag ^ ": should fire"));
  run "TYPO-013 clean with double backtick" (fun tag ->
      expect
        (does_not_fire "TYPO-013" "He said ``hello'' to me")
        (tag ^ ": double backtick is TeX quote"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-014: Space before percent sign (relocated from old TYPO-028)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-014 fires on space-percent" (fun tag ->
      expect (fires "TYPO-014" "50 %") (tag ^ ": should fire"));
  run "TYPO-014 clean" (fun tag ->
      expect (does_not_fire "TYPO-014" "50%") (tag ^ ": no space"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-015: Double \% in source
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-015 fires on double percent escape" (fun tag ->
      expect (fires "TYPO-015" "Value is 50\\%\\%") (tag ^ ": should fire"));
  run "TYPO-015 clean" (fun tag ->
      expect (does_not_fire "TYPO-015" "Value is 50\\%") (tag ^ ": single ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-016: ~ missing before \cite / \ref
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-016 fires on space before cite" (fun tag ->
      expect (fires "TYPO-016" "See \\cite{foo}") (tag ^ ": should fire"));
  run "TYPO-016 clean with tilde" (fun tag ->
      expect
        (does_not_fire "TYPO-016" "See~\\cite{foo}")
        (tag ^ ": tilde is correct"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-017: TeX accent commands in text
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-017 fires on TeX accent" (fun tag ->
      expect (fires "TYPO-017" "caf\\'{e}") (tag ^ ": should fire"));
  run "TYPO-017 clean" (fun tag ->
      expect (does_not_fire "TYPO-017" "café") (tag ^ ": UTF-8 ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-018: Multiple consecutive spaces (relocated from old TYPO-011)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-018 fires on double space" (fun tag ->
      expect (fires "TYPO-018" "Text  with  spaces") (tag ^ ": should fire"));
  run "TYPO-018 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-018" "Normal text here")
        (tag ^ ": single spaces"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-019: Comma splice — DEFERRED (NLP)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-019 never fires (deferred)" (fun tag ->
      expect
        (does_not_fire "TYPO-019" "Any text here, it should not fire")
        (tag ^ ": NLP deferred"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-020: Sentence without ending punctuation — DEFERRED (NLP)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-020 never fires (deferred)" (fun tag ->
      expect
        (does_not_fire "TYPO-020" "This sentence has no period")
        (tag ^ ": NLP deferred"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-021: Capital letter after ellipsis without space
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-021 fires on ellipsis-capital" (fun tag ->
      expect (fires "TYPO-021" "Wait...Then go") (tag ^ ": should fire"));
  run "TYPO-021 clean" (fun tag ->
      expect (does_not_fire "TYPO-021" "Wait... Then go") (tag ^ ": has space"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-022: Space before closing punctuation (relocated from old TYPO-012)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-022 fires on space-paren" (fun tag ->
      expect (fires "TYPO-022" "(text )") (tag ^ ": should fire"));
  run "TYPO-022 fires on space-bracket" (fun tag ->
      expect (fires "TYPO-022" "[text ]") (tag ^ ": should fire"));
  run "TYPO-022 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-022" "(text) [ok]")
        (tag ^ ": no trailing space"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-023: ASCII & outside tabular env
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-023 fires on bare ampersand" (fun tag ->
      expect (fires "TYPO-023" "Tom & Jerry are friends") (tag ^ ": should fire"));
  run "TYPO-023 clean with escaped" (fun tag ->
      expect
        (does_not_fire "TYPO-023" "Tom \\& Jerry are friends")
        (tag ^ ": escaped ok"));
  run "TYPO-023 clean inside tabular" (fun tag ->
      expect
        (does_not_fire "TYPO-023" "\\begin{tabular}{ll} a & b \\end{tabular}")
        (tag ^ ": inside tabular ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-024: Dangling dash at line end
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-024 fires on dash at EOL" (fun tag ->
      expect
        (fires "TYPO-024" "This is a long-\nwinded sentence")
        (tag ^ ": should fire"));
  run "TYPO-024 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-024" "This is a long-winded sentence")
        (tag ^ ": dash mid-line ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-025: Space before en-dash in number range
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-025 fires on spaced en-dash range" (fun tag ->
      expect (fires "TYPO-025" "pages 5 --10") (tag ^ ": should fire"));
  run "TYPO-025 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-025" "pages 5--10")
        (tag ^ ": no space before dash"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-026: Wrong dash in page range
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-026 fires on unicode en-dash between digits" (fun tag ->
      expect (fires "TYPO-026" "pages 5\xe2\x80\x9310") (tag ^ ": should fire"));
  run "TYPO-026 clean with ASCII dash" (fun tag ->
      expect (does_not_fire "TYPO-026" "pages 5--10") (tag ^ ": ASCII -- ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-027: Multiple exclamation marks (relocated from old TYPO-016)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-027 fires on !!" (fun tag ->
      expect (fires "TYPO-027" "Wow!!") (tag ^ ": should fire"));
  run "TYPO-027 fires on !!!" (fun tag ->
      expect (fires "TYPO-027" "Amazing!!!") (tag ^ ": should fire"));
  run "TYPO-027 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-027" "Wow! Really!")
        (tag ^ ": single exclamation ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-028: Use of $$ display math delimiter
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-028 fires on $$ delimiter" (fun tag ->
      expect (fires "TYPO-028" "$$x^2$$") (tag ^ ": should fire"));
  run "TYPO-028 clean with \\[" (fun tag ->
      expect
        (does_not_fire "TYPO-028" "\\[x^2\\]")
        (tag ^ ": modern delimiter ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-029: Non-breaking space after \ref missing
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-029 fires on ref-space" (fun tag ->
      expect (fires "TYPO-029" "\\ref{fig:1} shows") (tag ^ ": should fire"));
  run "TYPO-029 clean with tilde" (fun tag ->
      expect (does_not_fire "TYPO-029" "\\ref{fig:1}~shows") (tag ^ ": tilde ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-030: UK spelling inconsistency — DEFERRED (NLP)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-030 never fires (deferred)" (fun tag ->
      expect
        (does_not_fire "TYPO-030" "colour color behaviour behavior")
        (tag ^ ": NLP deferred"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-031: American punctuation placement — DEFERRED (NLP)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-031 never fires (deferred)" (fun tag ->
      expect
        (does_not_fire "TYPO-031" {|He said "hello," she replied.|})
        (tag ^ ": NLP deferred"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-032: Comma before \cite
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-032 fires on comma-cite" (fun tag ->
      expect (fires "TYPO-032" "as shown,\\cite{foo}") (tag ^ ": should fire"));
  run "TYPO-032 fires on comma-space-cite" (fun tag ->
      expect (fires "TYPO-032" "as shown, \\cite{foo}") (tag ^ ": should fire"));
  run "TYPO-032 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-032" "as shown~\\cite{foo}")
        (tag ^ ": tilde ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-033: Abbreviation et.al without space
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-033 fires on et.al" (fun tag ->
      expect (fires "TYPO-033" "Smith et.al") (tag ^ ": should fire"));
  run "TYPO-033 clean" (fun tag ->
      expect (does_not_fire "TYPO-033" "Smith et al.") (tag ^ ": correct form"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-034: Spurious space before \footnote
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-034 fires on space-footnote" (fun tag ->
      expect (fires "TYPO-034" "Text \\footnote{note}") (tag ^ ": should fire"));
  run "TYPO-034 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-034" "Text\\footnote{note}")
        (tag ^ ": no space"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-035: Space before French punctuation
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-035 fires on space-semicolon" (fun tag ->
      expect (fires "TYPO-035" "Word ;") (tag ^ ": should fire"));
  run "TYPO-035 fires on space-colon" (fun tag ->
      expect (fires "TYPO-035" "Word :") (tag ^ ": colon"));
  run "TYPO-035 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-035" "Word; more: stuff")
        (tag ^ ": no space before"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-036: Suspicious consecutive capitals (shouting)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-036 fires on all-caps" (fun tag ->
      expect
        (fires "TYPO-036" "THIS IS SHOUTING at you")
        (tag ^ ": 3+ caps words"));
  run "TYPO-036 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-036" "This Is Normal Case Text")
        (tag ^ ": mixed case ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-037: Space before comma
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-037 fires on space-comma" (fun tag ->
      expect (fires "TYPO-037" "Word , next") (tag ^ ": should fire"));
  run "TYPO-037 clean" (fun tag ->
      expect (does_not_fire "TYPO-037" "Word, next") (tag ^ ": no space"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-038: Bare email address
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-038 fires on bare email" (fun tag ->
      expect
        (fires "TYPO-038" "Contact user@example.com for info")
        (tag ^ ": should fire"));
  run "TYPO-038 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-038" "Contact the admin for info")
        (tag ^ ": no email"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-039: URL without \url{}
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-039 fires on bare URL" (fun tag ->
      expect
        (fires "TYPO-039" "See https://example.com/path for details")
        (tag ^ ": should fire"));
  run "TYPO-039 fires on http" (fun tag ->
      expect (fires "TYPO-039" "Visit http://example.org") (tag ^ ": http"));
  run "TYPO-039 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-039" "See the website for details")
        (tag ^ ": no URL"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-040: Inline math exceeds 80 characters
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-040 fires on long math" (fun tag ->
      let long_math = "$" ^ String.make 81 'x' ^ "$" in
      expect (fires "TYPO-040" long_math) (tag ^ ": should fire"));
  run "TYPO-040 clean short math" (fun tag ->
      expect (does_not_fire "TYPO-040" "$x + y = z$") (tag ^ ": short math ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-041: Incorrect spacing around \ldots
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-041 fires on .\\ldots" (fun tag ->
      expect (fires "TYPO-041" "a.\\ldots") (tag ^ ": period-ldots"));
  run "TYPO-041 fires on \\ldots." (fun tag ->
      expect (fires "TYPO-041" "\\ldots.b") (tag ^ ": ldots-period"));
  run "TYPO-041 fires on ,\\ldots" (fun tag ->
      expect (fires "TYPO-041" "a,\\ldots") (tag ^ ": comma-ldots"));
  run "TYPO-041 clean" (fun tag ->
      expect (does_not_fire "TYPO-041" "a \\ldots b") (tag ^ ": properly spaced"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-042: Multiple consecutive question marks ??
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-042 fires on ??" (fun tag ->
      expect (fires "TYPO-042" "What??") (tag ^ ": should fire"));
  run "TYPO-042 clean" (fun tag ->
      expect (does_not_fire "TYPO-042" "What? How?") (tag ^ ": single ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-043: Smart quotes detected (curly Unicode quotes)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-043 fires on left double curly" (fun tag ->
      expect (fires "TYPO-043" "text \xe2\x80\x9c here") (tag ^ ": U+201C"));
  run "TYPO-043 fires on right double curly" (fun tag ->
      expect (fires "TYPO-043" "text \xe2\x80\x9d here") (tag ^ ": U+201D"));
  run "TYPO-043 fires on left single curly" (fun tag ->
      expect (fires "TYPO-043" "text \xe2\x80\x98 here") (tag ^ ": U+2018"));
  run "TYPO-043 fires on right single curly" (fun tag ->
      expect (fires "TYPO-043" "text \xe2\x80\x99 here") (tag ^ ": U+2019"));
  run "TYPO-043 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-043" "Normal ASCII text")
        (tag ^ ": no curly quotes"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-045: Non-ASCII punctuation in math mode
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-045 fires on non-ascii in math" (fun tag ->
      (* U+00E9 = é = \xc3\xa9 — two bytes, both >= 0x80 *)
      expect (fires "TYPO-045" "$\xc3\xa9$") (tag ^ ": non-ASCII in $...$"));
  run "TYPO-045 clean ascii math" (fun tag ->
      expect (does_not_fire "TYPO-045" "$x + y = z$") (tag ^ ": ASCII math ok"));
  run "TYPO-045 non-ascii outside math" (fun tag ->
      expect
        (does_not_fire "TYPO-045" "\xc3\xa9 is outside math")
        (tag ^ ": outside math ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-046: Use of \begin{math}
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-046 fires on begin-math" (fun tag ->
      expect
        (fires "TYPO-046" "\\begin{math}x=y\\end{math}")
        (tag ^ ": should fire"));
  run "TYPO-046 clean" (fun tag ->
      expect (does_not_fire "TYPO-046" "$x=y$") (tag ^ ": dollar math ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-047: Starred \section*
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-047 fires on section*" (fun tag ->
      expect (fires "TYPO-047" "\\section*{Title}") (tag ^ ": should fire"));
  run "TYPO-047 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-047" "\\section{Title}")
        (tag ^ ": numbered section ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-048: En-dash used as minus in text
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-048 fires on en-dash in text" (fun tag ->
      expect
        (fires "TYPO-048" "Value \xe2\x80\x93 here")
        (tag ^ ": en-dash in text"));
  run "TYPO-048 clean in math" (fun tag ->
      expect
        (does_not_fire "TYPO-048" "$a \xe2\x80\x93 b$")
        (tag ^ ": math stripped"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-049: Space after opening curly quote
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-049 fires on left-dquote-space" (fun tag ->
      expect (fires "TYPO-049" "\xe2\x80\x9c text") (tag ^ ": U+201C + space"));
  run "TYPO-049 fires on left-squote-space" (fun tag ->
      expect (fires "TYPO-049" "\xe2\x80\x98 text") (tag ^ ": U+2018 + space"));
  run "TYPO-049 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-049" "\xe2\x80\x9ctext\xe2\x80\x9d")
        (tag ^ ": no space after opening"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-051: Thin space U+2009
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-051 fires on thin space" (fun tag ->
      expect (fires "TYPO-051" "text\xe2\x80\x89here") (tag ^ ": U+2009"));
  run "TYPO-051 clean" (fun tag ->
      expect (does_not_fire "TYPO-051" "text here") (tag ^ ": normal space"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-052: Unescaped < or > in text
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-052 fires on <" (fun tag ->
      expect (fires "TYPO-052" "2<3 in text") (tag ^ ": less than"));
  run "TYPO-052 fires on >" (fun tag ->
      expect (fires "TYPO-052" "5>3 in text") (tag ^ ": greater than"));
  run "TYPO-052 clean in math" (fun tag ->
      expect
        (does_not_fire "TYPO-052" "$2<3$ and $5>3$")
        (tag ^ ": math stripped"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-053: Unicode midline ellipsis U+22EF
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-053 fires on U+22EF" (fun tag ->
      expect (fires "TYPO-053" "a\xe2\x8b\xafb") (tag ^ ": midline ellipsis"));
  run "TYPO-053 clean" (fun tag ->
      expect (does_not_fire "TYPO-053" "a\\cdots b") (tag ^ ": macro ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-054: En-dash adjacent to letter
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-054 fires on letter-endash-letter" (fun tag ->
      expect
        (fires "TYPO-054" "word\xe2\x80\x93word")
        (tag ^ ": no space around en-dash"));
  run "TYPO-054 clean spaced" (fun tag ->
      expect
        (does_not_fire "TYPO-054" "word \xe2\x80\x93 word")
        (tag ^ ": spaced en-dash ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-055: Consecutive thin spaces \,\,
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-055 fires on \\,\\," (fun tag ->
      expect (fires "TYPO-055" "text\\,\\,more") (tag ^ ": should fire"));
  run "TYPO-055 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-055" "text\\,more")
        (tag ^ ": single thinspace ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-056: Legacy TeX accent command
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-056 fires on accent" (fun tag ->
      expect (fires "TYPO-056" "Caf\\'{e}") (tag ^ ": acute accent"));
  run "TYPO-056 fires on grave" (fun tag ->
      expect (fires "TYPO-056" "\\`{a}") (tag ^ ": grave accent"));
  run "TYPO-056 fires on umlaut" (fun tag ->
      expect (fires "TYPO-056" "\\\"{o}") (tag ^ ": umlaut"));
  run "TYPO-056 clean" (fun tag ->
      expect (does_not_fire "TYPO-056" "Caf\xc3\xa9") (tag ^ ": UTF-8 char ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-057: Number adjacent to degree symbol
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-057 fires on digit-degree" (fun tag ->
      expect (fires "TYPO-057" "45\xc2\xb0") (tag ^ ": 45 degree"));
  run "TYPO-057 clean spaced" (fun tag ->
      expect
        (does_not_fire "TYPO-057" "45\\,\xc2\xb0")
        (tag ^ ": thin space before degree"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-058: Greek homograph letters in Latin text
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-058 fires on alpha" (fun tag ->
      expect (fires "TYPO-058" "text \xce\xb1 here") (tag ^ ": Greek alpha"));
  run "TYPO-058 fires on epsilon" (fun tag ->
      expect (fires "TYPO-058" "text \xce\xb5 here") (tag ^ ": Greek epsilon"));
  run "TYPO-058 fires on omicron" (fun tag ->
      expect (fires "TYPO-058" "text \xce\xbf here") (tag ^ ": Greek omicron"));
  run "TYPO-058 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-058" "Normal Latin text")
        (tag ^ ": no Greek homoglyphs"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-061: Unicode multiplication sign in text
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-061 fires on multiply" (fun tag ->
      expect (fires "TYPO-061" "2\xc3\x973 in text") (tag ^ ": U+00D7"));
  run "TYPO-061 clean in math" (fun tag ->
      expect (does_not_fire "TYPO-061" "$2\xc3\x973$") (tag ^ ": math stripped"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-062: Literal backslash in text (already partially tested, but adding
     comprehensive coverage)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-062 fires on bare \\\\" (fun tag ->
      expect (fires "TYPO-062" "Path\\\\file") (tag ^ ": should fire"));
  run "TYPO-062 does not fire on \\\\[" (fun tag ->
      expect (does_not_fire "TYPO-062" "text\\\\[2pt]") (tag ^ ": line break ok"));
  run "TYPO-062 does not fire on \\\\*" (fun tag ->
      expect
        (does_not_fire "TYPO-062" "text\\\\*")
        (tag ^ ": starred line break ok"));
  run "TYPO-062 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-062" "Normal text without backslash")
        (tag ^ ": clean"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-063: Non-breaking hyphen U+2011
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-063 fires on nb-hyphen" (fun tag ->
      expect (fires "TYPO-063" "text\xe2\x80\x91here") (tag ^ ": U+2011"));
  run "TYPO-063 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-063" "text-here")
        (tag ^ ": standard hyphen ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-060: Smart quotes inside lstlisting/verbatim
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-060 fires on curly quote in lstlisting" (fun tag ->
      expect
        (fires "TYPO-060"
           "\\begin{lstlisting}\n\
            print(\xe2\x80\x9chi\xe2\x80\x9d)\n\
            \\end{lstlisting}")
        (tag ^ ": curly in lstlisting"));
  run "TYPO-060 fires on curly quote in verbatim" (fun tag ->
      expect
        (fires "TYPO-060"
           "\\begin{verbatim}\n\xe2\x80\x98text\xe2\x80\x99\n\\end{verbatim}")
        (tag ^ ": curly in verbatim"));
  run "TYPO-060 count=2 for two curly quotes in lstlisting" (fun tag ->
      expect
        (fires_with_count "TYPO-060"
           "\\begin{lstlisting}\n\xe2\x80\x9c\xe2\x80\x9d\n\\end{lstlisting}" 2)
        (tag ^ ": count=2"));
  run "TYPO-060 does not fire outside lstlisting" (fun tag ->
      expect
        (does_not_fire "TYPO-060" "Normal \xe2\x80\x9ctext\xe2\x80\x9d here")
        (tag ^ ": outside verbatim ok"));
  run "TYPO-060 clean" (fun tag ->
      expect
        (does_not_fire "TYPO-060"
           "\\begin{lstlisting}\nprint(\"hi\")\n\\end{lstlisting}")
        (tag ^ ": ASCII quotes in lstlisting ok"));

  (* ══════════════════════════════════════════════════════════════════════
     Math-mode edge cases for rules using strip_math_segments
     ══════════════════════════════════════════════════════════════════════ *)

  (* TYPO-045: boundary — multiple $ delimiters *)
  run "TYPO-045 fires on non-ascii in second math" (fun tag ->
      expect
        (fires "TYPO-045" "$x$ and $\xc3\xa9$")
        (tag ^ ": second math segment"));
  run "TYPO-045 count=2 for two non-ascii bytes" (fun tag ->
      expect
        (fires_with_count "TYPO-045" "$\xc3\xa9$" 2)
        (tag ^ ": count two bytes of U+00E9"));

  (* TYPO-040: boundary — exactly 80 chars should NOT fire, 81 SHOULD *)
  run "TYPO-040 does not fire at exactly 80 chars" (fun tag ->
      let math80 = "$" ^ String.make 80 'x' ^ "$" in
      expect (does_not_fire "TYPO-040" math80) (tag ^ ": 80 ok"));
  run "TYPO-040 count=2 for two long inline maths" (fun tag ->
      let long1 = "$" ^ String.make 81 'a' ^ "$" in
      let long2 = "$" ^ String.make 90 'b' ^ "$" in
      expect
        (fires_with_count "TYPO-040" (long1 ^ " text " ^ long2) 2)
        (tag ^ ": count=2"));

  (* ══════════════════════════════════════════════════════════════════════
     Additional count verification tests
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-005 count=2 for two ellipses" (fun tag ->
      expect
        (fires_with_count "TYPO-005" "Wait... and also..." 2)
        (tag ^ ": count=2"));
  run "TYPO-007 count=2 for two trailing-space lines" (fun tag ->
      expect
        (fires_with_count "TYPO-007" "text   \nmore   \nend" 2)
        (tag ^ ": count=2"));
  run "TYPO-010 count=2 for two space-before-punct" (fun tag ->
      expect
        (fires_with_count "TYPO-010" "Text , here . too" 2)
        (tag ^ ": count=2"));
  run "TYPO-043 count=4 for all four curly types" (fun tag ->
      expect
        (fires_with_count "TYPO-043"
           "\xe2\x80\x9c \xe2\x80\x9d \xe2\x80\x98 \xe2\x80\x99" 4)
        (tag ^ ": count=4"));
  run "TYPO-052 count=2 for < and >" (fun tag ->
      expect (fires_with_count "TYPO-052" "a<b>c in text" 2) (tag ^ ": count=2"));
  run "TYPO-056 count=2 for two accents" (fun tag ->
      expect
        (fires_with_count "TYPO-056" "Caf\\'{e} and \\`{a}" 2)
        (tag ^ ": count=2"));
  run "TYPO-058 count=3 for three Greek homographs" (fun tag ->
      expect
        (fires_with_count "TYPO-058" "The \xce\xb1 and \xce\xb5 and \xce\xbf" 3)
        (tag ^ ": count=3"));

  (* ══════════════════════════════════════════════════════════════════════
     Boundary condition and tricky-input tests
     ══════════════════════════════════════════════════════════════════════ *)

  (* TYPO-002: count_substring allows overlaps, so "---" matches "--" twice *)
  run "TYPO-002 fires on --- via overlap" (fun tag ->
      expect (fires "TYPO-002" "This---that") (tag ^ ": overlap matches"));

  (* TYPO-008 fires on 4 newlines too *)
  run "TYPO-008 fires on 4 newlines" (fun tag ->
      expect (fires "TYPO-008" "text\n\n\n\nmore") (tag ^ ": four newlines"));

  (* TYPO-009 does not fire on mid-line ~ used as non-breaking space *)
  run "TYPO-009 does not fire on Figure~1" (fun tag ->
      expect
        (does_not_fire "TYPO-009" "See Figure~1 for details")
        (tag ^ ": normal tilde usage"));

  (* TYPO-036 boundary: exactly 3 uppercase words in sequence *)
  run "TYPO-036 fires on exactly 3 uppercase words" (fun tag ->
      expect (fires "TYPO-036" "The ABC DEF GHI method") (tag ^ ": 3 caps words"));
  run "TYPO-036 does not fire on 2 uppercase words" (fun tag ->
      expect
        (does_not_fire "TYPO-036" "Use ABC DEF method")
        (tag ^ ": 2 caps insufficient"));

  (* TYPO-038 count=2 for two emails *)
  run "TYPO-038 count=2" (fun tag ->
      expect
        (fires_with_count "TYPO-038" "Contact a@b.com or c@d.org" 2)
        (tag ^ ": count=2"));

  (* TYPO-039: regex is https?:// so only http/https, not ftp *)
  run "TYPO-039 does not fire on ftp URL" (fun tag ->
      expect
        (does_not_fire "TYPO-039" "See ftp://files.example.com for data")
        (tag ^ ": ftp not matched"));
  run "TYPO-039 count=2 for two URLs" (fun tag ->
      expect
        (fires_with_count "TYPO-039" "Visit http://a.com and https://b.org" 2)
        (tag ^ ": count=2"));

  (* TYPO-046 count includes both begin and end *)
  run "TYPO-046 count=2 for begin+end" (fun tag ->
      expect
        (fires_with_count "TYPO-046" "\\begin{math}x\\end{math}" 2)
        (tag ^ ": count begin+end"));

  (* TYPO-047 count=2 for two starred sections *)
  run "TYPO-047 count=2" (fun tag ->
      expect
        (fires_with_count "TYPO-047" "\\section*{A}\\section*{B}" 2)
        (tag ^ ": count=2"));

  (* TYPO-048 count for multiple en-dashes in text *)
  run "TYPO-048 count=2 for two en-dashes" (fun tag ->
      expect
        (fires_with_count "TYPO-048" "val\xe2\x80\x93ue and oth\xe2\x80\x93er" 2)
        (tag ^ ": count=2"));

  (* TYPO-054 does not fire on number ranges like 1–10 *)
  run "TYPO-054 fires on word-endash-word" (fun tag ->
      expect
        (fires "TYPO-054" "New York\xe2\x80\x93London")
        (tag ^ ": city endash city"));

  (* TYPO-055 count for triple thinspace *)
  run "TYPO-055 count=2 for \\,\\,\\," (fun tag ->
      expect
        (fires_with_count "TYPO-055" "text\\,\\,\\,more" 2)
        (tag ^ ": count=2 for triple"));

  (* TYPO-062 count for multiple bare backslashes *)
  run "TYPO-062 count=2 for two bare backslashes" (fun tag ->
      expect
        (fires_with_count "TYPO-062" "path\\\\file and dir\\\\name" 2)
        (tag ^ ": count=2"));

  (* TYPO-063 count for two nb-hyphens *)
  run "TYPO-063 count=2" (fun tag ->
      expect
        (fires_with_count "TYPO-063" "\xe2\x80\x91one \xe2\x80\x91two" 2)
        (tag ^ ": count=2"));

  (* ══════════════════════════════════════════════════════════════════════
     Realistic LaTeX fragment — multi-rule integration test
     ══════════════════════════════════════════════════════════════════════ *)
  run "Integration: realistic LaTeX triggers expected rules" (fun tag ->
      let doc =
        "\\documentclass{article}\n\
         \\begin{document}\n\n\
         He said \"hello\" and goodbye.  Next sentence.\n\n\
         Contact user@example.com for info.\n\n\
         The value is 50 %.\n\n\
         See https://example.com for details.\n\n\
         \\end{document}\n"
      in
      let results = Validators.run_all doc in
      let has id =
        List.exists (fun (r : Validators.result) -> r.id = id) results
      in
      (* TYPO-001: straight quotes *)
      expect (has "TYPO-001") (tag ^ ": TYPO-001 fires on straight quotes");
      (* TYPO-038: bare email *)
      expect (has "TYPO-038") (tag ^ ": TYPO-038 fires on bare email");
      (* TYPO-039: bare URL *)
      expect (has "TYPO-039") (tag ^ ": TYPO-039 fires on bare URL"));

  run "Clean realistic LaTeX — no TYPO fires" (fun tag ->
      let clean =
        "\\documentclass{article}\n"
        ^ "\\usepackage[utf8]{inputenc}\n"
        ^ "\\begin{document}\n"
        ^ "\n"
        ^ "This is well-formatted.\n"
        ^ "\n"
        ^ "The formula $E = mc^2$ is famous.\n"
        ^ "\n"
        ^ "See~\\cite{einstein1905} for the original paper.\n"
        ^ "\n"
        ^ "\\end{document}\n"
      in
      let results = Validators.run_all clean in
      let typo_results =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 5 && String.sub r.id 0 5 = "TYPO-")
          results
      in
      expect (typo_results = []) (tag ^ ": clean realistic LaTeX, no TYPO"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "Empty input — no TYPO fires" (fun tag ->
      let results = Validators.run_all "" in
      let typo_results =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 5 && String.sub r.id 0 5 = "TYPO-")
          results
      in
      expect (typo_results = []) (tag ^ ": empty input, no TYPO"));

  run "Clean LaTeX — no TYPO fires" (fun tag ->
      let clean =
        "\\documentclass{article}\n\
         \\begin{document}\n\
         Hello world.\n\
         \\end{document}\n"
      in
      let results = Validators.run_all clean in
      let typo_results =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 5 && String.sub r.id 0 5 = "TYPO-")
          results
      in
      expect (typo_results = []) (tag ^ ": clean LaTeX, no TYPO"));

  (* ══════════════════════════════════════════════════════════════════════ Done
     ══════════════════════════════════════════════════════════════════════ *)
  if !fails > 0 then (
    Printf.eprintf "[typo] %d FAILURES in %d cases\n%!" !fails !cases;
    exit 1)
  else Printf.printf "[typo] PASS %d cases\n%!" !cases
