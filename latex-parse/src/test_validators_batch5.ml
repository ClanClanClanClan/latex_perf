(** Unit tests for L0 Batch 5: final non-locale L0 rules. ENC-010, ENC-011,
    ENC-015, MATH-083, SPC-017, SPC-026, TYPO-044, VERB-011 *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[batch5] FAIL: %s\n%!" msg;
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
  (* ══════════════════════════════════════════════════════════════════════
     ENC-010: Non-canonical NFC form
     ══════════════════════════════════════════════════════════════════════ *)

  (* a + combining acute (CC 81) → NFC would be à but here it's decomposed *)
  run "ENC-010 fires on decomposed a-acute" (fun tag ->
      expect (fires "ENC-010" "a\xcc\x81") (tag ^ ": a + combining acute"));
  run "ENC-010 fires on decomposed e-grave" (fun tag ->
      expect (fires "ENC-010" "e\xcc\x80") (tag ^ ": e + combining grave"));
  run "ENC-010 fires on decomposed o-diaeresis" (fun tag ->
      expect (fires "ENC-010" "o\xcc\x88") (tag ^ ": o + combining diaeresis"));
  run "ENC-010 fires on decomposed n-tilde" (fun tag ->
      expect (fires "ENC-010" "n\xcc\x83") (tag ^ ": n + combining tilde"));
  run "ENC-010 fires on decomposed a-circumflex" (fun tag ->
      expect (fires "ENC-010" "a\xcc\x82") (tag ^ ": a + combining circumflex"));
  run "ENC-010 fires on decomposed c-cedilla" (fun tag ->
      expect (fires "ENC-010" "c\xcc\xa7") (tag ^ ": c + combining cedilla"));
  run "ENC-010 count=2" (fun tag ->
      expect
        (fires_with_count "ENC-010" "a\xcc\x81 and e\xcc\x80" 2)
        (tag ^ ": count=2"));
  run "ENC-010 uppercase letter" (fun tag ->
      expect (fires "ENC-010" "A\xcc\x81") (tag ^ ": uppercase A + acute"));
  run "ENC-010 clean: precomposed NFC" (fun tag ->
      expect
        (does_not_fire "ENC-010" "\xc3\xa9")
        (tag ^ ": precomposed e-acute (NFC)"));
  run "ENC-010 clean: ASCII only" (fun tag ->
      expect (does_not_fire "ENC-010" "Hello World") (tag ^ ": plain ASCII"));
  run "ENC-010 clean: combining after non-ASCII" (fun tag ->
      (* CC 80 after a non-ASCII byte should not fire — only ASCII letters *)
      expect
        (does_not_fire "ENC-010" "\xc3\xa9\xcc\x80")
        (tag ^ ": combining after non-ASCII base"));

  (* ══════════════════════════════════════════════════════════════════════
     ENC-011: Byte sequence resembles MacRoman encoding
     ══════════════════════════════════════════════════════════════════════ *)

  (* 0x8E is MacRoman e-acute; as a standalone byte in 0x80-0x9F range, it
     suggests MacRoman encoding *)
  run "ENC-011 fires on isolated 0x8E" (fun tag ->
      expect (fires "ENC-011" "hello\x8eworld") (tag ^ ": 0x8E"));
  run "ENC-011 fires on isolated 0x92" (fun tag ->
      expect (fires "ENC-011" "it\x92s") (tag ^ ": 0x92 right quote"));
  run "ENC-011 fires on isolated 0x85" (fun tag ->
      expect (fires "ENC-011" "test\x85abc") (tag ^ ": 0x85 ellipsis"));
  run "ENC-011 count=3" (fun tag ->
      expect
        (fires_with_count "ENC-011" "a\x80b\x90c\x9fd" 3)
        (tag ^ ": count=3"));
  run "ENC-011 clean: valid UTF-8 continuation" (fun tag ->
      (* C3 A9 is e-acute in UTF-8: C3 is lead byte, A9 is continuation. A9 is
         in 0x80-0x9F range but preceded by valid lead byte C3 *)
      expect (does_not_fire "ENC-011" "\xc3\xa9") (tag ^ ": valid UTF-8 e-acute"));
  run "ENC-011 clean: pure ASCII" (fun tag ->
      expect (does_not_fire "ENC-011" "Hello World 123") (tag ^ ": ASCII only"));
  run "ENC-011 clean: valid high UTF-8" (fun tag ->
      (* E2 80 99 is right single quotation mark U+2019 — valid UTF-8 *)
      expect
        (does_not_fire "ENC-011" "it\xe2\x80\x99s")
        (tag ^ ": valid UTF-8 right quote"));

  (* ══════════════════════════════════════════════════════════════════════
     ENC-015: Non-NFKC homoglyph character
     ══════════════════════════════════════════════════════════════════════ *)

  (* U+00B5 MICRO SIGN = C2 B5 *)
  run "ENC-015 fires on micro sign" (fun tag ->
      expect (fires "ENC-015" "5\xc2\xb5m") (tag ^ ": micro sign"));
  (* U+2126 OHM SIGN = E2 84 A6 *)
  run "ENC-015 fires on ohm sign" (fun tag ->
      expect (fires "ENC-015" "50\xe2\x84\xa6") (tag ^ ": ohm sign"));
  (* U+212B ANGSTROM SIGN = E2 84 AB *)
  run "ENC-015 fires on angstrom sign" (fun tag ->
      expect (fires "ENC-015" "3\xe2\x84\xab") (tag ^ ": angstrom sign"));
  (* U+017F LATIN SMALL LONG S = C5 BF *)
  run "ENC-015 fires on long s" (fun tag ->
      expect (fires "ENC-015" "proce\xc5\xbfs") (tag ^ ": long s"));
  run "ENC-015 count: micro + ohm" (fun tag ->
      expect
        (fires_with_count "ENC-015" "5\xc2\xb5m 50\xe2\x84\xa6" 2)
        (tag ^ ": count=2 (micro+ohm)"));
  run "ENC-015 clean: Greek mu" (fun tag ->
      (* U+03BC GREEK SMALL MU = CE BC — this is the canonical form *)
      expect (does_not_fire "ENC-015" "5\xce\xbcm") (tag ^ ": Greek mu is NFKC"));
  run "ENC-015 clean: plain ASCII" (fun tag ->
      expect (does_not_fire "ENC-015" "50 ohms") (tag ^ ": ASCII only"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-083: Unicode minus inside text mode
     ══════════════════════════════════════════════════════════════════════ *)

  (* U+2212 MINUS SIGN = E2 88 92 *)
  run "MATH-083 fires on minus in text" (fun tag ->
      expect
        (fires "MATH-083" "The result is 5\xe2\x88\x923.")
        (tag ^ ": minus in text"));
  run "MATH-083 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-083" "a\xe2\x88\x92b and c\xe2\x88\x92d" 2)
        (tag ^ ": count=2"));
  run "MATH-083 clean: minus inside math" (fun tag ->
      expect
        (does_not_fire "MATH-083" "$5\xe2\x88\x923$")
        (tag ^ ": minus inside $..$ ok"));
  run "MATH-083 clean: minus inside \\[..\\]" (fun tag ->
      expect
        (does_not_fire "MATH-083" "\\[5\xe2\x88\x923\\]")
        (tag ^ ": minus inside \\[..\\] ok"));
  run "MATH-083 clean: minus inside equation env" (fun tag ->
      expect
        (does_not_fire "MATH-083"
           "\\begin{equation}5\xe2\x88\x923\\end{equation}")
        (tag ^ ": minus inside equation ok"));
  run "MATH-083 clean: normal hyphen" (fun tag ->
      expect
        (does_not_fire "MATH-083" "well-known")
        (tag ^ ": ASCII hyphen is fine"));
  run "MATH-083 clean: no minus at all" (fun tag ->
      expect (does_not_fire "MATH-083" "Hello World") (tag ^ ": no minus"));

  (* ══════════════════════════════════════════════════════════════════════
     SPC-017: Missing thin space before units
     ══════════════════════════════════════════════════════════════════════ *)
  run "SPC-017 fires on 5cm" (fun tag ->
      expect (fires "SPC-017" "The length is 5cm.") (tag ^ ": 5cm"));
  run "SPC-017 fires on 100kg" (fun tag ->
      expect (fires "SPC-017" "Weight: 100kg") (tag ^ ": 100kg"));
  run "SPC-017 fires on 3GHz" (fun tag ->
      expect (fires "SPC-017" "Clock speed 3GHz") (tag ^ ": 3GHz"));
  run "SPC-017 fires on 10mm" (fun tag ->
      expect (fires "SPC-017" "gap of 10mm") (tag ^ ": 10mm"));
  run "SPC-017 fires on 5eV" (fun tag ->
      expect (fires "SPC-017" "energy 5eV") (tag ^ ": 5eV"));
  run "SPC-017 fires on 20dB" (fun tag ->
      expect (fires "SPC-017" "gain 20dB") (tag ^ ": 20dB"));
  run "SPC-017 count=2" (fun tag ->
      expect (fires_with_count "SPC-017" "5cm and 10kg" 2) (tag ^ ": count=2"));
  run "SPC-017 clean: proper thin space" (fun tag ->
      expect
        (does_not_fire "SPC-017" "The length is 5\\,cm.")
        (tag ^ ": thin space ok"));
  run "SPC-017 clean: space before unit" (fun tag ->
      expect
        (does_not_fire "SPC-017" "The length is 5 cm.")
        (tag ^ ": space before unit ok"));
  run "SPC-017 clean: inside math" (fun tag ->
      expect
        (does_not_fire "SPC-017" "$5cm$")
        (tag ^ ": inside math not flagged"));
  run "SPC-017 clean: no number-unit pattern" (fun tag ->
      expect (does_not_fire "SPC-017" "Hello World") (tag ^ ": no pattern"));

  (* ══════════════════════════════════════════════════════════════════════
     SPC-026: Mixed indentation width at same list depth
     ══════════════════════════════════════════════════════════════════════ *)
  run "SPC-026 fires on mixed indent itemize" (fun tag ->
      let src =
        "\\begin{itemize}\n  \\item first\n    \\item second\n\\end{itemize}"
      in
      expect (fires "SPC-026" src) (tag ^ ": mixed indent in itemize"));
  run "SPC-026 fires on mixed indent enumerate" (fun tag ->
      let src =
        "\\begin{enumerate}\n \\item A\n   \\item B\n\\end{enumerate}"
      in
      expect (fires "SPC-026" src) (tag ^ ": mixed indent in enumerate"));
  run "SPC-026 fires on mixed indent description" (fun tag ->
      let src =
        "\\begin{description}\n\
        \  \\item[a] desc\n\
        \      \\item[b] desc\n\
         \\end{description}"
      in
      expect (fires "SPC-026" src) (tag ^ ": mixed indent in description"));
  run "SPC-026 count=2 (two envs)" (fun tag ->
      let src =
        "\\begin{itemize}\n\
        \  \\item a\n\
        \    \\item b\n\
         \\end{itemize}\n\
         \\begin{enumerate}\n\
        \ \\item c\n\
        \   \\item d\n\
         \\end{enumerate}"
      in
      expect (fires_with_count "SPC-026" src 2) (tag ^ ": count=2"));
  run "SPC-026 clean: consistent indent" (fun tag ->
      let src =
        "\\begin{itemize}\n  \\item first\n  \\item second\n\\end{itemize}"
      in
      expect (does_not_fire "SPC-026" src) (tag ^ ": consistent indent"));
  run "SPC-026 clean: single item" (fun tag ->
      let src = "\\begin{itemize}\n  \\item only one\n\\end{itemize}" in
      expect (does_not_fire "SPC-026" src) (tag ^ ": single item"));
  run "SPC-026 clean: no list env" (fun tag ->
      expect
        (does_not_fire "SPC-026" "Just some text, no lists.")
        (tag ^ ": no list environment"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-044: Acronym not defined on first use (TYPO-044 is in rules_vpd_gen,
     only available in pilot mode)
     ══════════════════════════════════════════════════════════════════════ *)

  (* Helper: run with pilot mode enabled *)
  let fires_pilot id src =
    Unix.putenv "L0_VALIDATORS" "pilot";
    let r = find_result id src in
    Unix.putenv "L0_VALIDATORS" "";
    r <> None
  in
  let does_not_fire_pilot id src =
    Unix.putenv "L0_VALIDATORS" "pilot";
    let r = find_result id src in
    Unix.putenv "L0_VALIDATORS" "";
    r = None
  in

  run "TYPO-044 fires on undefined acronym" (fun tag ->
      expect
        (fires_pilot "TYPO-044" "The XYZ system is used widely.")
        (tag ^ ": undefined XYZ"));
  run "TYPO-044 fires on multiple undefined" (fun tag ->
      expect
        (fires_pilot "TYPO-044" "The FOOBAR and BAZQUX protocols.")
        (tag ^ ": two undefined"));
  run "TYPO-044 clean: acronym with parenthetical definition" (fun tag ->
      expect
        (does_not_fire_pilot "TYPO-044"
           "The Foo Bar Accelerator (FBA) is great. FBA is used.")
        (tag ^ ": defined with (FBA)"));
  run "TYPO-044 clean: acronym before parenthetical expansion" (fun tag ->
      expect
        (does_not_fire_pilot "TYPO-044" "FBA (Foo Bar Accelerator) is great.")
        (tag ^ ": defined with FBA (...)"));
  run "TYPO-044 clean: well-known acronym USA" (fun tag ->
      expect
        (does_not_fire_pilot "TYPO-044" "The USA is a country.")
        (tag ^ ": USA is well-known"));
  run "TYPO-044 clean: well-known acronym PDF" (fun tag ->
      expect
        (does_not_fire_pilot "TYPO-044" "Export to PDF format.")
        (tag ^ ": PDF is well-known"));
  run "TYPO-044 clean: well-known acronym API" (fun tag ->
      expect
        (does_not_fire_pilot "TYPO-044" "Use the API to connect.")
        (tag ^ ": API is well-known"));
  run "TYPO-044 clean: well-known acronym HTTP" (fun tag ->
      expect
        (does_not_fire_pilot "TYPO-044" "Connect via HTTP or HTTPS.")
        (tag ^ ": HTTP/HTTPS well-known"));
  run "TYPO-044 clean: inside math not flagged" (fun tag ->
      (* Math content is stripped — acronym-like patterns in math are ok *)
      expect
        (does_not_fire_pilot "TYPO-044" "$XY + AB = CD$")
        (tag ^ ": math mode acronyms ok"));
  run "TYPO-044 clean: no acronyms" (fun tag ->
      expect
        (does_not_fire_pilot "TYPO-044" "Hello world, this is text.")
        (tag ^ ": no acronyms"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-011: Unknown lstlisting language
     ══════════════════════════════════════════════════════════════════════ *)
  run "VERB-011 fires on unknown language" (fun tag ->
      expect
        (fires "VERB-011"
           "\\begin{lstlisting}[language=Klingon]\ncode\n\\end{lstlisting}")
        (tag ^ ": unknown Klingon"));
  run "VERB-011 fires on another unknown" (fun tag ->
      expect
        (fires "VERB-011"
           "\\begin{lstlisting}[language=Brainfuck]\ncode\n\\end{lstlisting}")
        (tag ^ ": unknown Brainfuck"));
  run "VERB-011 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-011"
           ("\\begin{lstlisting}[language=Foo]\na\n\\end{lstlisting}\n"
           ^ "\\begin{lstlisting}[language=Bar]\nb\n\\end{lstlisting}")
           2)
        (tag ^ ": count=2"));
  run "VERB-011 clean: known language Python" (fun tag ->
      expect
        (does_not_fire "VERB-011"
           "\\begin{lstlisting}[language=Python]\ncode\n\\end{lstlisting}")
        (tag ^ ": Python ok"));
  run "VERB-011 clean: known language Java" (fun tag ->
      expect
        (does_not_fire "VERB-011"
           "\\begin{lstlisting}[language=Java]\ncode\n\\end{lstlisting}")
        (tag ^ ": Java ok"));
  run "VERB-011 clean: known language C" (fun tag ->
      expect
        (does_not_fire "VERB-011"
           "\\begin{lstlisting}[language=C]\ncode\n\\end{lstlisting}")
        (tag ^ ": C ok"));
  run "VERB-011 clean: known language Haskell" (fun tag ->
      expect
        (does_not_fire "VERB-011"
           "\\begin{lstlisting}[language=Haskell]\ncode\n\\end{lstlisting}")
        (tag ^ ": Haskell ok"));
  run "VERB-011 clean: known language OCaml" (fun tag ->
      expect
        (does_not_fire "VERB-011"
           "\\begin{lstlisting}[language=OCaml]\ncode\n\\end{lstlisting}")
        (tag ^ ": OCaml ok"));
  run "VERB-011 clean: no lstlisting" (fun tag ->
      expect
        (does_not_fire "VERB-011" "Just text, no code.")
        (tag ^ ": no lstlisting"));
  run "VERB-011 clean: lstlisting without language option" (fun tag ->
      expect
        (does_not_fire "VERB-011" "\\begin{lstlisting}\ncode\n\\end{lstlisting}")
        (tag ^ ": no language= option"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "empty input: no batch5 rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let batch5_ids =
        [
          "ENC-010";
          "ENC-011";
          "ENC-015";
          "MATH-083";
          "SPC-017";
          "SPC-026";
          "TYPO-044";
          "VERB-011";
        ]
      in
      let batch5_fires =
        List.filter
          (fun (r : Validators.result) -> List.mem r.id batch5_ids)
          results
      in
      expect (batch5_fires = []) (tag ^ ": no fires on empty"));

  run "clean LaTeX: no batch5 rules fire" (fun tag ->
      let src =
        "\\documentclass{article}\n\
         \\begin{document}\n\
         Hello world.\n\
         \\end{document}"
      in
      let results = Validators.run_all src in
      let batch5_ids =
        [
          "ENC-010";
          "ENC-011";
          "ENC-015";
          "MATH-083";
          "SPC-017";
          "SPC-026";
          "TYPO-044";
          "VERB-011";
        ]
      in
      let batch5_fires =
        List.filter
          (fun (r : Validators.result) -> List.mem r.id batch5_ids)
          results
      in
      expect (batch5_fires = []) (tag ^ ": no fires on clean doc"));

  run "all 7 default-mode rules discoverable via run_all" (fun tag ->
      (* Verify each rule fires on its trigger input — proves registration *)
      expect (fires "ENC-010" "a\xcc\x81") (tag ^ ": ENC-010 registered");
      expect (fires "ENC-011" "x\x8ey") (tag ^ ": ENC-011 registered");
      expect (fires "ENC-015" "x\xc2\xb5y") (tag ^ ": ENC-015 registered");
      expect (fires "MATH-083" "x\xe2\x88\x92y") (tag ^ ": MATH-083 registered");
      expect (fires "SPC-017" "5cm") (tag ^ ": SPC-017 registered");
      expect
        (fires "SPC-026"
           "\\begin{itemize}\n  \\item a\n    \\item b\n\\end{itemize}")
        (tag ^ ": SPC-026 registered");
      expect
        (fires "VERB-011"
           "\\begin{lstlisting}[language=Klingon]\nx\n\\end{lstlisting}")
        (tag ^ ": VERB-011 registered"));

  run "TYPO-044 fires in pilot mode" (fun tag ->
      (* TYPO-044 is in rules_vpd_gen, only loaded in pilot mode *)
      Unix.putenv "L0_VALIDATORS" "pilot";
      let result = find_result "TYPO-044" "The XYZZY protocol." in
      (* Restore default *)
      Unix.putenv "L0_VALIDATORS" "";
      expect (result <> None) (tag ^ ": TYPO-044 fires in pilot mode"));

  (* Combined: document with multiple issues from different rules *)
  run "combined: multiple rules fire" (fun tag ->
      let src =
        "The XYZ protocol runs at 5GHz.\n\
         Distance is 10cm from the \xc2\xb5-controller.\n\
         Result: 5\xe2\x88\x923."
      in
      (* Should trigger: SPC-017 (5GHz, 10cm), ENC-015 (micro sign), MATH-083
         (unicode minus in text), TYPO-044 (XYZ undefined, pilot only) *)
      expect (fires "SPC-017" src) (tag ^ ": SPC-017 fires");
      expect (fires "ENC-015" src) (tag ^ ": ENC-015 fires");
      expect (fires "MATH-083" src) (tag ^ ": MATH-083 fires"));

  if !fails > 0 then (
    Printf.eprintf "[batch5] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[batch5] PASS %d cases\n%!" !cases
