(** Unit tests for VERB, CJK, and CMD validator rules. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[verb-cjk-cmd] FAIL: %s\n%!" msg;
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
  (* ══════════════════════════════════════════════════════════════════════ VERB
     rules
     ══════════════════════════════════════════════════════════════════════ *)

  (* VERB-002: Tab inside verbatim *)
  run "VERB-002 fires on tab in verbatim" (fun tag ->
      expect
        (fires "VERB-002" "\\begin{verbatim}\n\thello\n\\end{verbatim}")
        (tag ^ ": tab in verbatim"));
  run "VERB-002 fires on tab in lstlisting" (fun tag ->
      expect
        (fires "VERB-002" "\\begin{lstlisting}\n\tcode\n\\end{lstlisting}")
        (tag ^ ": tab in lstlisting"));
  run "VERB-002 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-002"
           "\\begin{verbatim}\n\ta\n\tb\n\\end{verbatim}" 2)
        (tag ^ ": count=2"));
  run "VERB-002 clean" (fun tag ->
      expect
        (does_not_fire "VERB-002" "\\begin{verbatim}\n  code\n\\end{verbatim}")
        (tag ^ ": spaces ok"));

  (* VERB-003: Trailing spaces inside verbatim *)
  run "VERB-003 fires on trailing space" (fun tag ->
      expect
        (fires "VERB-003" "\\begin{verbatim}\ncode   \n\\end{verbatim}")
        (tag ^ ": trailing space"));
  run "VERB-003 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-003"
           "\\begin{verbatim}\na \nb \n\\end{verbatim}" 2)
        (tag ^ ": count=2"));
  run "VERB-003 clean" (fun tag ->
      expect
        (does_not_fire "VERB-003" "\\begin{verbatim}\ncode\n\\end{verbatim}")
        (tag ^ ": no trailing"));

  (* VERB-004: Non-ASCII quotes inside verbatim *)
  run "VERB-004 fires on curly quotes in verbatim" (fun tag ->
      expect
        (fires "VERB-004"
           "\\begin{verbatim}\n\xe2\x80\x9chi\xe2\x80\x9d\n\\end{verbatim}")
        (tag ^ ": curly quotes in verbatim"));
  run "VERB-004 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-004"
           "\\begin{lstlisting}\n\xe2\x80\x9c\xe2\x80\x9d\n\\end{lstlisting}" 2)
        (tag ^ ": count=2"));
  run "VERB-004 clean" (fun tag ->
      expect
        (does_not_fire "VERB-004" "\\begin{verbatim}\n\"hi\"\n\\end{verbatim}")
        (tag ^ ": ASCII quotes ok"));

  (* VERB-005: Verbatim line > 120 characters *)
  run "VERB-005 fires on long line" (fun tag ->
      let long_line = String.make 121 'x' in
      expect
        (fires "VERB-005"
           ("\\begin{verbatim}\n" ^ long_line ^ "\n\\end{verbatim}"))
        (tag ^ ": 121-char line"));
  run "VERB-005 does not fire on 120 chars" (fun tag ->
      let ok_line = String.make 120 'x' in
      expect
        (does_not_fire "VERB-005"
           ("\\begin{verbatim}\n" ^ ok_line ^ "\n\\end{verbatim}"))
        (tag ^ ": 120 ok"));

  (* VERB-006: Inline \verb used for multiline content *)
  run "VERB-006 fires on multiline verb" (fun tag ->
      expect (fires "VERB-006" "\\verb|line1\nline2|") (tag ^ ": multiline verb"));
  run "VERB-006 clean" (fun tag ->
      expect
        (does_not_fire "VERB-006" "\\verb|inline code|")
        (tag ^ ": single line ok"));

  (* VERB-007: Nested verbatim environment *)
  run "VERB-007 fires on nested verbatim" (fun tag ->
      expect
        (fires "VERB-007"
           "\\begin{verbatim}\n\
            \\begin{lstlisting}\n\
            x\n\
            \\end{lstlisting}\n\
            \\end{verbatim}")
        (tag ^ ": nested"));
  run "VERB-007 clean" (fun tag ->
      expect
        (does_not_fire "VERB-007" "\\begin{verbatim}\ncode\n\\end{verbatim}")
        (tag ^ ": not nested"));

  (* VERB-008: lstlisting uses language=none *)
  run "VERB-008 fires on language=none" (fun tag ->
      expect
        (fires "VERB-008"
           "\\begin{lstlisting}[language=none]\ncode\n\\end{lstlisting}")
        (tag ^ ": language=none"));
  run "VERB-008 clean" (fun tag ->
      expect
        (does_not_fire "VERB-008"
           "\\begin{lstlisting}[language=Python]\ncode\n\\end{lstlisting}")
        (tag ^ ": specific language ok"));

  (* VERB-010: Inline code uses back-ticks *)
  run "VERB-010 fires on backticks" (fun tag ->
      expect
        (fires "VERB-010" "Use `code here` for inline")
        (tag ^ ": backticks"));
  run "VERB-010 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-010" "Use `foo` and `bar` here" 2)
        (tag ^ ": count=2"));
  run "VERB-010 clean" (fun tag ->
      expect
        (does_not_fire "VERB-010" "No backticks here")
        (tag ^ ": no backticks"));

  (* VERB-013: Code line > 120 glyphs in minted *)
  run "VERB-013 fires on long minted line" (fun tag ->
      let long_line = String.make 121 'a' in
      expect
        (fires "VERB-013"
           ("\\begin{minted}{python}\n" ^ long_line ^ "\n\\end{minted}"))
        (tag ^ ": 121-char minted line"));
  run "VERB-013 clean" (fun tag ->
      expect
        (does_not_fire "VERB-013"
           "\\begin{minted}{python}\nshort\n\\end{minted}")
        (tag ^ ": short line ok"));

  (* VERB-015: catcode changes *)
  run "VERB-015 fires on catcode" (fun tag ->
      expect (fires "VERB-015" "\\catcode`\\@=11") (tag ^ ": catcode usage"));
  run "VERB-015 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-015" "\\catcode`\\@=11\n\\catcode`\\_=11" 2)
        (tag ^ ": count=2"));
  run "VERB-015 clean" (fun tag ->
      expect (does_not_fire "VERB-015" "normal text") (tag ^ ": no catcode"));

  (* VERB-017: minted lacks linenos in long block *)
  run "VERB-017 fires on long minted without linenos" (fun tag ->
      let lines =
        String.concat "\n" (List.init 25 (fun i -> "line" ^ string_of_int i))
      in
      expect
        (fires "VERB-017"
           ("\\begin{minted}{python}\n" ^ lines ^ "\n\\end{minted}"))
        (tag ^ ": >20 lines no linenos"));
  run "VERB-017 clean with linenos" (fun tag ->
      let lines = String.concat "\n" (List.init 25 (fun _ -> "code")) in
      expect
        (does_not_fire "VERB-017"
           ("\\begin{minted}[linenos]{python}\n" ^ lines ^ "\n\\end{minted}"))
        (tag ^ ": has linenos"));
  run "VERB-017 clean short block" (fun tag ->
      expect
        (does_not_fire "VERB-017"
           "\\begin{minted}{python}\nshort\n\\end{minted}")
        (tag ^ ": short block"));

  (* VERB-001: \verb delimiter reused inside same \verb block *)
  run "VERB-001 fires on nested verb" (fun tag ->
      expect
        (fires "VERB-001" "\\verb|foo\\verb|bar|")
        (tag ^ ": nested verb delimiter"));
  run "VERB-001 fires with different delimiter" (fun tag ->
      expect
        (fires "VERB-001" "\\verb!foo\\verb!bar!")
        (tag ^ ": different delimiter"));
  run "VERB-001 severity=Error" (fun tag ->
      match find_result "VERB-001" "\\verb|foo\\verb|bar|" with
      | Some r ->
          expect (r.severity = Validators.Error) (tag ^ ": severity is Error")
      | None -> expect false (tag ^ ": should fire"));
  run "VERB-001 clean single verb" (fun tag ->
      expect
        (does_not_fire "VERB-001" "\\verb|hello world|")
        (tag ^ ": normal usage"));
  run "VERB-001 clean verb*" (fun tag ->
      expect
        (does_not_fire "VERB-001" "\\verb*|hello|")
        (tag ^ ": star variant ok"));
  run "VERB-001 clean no verb" (fun tag ->
      expect
        (does_not_fire "VERB-001" "just plain text")
        (tag ^ ": no verb at all"));

  (* VERB-009: Missing caption in minted code block *)
  run "VERB-009 fires on bare minted" (fun tag ->
      expect
        (fires "VERB-009"
           "\\begin{minted}{python}\nprint(\"hi\")\n\\end{minted}")
        (tag ^ ": bare minted"));
  run "VERB-009 fires on minted with options but no listing" (fun tag ->
      expect
        (fires "VERB-009"
           "\\begin{minted}[linenos]{python}\ncode\n\\end{minted}")
        (tag ^ ": options but no listing"));
  run "VERB-009 severity=Warning" (fun tag ->
      match
        find_result "VERB-009" "\\begin{minted}{python}\ncode\n\\end{minted}"
      with
      | Some r ->
          expect
            (r.severity = Validators.Warning)
            (tag ^ ": severity is Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "VERB-009 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-009"
           "\\begin{minted}{python}\n\
            a\n\
            \\end{minted}\n\
            \\begin{minted}{java}\n\
            b\n\
            \\end{minted}"
           2)
        (tag ^ ": count=2 for two bare blocks"));
  run "VERB-009 clean wrapped in listing" (fun tag ->
      expect
        (does_not_fire "VERB-009"
           "\\begin{listing}\n\
            \\begin{minted}{python}\n\
            print(\"hi\")\n\
            \\end{minted}\n\
            \\end{listing}")
        (tag ^ ": wrapped in listing"));
  run "VERB-009 clean no minted" (fun tag ->
      expect
        (does_not_fire "VERB-009" "just text, no minted")
        (tag ^ ": no minted at all"));

  (* VERB-012: minted block missing autogobble *)
  run "VERB-012 fires on minted without options" (fun tag ->
      expect
        (fires "VERB-012" "\\begin{minted}{python}\ncode\n\\end{minted}")
        (tag ^ ": no options"));
  run "VERB-012 fires on minted with options but no autogobble" (fun tag ->
      expect
        (fires "VERB-012"
           "\\begin{minted}[linenos]{python}\ncode\n\\end{minted}")
        (tag ^ ": linenos but no autogobble"));
  run "VERB-012 severity=Info" (fun tag ->
      match
        find_result "VERB-012" "\\begin{minted}{python}\ncode\n\\end{minted}"
      with
      | Some r ->
          expect (r.severity = Validators.Info) (tag ^ ": severity is Info")
      | None -> expect false (tag ^ ": should fire"));
  run "VERB-012 count=2" (fun tag ->
      expect
        (fires_with_count "VERB-012"
           "\\begin{minted}{python}\n\
            a\n\
            \\end{minted}\n\
            \\begin{minted}{java}\n\
            b\n\
            \\end{minted}"
           2)
        (tag ^ ": count=2"));
  run "VERB-012 clean with autogobble" (fun tag ->
      expect
        (does_not_fire "VERB-012"
           "\\begin{minted}[autogobble]{python}\ncode\n\\end{minted}")
        (tag ^ ": has autogobble"));
  run "VERB-012 clean with autogobble and other opts" (fun tag ->
      expect
        (does_not_fire "VERB-012"
           "\\begin{minted}[linenos,autogobble]{python}\ncode\n\\end{minted}")
        (tag ^ ": autogobble with linenos"));
  run "VERB-012 clean no minted" (fun tag ->
      expect (does_not_fire "VERB-012" "plain text") (tag ^ ": no minted"));

  (* VERB-016: minted without escapeinside while containing back-ticks *)
  run "VERB-016 fires on backtick without escapeinside" (fun tag ->
      expect
        (fires "VERB-016" "\\begin{minted}{python}\n`backtick`\n\\end{minted}")
        (tag ^ ": backtick no escapeinside"));
  run "VERB-016 severity=Info" (fun tag ->
      match
        find_result "VERB-016" "\\begin{minted}{python}\n`tick`\n\\end{minted}"
      with
      | Some r ->
          expect (r.severity = Validators.Info) (tag ^ ": severity is Info")
      | None -> expect false (tag ^ ": should fire"));
  run "VERB-016 clean with escapeinside" (fun tag ->
      expect
        (does_not_fire "VERB-016"
           "\\begin{minted}[escapeinside=||]{python}\n`tick`\n\\end{minted}")
        (tag ^ ": has escapeinside"));
  run "VERB-016 clean no backticks" (fun tag ->
      expect
        (does_not_fire "VERB-016"
           "\\begin{minted}{python}\nno_ticks\n\\end{minted}")
        (tag ^ ": no backticks in body"));
  run "VERB-016 clean no minted" (fun tag ->
      expect (does_not_fire "VERB-016" "just text") (tag ^ ": no minted"));

  (* ══════════════════════════════════════════════════════════════════════ CJK
     rules
     ══════════════════════════════════════════════════════════════════════ *)

  (* CJK-001: Full-width comma U+FF0C *)
  run "CJK-001 fires on fullwidth comma" (fun tag ->
      expect (fires "CJK-001" "text\xef\xbc\x8cmore") (tag ^ ": U+FF0C"));
  run "CJK-001 count=2" (fun tag ->
      expect
        (fires_with_count "CJK-001" "\xef\xbc\x8c and \xef\xbc\x8c" 2)
        (tag ^ ": count=2"));
  run "CJK-001 clean" (fun tag ->
      expect (does_not_fire "CJK-001" "text, more") (tag ^ ": ASCII comma"));

  (* CJK-002: Full-width period U+FF0E *)
  run "CJK-002 fires on fullwidth period" (fun tag ->
      expect (fires "CJK-002" "text\xef\xbc\x8emore") (tag ^ ": U+FF0E"));
  run "CJK-002 clean" (fun tag ->
      expect (does_not_fire "CJK-002" "text. more") (tag ^ ": ASCII period"));

  (* CJK-014: Inter-punct U+30FB *)
  run "CJK-014 fires on inter-punct" (fun tag ->
      expect (fires "CJK-014" "text\xe3\x83\xbbmore") (tag ^ ": U+30FB"));
  run "CJK-014 count=2" (fun tag ->
      expect
        (fires_with_count "CJK-014" "\xe3\x83\xbb and \xe3\x83\xbb" 2)
        (tag ^ ": count=2"));
  run "CJK-014 clean" (fun tag ->
      expect (does_not_fire "CJK-014" "normal text") (tag ^ ": no inter-punct"));

  (* CJK-010: Half-width CJK punctuation in full-width context *)
  run "CJK-010 fires on ASCII comma after CJK" (fun tag ->
      expect (fires "CJK-010" "\xe4\xb8\xad,") (tag ^ ": CJK then comma"));
  run "CJK-010 fires on ASCII comma before CJK" (fun tag ->
      expect (fires "CJK-010" ",\xe4\xb8\xad") (tag ^ ": comma then CJK"));
  run "CJK-010 fires on period after CJK" (fun tag ->
      expect (fires "CJK-010" "\xe4\xb8\xad.") (tag ^ ": CJK then period"));
  run "CJK-010 fires on semicolon after CJK" (fun tag ->
      expect (fires "CJK-010" "\xe4\xb8\xad;") (tag ^ ": CJK then semicolon"));
  run "CJK-010 fires on colon after CJK" (fun tag ->
      expect (fires "CJK-010" "\xe4\xb8\xad:") (tag ^ ": CJK then colon"));
  run "CJK-010 severity=Warning" (fun tag ->
      match find_result "CJK-010" "\xe4\xb8\xad," with
      | Some r ->
          expect
            (r.severity = Validators.Warning)
            (tag ^ ": severity is Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "CJK-010 count=2" (fun tag ->
      expect
        (fires_with_count "CJK-010" "\xe4\xb8\xad,\xe4\xb8\xad." 2)
        (tag ^ ": count=2 for comma and period"));
  run "CJK-010 clean ASCII only" (fun tag ->
      expect (does_not_fire "CJK-010" "hello, world") (tag ^ ": no CJK context"));
  run "CJK-010 clean no punctuation near CJK" (fun tag ->
      expect
        (does_not_fire "CJK-010" "\xe4\xb8\xad\xe6\x96\x87")
        (tag ^ ": CJK without half-width punct"));

  (* ══════════════════════════════════════════════════════════════════════ CMD
     rules
     ══════════════════════════════════════════════════════════════════════ *)

  (* CMD-002: \def instead of \renewcommand *)
  run "CMD-002 fires on def" (fun tag ->
      expect (fires "CMD-002" "\\def\\mycommand{stuff}") (tag ^ ": def usage"));
  run "CMD-002 count=2" (fun tag ->
      expect
        (fires_with_count "CMD-002" "\\def\\foo{a}\n\\def\\bar{b}" 2)
        (tag ^ ": count=2"));
  run "CMD-002 clean" (fun tag ->
      expect
        (does_not_fire "CMD-002" "\\newcommand{\\mycommand}{stuff}")
        (tag ^ ": newcommand ok"));

  (* CMD-004: CamelCase command names discouraged *)
  run "CMD-004 fires on newcommand with camelCase" (fun tag ->
      expect
        (fires "CMD-004" "\\newcommand{\\myFunc}{stuff}")
        (tag ^ ": camelCase newcommand"));
  run "CMD-004 fires on renewcommand with camelCase" (fun tag ->
      expect
        (fires "CMD-004" "\\renewcommand{\\getValue}{stuff}")
        (tag ^ ": camelCase renewcommand"));
  run "CMD-004 fires on def with camelCase" (fun tag ->
      expect (fires "CMD-004" "\\def\\myVar{stuff}") (tag ^ ": camelCase def"));
  run "CMD-004 severity=Info" (fun tag ->
      match find_result "CMD-004" "\\newcommand{\\myFunc}{stuff}" with
      | Some r ->
          expect (r.severity = Validators.Info) (tag ^ ": severity is Info")
      | None -> expect false (tag ^ ": should fire"));
  run "CMD-004 count=2" (fun tag ->
      expect
        (fires_with_count "CMD-004"
           "\\newcommand{\\myFunc}{a}\n\\renewcommand{\\getValue}{b}" 2)
        (tag ^ ": count=2"));
  run "CMD-004 clean all lowercase" (fun tag ->
      expect
        (does_not_fire "CMD-004" "\\newcommand{\\myfunc}{stuff}")
        (tag ^ ": all lowercase ok"));
  run "CMD-004 clean ALLCAPS" (fun tag ->
      expect
        (does_not_fire "CMD-004" "\\newcommand{\\MYFUNC}{stuff}")
        (tag ^ ": all caps ok"));
  run "CMD-004 clean no command def" (fun tag ->
      expect
        (does_not_fire "CMD-004" "just text, no commands")
        (tag ^ ": no command definitions"));

  (* CMD-005: Single-letter macro *)
  run "CMD-005 fires on single-letter" (fun tag ->
      expect
        (fires "CMD-005" "\\newcommand{\\x}{text}")
        (tag ^ ": single letter"));
  run "CMD-005 clean" (fun tag ->
      expect
        (does_not_fire "CMD-005" "\\newcommand{\\myCmd}{text}")
        (tag ^ ": multi-letter ok"));

  (* CMD-006: Macro defined inside document body *)
  run "CMD-006 fires on body def" (fun tag ->
      expect
        (fires "CMD-006"
           "\\begin{document}\n\\newcommand{\\foo}{bar}\n\\end{document}")
        (tag ^ ": def in body"));
  run "CMD-006 clean in preamble" (fun tag ->
      expect
        (does_not_fire "CMD-006"
           "\\newcommand{\\foo}{bar}\n\\begin{document}\ntext\n\\end{document}")
        (tag ^ ": preamble ok"));

  (* CMD-008: \@ in macro name without makeatletter *)
  run "CMD-008 fires on @ in name" (fun tag ->
      expect
        (fires "CMD-008" "\\def\\my@cmd{stuff}")
        (tag ^ ": @ without makeatletter"));
  run "CMD-008 clean with makeatletter" (fun tag ->
      expect
        (does_not_fire "CMD-008"
           "\\makeatletter\n\\def\\my@cmd{stuff}\n\\makeatother")
        (tag ^ ": makeatletter present"));

  (* CMD-009: Macro name contains digits *)
  run "CMD-009 fires on digits" (fun tag ->
      expect (fires "CMD-009" "\\newcommand{\\cmd2}{text}") (tag ^ ": digits"));
  run "CMD-009 clean" (fun tag ->
      expect
        (does_not_fire "CMD-009" "\\newcommand{\\mycmd}{text}")
        (tag ^ ": no digits"));

  (* CMD-011: \def in preamble without \makeatletter *)
  run "CMD-011 fires on def in preamble" (fun tag ->
      expect
        (fires "CMD-011" "\\def\\myfoo{bar}\n\\begin{document}\n\\end{document}")
        (tag ^ ": def without makeatletter"));
  run "CMD-011 clean with makeatletter" (fun tag ->
      expect
        (does_not_fire "CMD-011"
           "\\makeatletter\n\
            \\def\\myfoo{bar}\n\
            \\makeatother\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": makeatletter present"));

  (* CMD-013: \def\arraystretch in document body *)
  run "CMD-013 fires in body" (fun tag ->
      expect
        (fires "CMD-013"
           "\\begin{document}\n\\def\\arraystretch{1.5}\n\\end{document}")
        (tag ^ ": arraystretch in body"));
  run "CMD-013 clean in preamble" (fun tag ->
      expect
        (does_not_fire "CMD-013"
           "\\def\\arraystretch{1.5}\n\\begin{document}\ntext\n\\end{document}")
        (tag ^ ": preamble ok"));

  (* ══════════════════════════════════════════════════════════════════════ Edge
     cases
     ══════════════════════════════════════════════════════════════════════ *)

  (* Empty input triggers nothing *)
  run "empty input" (fun tag ->
      let results = Validators.run_all "" in
      let verb_cjk_cmd =
        List.filter
          (fun (r : Validators.result) ->
            let pfx3 =
              if String.length r.id >= 4 then String.sub r.id 0 4 else ""
            in
            let pfx4 =
              if String.length r.id >= 5 then String.sub r.id 0 5 else ""
            in
            pfx3 = "VERB" || pfx3 = "CJK-" || pfx3 = "CMD-" || pfx4 = "VERB-")
          results
      in
      expect (verb_cjk_cmd = []) (tag ^ ": no fires on empty"));

  if !fails > 0 then (
    Printf.eprintf "[verb-cjk-cmd] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[verb-cjk-cmd] PASS %d cases\n%!" !cases
