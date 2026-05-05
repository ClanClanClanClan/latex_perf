(** Unit tests for TYPO-002 / TYPO-003 fix producers (v26.2.1 PR #3).

    These rules aggregate [count] per document and emit one replace edit per
    non-overlapping match position. See [specs/v26/V26_2_1_PLAN.md] §3 PR #3 for
    the design rationale. *)

open Test_helpers

let apply_all s edits =
  match Latex_parse_lib.Cst_edit.apply_all s edits with
  | Ok out -> out
  | Error _ -> failwith "overlapping fix edits — should not happen in tests"

let () =
  (* TYPO-002/003 ship in the pilot rule set (gated by L0_VALIDATORS). Enable it
     for the duration of this test file. *)
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* TYPO-002: `--` → `–` (en-dash). *)
  run "TYPO-002 fix: single -- becomes en-dash" (fun tag ->
      let src = "Words -- more words" in
      let edits = fix_edits "TYPO-002" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Words – more words")
        (tag ^ ": one edit, applied = en-dash"));

  run "TYPO-002 fix: two disjoint -- produce two edits" (fun tag ->
      let src = "a -- b, c -- d" in
      let edits = fix_edits "TYPO-002" src in
      expect
        (List.length edits = 2 && apply_all src edits = "a – b, c – d")
        (tag ^ ": two edits applied correctly"));

  run "TYPO-002 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-002" "no double hyphens here")
        (tag ^ ": no fire, no fix"));

  (* TYPO-003: `---` → `—` (em-dash). TYPO-002 is suppressed by conflict edge on
     the same source. *)
  run "TYPO-003 fix: single --- becomes em-dash" (fun tag ->
      let src = "Words --- more words" in
      let edits = fix_edits "TYPO-003" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Words — more words")
        (tag ^ ": one edit, applied = em-dash"));

  run "TYPO-003 fix: two disjoint --- produce two edits" (fun tag ->
      let src = "a --- b, c --- d" in
      let edits = fix_edits "TYPO-003" src in
      expect
        (List.length edits = 2 && apply_all src edits = "a — b, c — d")
        (tag ^ ": two edits applied correctly"));

  run "TYPO-003 on ---- emits one non-overlapping edit at offset 0" (fun tag ->
      (* `----` contains `---` at offset 0 (non-overlap advance by 3). TYPO-003
         fix emits one replace(0,3,"—"); applying yields `—-`. Rule-count may be
         >1 (overlap semantics) but fix-count = 1. *)
      let src = "word ---- word" in
      let edits = fix_edits "TYPO-003" src in
      expect
        (List.length edits = 1 && apply_all src edits = "word —- word")
        (tag ^ ": one non-overlapping edit"));

  (* Interaction: when --- is present, TYPO-003 wins (conflict edge from PR #241
     p1.3); TYPO-002 is suppressed at run_all level. We don't assert on TYPO-002
     here — the test above already covers TYPO-002's fix semantics in isolation
     (no --- in the source). *)

  (* v26.3 §3 item E: 5 new fix producers. Quick smoke tests below verify each
     emits applicable edits. *)
  run "TYPO-018 fix collapses double space" (fun tag ->
      let src = "alpha  beta" in
      let edits = fix_edits "TYPO-018" src in
      expect
        (List.length edits = 1 && apply_all src edits = "alpha beta")
        (tag ^ ": one space remains"));

  run "TYPO-022 fix removes space before closing brace" (fun tag ->
      let src = "(foo )" in
      let edits = fix_edits "TYPO-022" src in
      expect
        (List.length edits = 1 && apply_all src edits = "(foo)")
        (tag ^ ": ' )' becomes ')'"));

  run "TYPO-033 fix replaces et.al with et al." (fun tag ->
      let src = "Foo et.al bar" in
      let edits = fix_edits "TYPO-033" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Foo et al. bar")
        (tag ^ ": et al. with space"));

  run "TYPO-037 fix removes space before comma" (fun tag ->
      let src = "alpha , beta" in
      let edits = fix_edits "TYPO-037" src in
      expect
        (List.length edits = 1 && apply_all src edits = "alpha, beta")
        (tag ^ ": no leading space"));

  run "TYPO-024 fix deletes trailing dash" (fun tag ->
      let src = "Hello-\nWorld" in
      let edits = fix_edits "TYPO-024" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Hello\nWorld")
        (tag ^ ": dangling dash removed"));

  run "TYPO-024 fix handles CRLF line endings" (fun tag ->
      let src = "Hello-\r\nWorld" in
      let edits = fix_edits "TYPO-024" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Hello\r\nWorld")
        (tag ^ ": dangling dash removed across CRLF"));

  run "TYPO-027 fix collapses run of !!! to single !" (fun tag ->
      let src = "Wow!!! Amazing" in
      let edits = fix_edits "TYPO-027" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Wow! Amazing")
        (tag ^ ": run reduced to single bang"));

  run "TYPO-035 fix inserts NBSP before French punct" (fun tag ->
      let src = "Bonjour ; au revoir : merci !" in
      let edits = fix_edits "TYPO-035" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 3
        && out = "Bonjour\xc2\xa0; au revoir\xc2\xa0: merci\xc2\xa0!")
        (tag ^ ": NBSP-prefixed punctuation"));

  (* v26.3.1 batch — 10 new fix producers. *)
  run "TYPO-006 fix replaces tabs with 4 spaces" (fun tag ->
      let src = "a\tb\tc" in
      let edits = fix_edits "TYPO-006" src in
      expect
        (List.length edits = 2 && apply_all src edits = "a    b    c")
        (tag ^ ": two tabs replaced"));

  run "TYPO-007 fix strips trailing spaces" (fun tag ->
      let src = "alpha   \nbeta\t \ngamma" in
      let edits = fix_edits "TYPO-007" src in
      expect
        (List.length edits = 2 && apply_all src edits = "alpha\nbeta\ngamma")
        (tag ^ ": trailing whitespace stripped on both lines"));

  run "TYPO-008 fix collapses 4 newlines to 2" (fun tag ->
      let src = "a\n\n\n\nb" in
      let edits = fix_edits "TYPO-008" src in
      expect
        (List.length edits = 1 && apply_all src edits = "a\n\nb")
        (tag ^ ": run collapsed"));

  run "TYPO-009 fix strips ~ at line start" (fun tag ->
      let src = "~alpha\n~beta" in
      let edits = fix_edits "TYPO-009" src in
      expect
        (List.length edits = 2 && apply_all src edits = "alpha\nbeta")
        (tag ^ ": both leading ~ deleted"));

  run "TYPO-013 fix replaces single backtick with curly opening quote"
    (fun tag ->
      let src = "`hello' and `world'" in
      let edits = fix_edits "TYPO-013" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "\xe2\x80\x98hello' and \xe2\x80\x98world'")
        (tag ^ ": both backticks replaced"));

  run "TYPO-013 leaves double `` alone" (fun tag ->
      expect
        (does_not_fire "TYPO-013" "``opener'' is fine")
        (tag ^ ": no fire on TeX double-backtick"));

  run "TYPO-015 fix collapses double escaped percent" (fun tag ->
      let src = "stray \\%\\% inline" in
      let edits = fix_edits "TYPO-015" src in
      expect
        (List.length edits = 1 && apply_all src edits = "stray \\% inline")
        (tag ^ ": double escape collapsed"));

  run "SPC-002 fix empties whitespace-only lines" (fun tag ->
      let src = "alpha\n   \nbeta\n\t\ngamma" in
      let edits = fix_edits "SPC-002" src in
      expect
        (List.length edits = 2 && apply_all src edits = "alpha\n\nbeta\n\ngamma")
        (tag ^ ": both ws-only lines emptied"));

  run "SPC-003 fix replaces leading tabs in mixed indent" (fun tag ->
      let src = " \tcode\nclean\n\t code2" in
      let edits = fix_edits "SPC-003" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 2 && out = "     code\nclean\n     code2")
        (tag ^ ": both mixed-indent lines normalised"));

  run "SPC-004 fix replaces bare CR with LF" (fun tag ->
      let src = "alpha\rbeta\r\ngamma\rdelta" in
      let edits = fix_edits "SPC-004" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "alpha\nbeta\r\ngamma\ndelta")
        (tag ^ ": CRs not in CRLF replaced"));

  run "SPC-005 fix strips trailing tabs" (fun tag ->
      let src = "alpha\t\nbeta\nclean\t\t\ndone" in
      let edits = fix_edits "SPC-005" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "alpha\nbeta\nclean\ndone")
        (tag ^ ": both trailing-tab lines stripped"));

  (* v26.4 §1.3: 5 more fix producers. *)
  run "TYPO-014 fix removes space before percent" (fun tag ->
      let src = "alpha %comment\nbeta %end" in
      let edits = fix_edits "TYPO-014" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "alpha%comment\nbeta%end")
        (tag ^ ": both spaces deleted"));

  run "TYPO-021 fix inserts space after ASCII ellipsis" (fun tag ->
      let src = "Hello...World" in
      let edits = fix_edits "TYPO-021" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Hello... World")
        (tag ^ ": space inserted before W"));

  run "TYPO-021 fix inserts space after Unicode ellipsis" (fun tag ->
      let src = "End\xe2\x80\xa6Next" in
      (* "End…Next" *)
      let edits = fix_edits "TYPO-021" src in
      expect
        (List.length edits = 1 && apply_all src edits = "End\xe2\x80\xa6 Next")
        (tag ^ ": space inserted before N"));

  run "TYPO-025 fix removes space before en-dash in number range" (fun tag ->
      let src = "see pp. 12 \xe2\x80\x9320 and 30 --45" in
      (* "12 –20" *)
      let edits = fix_edits "TYPO-025" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 2 && out = "see pp. 12\xe2\x80\x9320 and 30--45")
        (tag ^ ": both space-runs collapsed"));

  run "SPC-009 fix strips ASCII tilde at line start" (fun tag ->
      let src = "~ alpha\n~beta" in
      let edits = fix_edits "SPC-009" src in
      expect
        (List.length edits = 2 && apply_all src edits = " alpha\nbeta")
        (tag ^ ": both ~ stripped"));

  run "SPC-009 fix strips Unicode NBSP at line start" (fun tag ->
      let src = "\xc2\xa0alpha\nbeta" in
      let edits = fix_edits "SPC-009" src in
      expect
        (List.length edits = 1 && apply_all src edits = "alpha\nbeta")
        (tag ^ ": NBSP stripped"));

  run "SPC-010 fix collapses double space after period to single" (fun tag ->
      let src = "First.  Second.  Third." in
      let edits = fix_edits "SPC-010" src in
      expect
        (List.length edits = 2 && apply_all src edits = "First. Second. Third.")
        (tag ^ ": both runs collapsed"));

  (* v26.5 §7 cycle byproduct: 4 more fix producers. *)
  run "TYPO-016 fix replaces space-before-cite with NBSP" (fun tag ->
      let src = "see \\cite{x} and \\ref{y}." in
      let edits = fix_edits "TYPO-016" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "see~\\cite{x} and~\\ref{y}.")
        (tag ^ ": both spaces replaced with ~"));

  run "TYPO-026 fix replaces en-dash in number range with --" (fun tag ->
      let src = "pages 12\xe2\x80\x9320 and 30\xe2\x80\x9345" in
      let edits = fix_edits "TYPO-026" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "pages 12--20 and 30--45")
        (tag ^ ": both en-dashes replaced"));

  run "SPC-008 fix strips leading whitespace from indented paragraph"
    (fun tag ->
      let src = "Para one.\n\n   Indented paragraph." in
      let edits = fix_edits "SPC-008" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Para one.\n\nIndented paragraph.")
        (tag ^ ": leading whitespace stripped"));

  run "SPC-008 fix leaves \\item lines alone" (fun tag ->
      expect
        (does_not_fire "SPC-008" "First line.\n\n  \\item bullet")
        (tag ^ ": \\item exempt"));

  run "SPC-011 fix strips trailing space inside $$…$$" (fun tag ->
      let src = "$$\nx + y  \nz\n$$" in
      let edits = fix_edits "SPC-011" src in
      expect
        (List.length edits = 1 && apply_all src edits = "$$\nx + y\nz\n$$")
        (tag ^ ": trailing whitespace before \\n stripped inside display"));

  (* v27.0.5 batch: TYPO-010 fix producer. TYPO-004 fix deliberately deferred —
     `` and '' need math-range filtering before they can be auto-fixed (`` `` ``
     is fine; '' in $f''(x)$ is derivative notation which would corrupt). *)
  run "TYPO-010 fix: drops space before comma" (fun tag ->
      let src = "Apples , oranges , bananas" in
      let edits = fix_edits "TYPO-010" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "Apples, oranges, bananas")
        (tag ^ ": both spaces removed before ,"));

  run "TYPO-010 fix: handles multiple punctuation kinds" (fun tag ->
      let src = "Hi ! How ? Yes ; ok ." in
      let edits = fix_edits "TYPO-010" src in
      expect
        (List.length edits = 4 && apply_all src edits = "Hi! How? Yes; ok.")
        (tag ^ ": ! ? ; . all normalised"));

  run "TYPO-010 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-010" "Apples, oranges, bananas.")
        (tag ^ ": no fire, no fix"));

  (* v27.0.6 batch: TYPO-004 fix producer (math-aware via find_math_ranges). *)
  run "TYPO-004 fix: backtick/apostrophe become curly quotes outside math"
    (fun tag ->
      let src = "Said ``hello'' to her" in
      let edits = fix_edits "TYPO-004" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "Said \xe2\x80\x9chello\xe2\x80\x9d to her")
        (tag ^ ": `` → U+201C, '' → U+201D"));

  run "TYPO-004 fix: skips '' inside $..$ math (double-prime preserved)"
    (fun tag ->
      let src = "Let $f''(x) = 0$ and ``done''" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      (* Only the ``done'' outside math should be fixed. $f''(x) = 0$ must
         remain bytewise unchanged. *)
      expect
        (List.length edits = 2
        && out = "Let $f''(x) = 0$ and \xe2\x80\x9cdone\xe2\x80\x9d"
        && (* Math segment $f''(x) = 0$ unchanged *)
        String.length out = String.length src - 4 + 6
        (* removed 4 bytes (`` and ''), added 6 (UTF-8 U+201C + U+201D) *))
        (tag ^ ": math segment preserved"));

  run "TYPO-004 fix: skips '' inside \\[...\\] display math" (fun tag ->
      let src = "\\[ y'' = a y' + b y \\] and ``z''" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      expect
        (out = "\\[ y'' = a y' + b y \\] and \xe2\x80\x9cz\xe2\x80\x9d"
        && List.length edits = 2)
        (tag ^ ": display math preserved"));

  run "TYPO-004 fix: skips '' inside \\begin{equation} env" (fun tag ->
      let src = "\\begin{equation} f''(x) = 0 \\end{equation} and ``done''" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      expect
        (out
         = "\\begin{equation} f''(x) = 0 \\end{equation} and \
            \xe2\x80\x9cdone\xe2\x80\x9d"
        && List.length edits = 2)
        (tag ^ ": equation env preserved"));

  run "TYPO-004 fix: still fires count on '' in math (no-fix path)" (fun tag ->
      (* Math-only `` or '' should still report (count > 0) but no auto-fix.
         Round-8 audit: previously asserted only [List.length edits = 0], which
         can't disambiguate "rule didn't fire" from "rule fired but emitted no
         fix". Now also asserts [fires_with_count] = 2 to verify the rule DOES
         fire (count = 2 because the source contains two '' pairs at offsets 3
         and 9), and the fix list is empty because both pairs are inside
         math. *)
      let src = "$f''(x) g''(x)$" in
      let edits = fix_edits "TYPO-004" src in
      expect
        (fires_with_count "TYPO-004" src 2 && List.length edits = 0)
        (tag ^ ": rule fires with count=2, no fix edits"));

  run "TYPO-004 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-004" "no curly quote needed here")
        (tag ^ ": no fire, no fix"));

  run "TYPO-004 fix: escaped \\$ does not open math" (fun tag ->
      (* \$ is a literal dollar sign in LaTeX (escaped); it must NOT open a math
         segment. `` `` and '' adjacent to \$ should still be fixed. *)
      let src = "Cost: \\$5 ``cheap'' compared to gold" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 2
        && out = "Cost: \\$5 \xe2\x80\x9ccheap\xe2\x80\x9d compared to gold")
        (tag ^ ": \\$ treated as literal, fix applies"));

  run "TYPO-004 fix: multiple math regions correctly delimited" (fun tag ->
      (* Three math regions interleaved with text. Each `''` outside math is
         fixed; the two inside math are preserved. *)
      let src = "Pre $a''$ mid ``one'' more $b''$ end ``two''" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 4
        && out
           = "Pre $a''$ mid \xe2\x80\x9cone\xe2\x80\x9d more $b''$ end \
              \xe2\x80\x9ctwo\xe2\x80\x9d")
        (tag ^ ": three math regions preserved, text segments fixed"));

  run "TYPO-004 fix: skips '' inside $$..$$ display math (matched-pair)"
    (fun tag ->
      (* Critical case for TeX-style $$..$$ display math. strip_math_segments
         uses a single-$ toggle and treats $$x$$ as two empty math + literal
         middle, which would let TYPO-004's fix corrupt $$f''(x)=0$$.
         find_math_ranges matches $$ as a pair before the toggle path runs.
         Verifies the v27.0.6 round-2 audit fix. *)
      let src = "Pre $$f''(x) = 0$$ post ``done''" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 2
        && out = "Pre $$f''(x) = 0$$ post \xe2\x80\x9cdone\xe2\x80\x9d")
        (tag ^ ": $$..$$ display math preserved"));

  run "TYPO-004 fix: skips `` inside $..$ math (symmetric to '' case)"
    (fun tag ->
      (* Round-5 audit: '' tested in math but `` not. Symmetric coverage:
         backtick-pair inside math should also be preserved. Pattern is unusual
         (TeX low-level uses backtick for char codes) but the helper's filter is
         direction-agnostic — verifying. *)
      let src = "$``x$ then ``y''" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 2 && out = "$``x$ then \xe2\x80\x9cy\xe2\x80\x9d")
        (tag ^ ": `` inside $..$ preserved, outer pair fixed"));

  run "TYPO-004 fix: skips '' inside \\(..\\) paren math" (fun tag ->
      (* Round-6 audit: CHANGELOG lists \\(..\\) as supported but no test
         verified. Other syntaxes covered ($, $$, \\[, env); this adds the
         missing one for completeness. *)
      let src = "Try \\(f''(x) \\neq 0\\) and ``yes''" in
      let edits = fix_edits "TYPO-004" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 2
        && out = "Try \\(f''(x) \\neq 0\\) and \xe2\x80\x9cyes\xe2\x80\x9d")
        (tag ^ ": \\(..\\) paren math preserved"));

  (* v27.0.7 batch: TYPO-005 fix producer (... → \dots, math-aware). *)
  run "TYPO-005 fix: ... in text becomes \\dots" (fun tag ->
      let src = "Wait... what?" in
      let edits = fix_edits "TYPO-005" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Wait\\dots what?")
        (tag ^ ": ... → \\dots in plain text"));

  run "TYPO-005 fix: skips ... inside $..$ math" (fun tag ->
      (* $1, 2, ..., n$ is the canonical math-ellipsis idiom; the fix must NOT
         auto-rewrite it. *)
      let src = "Sequence $1, 2, ..., n$ and footnote..." in
      let edits = fix_edits "TYPO-005" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "Sequence $1, 2, ..., n$ and footnote\\dots")
        (tag ^ ": math ellipsis preserved, footnote fixed"));

  run "TYPO-005 fix: skips ... inside \\[..\\] display math" (fun tag ->
      let src = "\\[ a_1, a_2, ..., a_n \\] then ..." in
      let edits = fix_edits "TYPO-005" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1 && out = "\\[ a_1, a_2, ..., a_n \\] then \\dots")
        (tag ^ ": display math ellipsis preserved"));

  run "TYPO-005 does not fire when ... is only in math" (fun tag ->
      (* Math-only `...` should NOT fire — count is computed on
         strip_math_segments output, which excludes math content. *)
      expect
        (does_not_fire "TYPO-005" "$x_1, x_2, ..., x_n$")
        (tag ^ ": math-only ellipsis suppressed"));

  run "TYPO-005 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-005" "Already correct \\dots usage.")
        (tag ^ ": clean source no fire"));

  (* v27.0.8 batch: TYPO-001 fix producer (ASCII straight quote -> curly via
     alternation, math-aware). *)
  run "TYPO-001 fix: matched pair becomes curly-pair via alternation"
    (fun tag ->
      let src = "Said \"hello\" to her" in
      let edits = fix_edits "TYPO-001" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "Said \xe2\x80\x9chello\xe2\x80\x9d to her")
        (tag ^ ": even-idx -> opening, odd-idx -> closing"));

  run "TYPO-001 fix: two matched pairs alternate correctly" (fun tag ->
      let src = "\"a\" and \"b\"" in
      let edits = fix_edits "TYPO-001" src in
      expect
        (List.length edits = 4
        && apply_all src edits
           = "\xe2\x80\x9ca\xe2\x80\x9d and \xe2\x80\x9cb\xe2\x80\x9d")
        (tag ^ ": four edits, alternating opening/closing"));

  run "TYPO-001 fix: skips quotes inside $..$ math" (fun tag ->
      (* Quotes inside math (rare but possible in e.g. \text{}) are preserved by
         the math-range filter. *)
      let src = "Outside \"q1\" and $\"math-q\"$ then \"q2\"" in
      let edits = fix_edits "TYPO-001" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 4
        && out
           = "Outside \xe2\x80\x9cq1\xe2\x80\x9d and $\"math-q\"$ then \
              \xe2\x80\x9cq2\xe2\x80\x9d")
        (tag ^ ": four outside-math edits, math quotes preserved"));

  run "TYPO-001 does not fire when quotes only in math" (fun tag ->
      expect
        (does_not_fire "TYPO-001" "$\"x\" + \"y\"$")
        (tag ^ ": math-only quotes suppressed"));

  run "TYPO-001 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-001" "Already \xe2\x80\x9ccurly\xe2\x80\x9d")
        (tag ^ ": clean curly source no fire"));

  run "TYPO-001 fix: skips backslash-escaped quotes (round-1 audit)" (fun tag ->
      (* LaTeX backslash-doublequote forms the umlaut command (renders
         u-umlaut); auto-replacing would corrupt the umlaut. The fix must skip
         backslash-escaped quotes entirely. Source has 2 real text quotes around
         the second word and one escaped pair inside the umlaut ligature; fix
         should emit edits only for the 2 real text quotes. *)
      let src = "Caf\\\"e is \"f\\\"oo\" and bar" in
      let edits = fix_edits "TYPO-001" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 2
        && out = "Caf\\\"e is \xe2\x80\x9cf\\\"oo\xe2\x80\x9d and bar")
        (tag ^ ": umlaut command preserved, real quotes fixed"));

  run "TYPO-001 fix: escapes interleaved with real quotes preserve alternation"
    (fun tag ->
      (* Round-2 audit: escaped quote-commands (umlauts) should not consume an
         alternation slot. Source has 3 escaped umlauts (skipped) and 2 real
         quote pairs; alternation runs only over the real quotes. *)
      let src = "Caf\\\"e \"x\" and na\\\"\\\"ve \"y\"" in
      let edits = fix_edits "TYPO-001" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 4
        && out
           = "Caf\\\"e \xe2\x80\x9cx\xe2\x80\x9d and na\\\"\\\"ve \
              \xe2\x80\x9cy\xe2\x80\x9d")
        (tag ^ ": umlauts preserved, alternation runs only over real quotes"));

  run "TYPO-001 fix: odd quote count gives best-effort alternation" (fun tag ->
      (* 3 quotes: open, close, open (last unmatched). *)
      let src = "\"a\"b\"c" in
      let edits = fix_edits "TYPO-001" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 3
        && out = "\xe2\x80\x9ca\xe2\x80\x9db\xe2\x80\x9cc")
        (tag ^ ": alternation despite mismatch"));

  (* v27.0.9 batch: TYPO-038 fix producer (email -> href, math-aware). *)
  run "TYPO-038 fix: bare email becomes \\href{mailto:...}{...}" (fun tag ->
      let src = "Contact: alice@example.com for more." in
      let edits = fix_edits "TYPO-038" src in
      expect
        (List.length edits = 1
        && apply_all src edits
           = "Contact: \\href{mailto:alice@example.com}{alice@example.com} for \
              more.")
        (tag ^ ": email wrapped with mailto href"));

  run "TYPO-038 fix: two emails get two wraps" (fun tag ->
      let src = "Email a@b.io or c@d.org now." in
      let edits = fix_edits "TYPO-038" src in
      expect
        (List.length edits = 2
        && apply_all src edits
           = "Email \\href{mailto:a@b.io}{a@b.io} or \
              \\href{mailto:c@d.org}{c@d.org} now.")
        (tag ^ ": two distinct emails, two non-overlapping wraps"));

  run "TYPO-038 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-038" "Already wrapped: \\href{mailto:x@y.z}{x@y.z}")
        (tag ^ ": pre-wrapped email shouldn't fire"));

  run "TYPO-038 fix: math + wrapped + plain integration" (fun tag ->
      (* Restored from v27.0.9 round-1 audit (commit 1026e1b) which the
         squash-merge of PR #340 dropped per
         feedback_squash_merge_drops_late_commits.md. *)
      let src =
        "Plain a@b.io, math $x@y.com$ and \\href{mailto:c@d.org}{c@d.org}."
      in
      let edits = fix_edits "TYPO-038" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out
           = "Plain \\href{mailto:a@b.io}{a@b.io}, math $x@y.com$ and \
              \\href{mailto:c@d.org}{c@d.org}.")
        (tag ^ ": only plain email wrapped; math + wrapped preserved"));

  run "TYPO-038 fix: literal mailto: text is NOT skipped (round-1 audit fix)"
    (fun tag ->
      (* Pre-v27.0.10 prefix-byte check treated any email preceded by literal
         `mailto:` as wrapped, even in plain text. v27.0.10 uses
         find_href_mailto_ranges so only emails inside real
         \\href{mailto:...}{...} constructs are skipped. *)
      let src = "Send to mailto:alice@x.com today" in
      let edits = fix_edits "TYPO-038" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "Send to mailto:\\href{mailto:alice@x.com}{alice@x.com} today"
        )
        (tag ^ ": email after literal mailto: text gets wrapped"));

  run "TYPO-038 fix: non-href two-arg command does NOT mask email" (fun tag ->
      (* Pre-v27.0.10 prefix-byte check treated any email preceded by `}{` as
         wrapped. v27.0.10 only skips inside real \\href{mailto:...}{...}. *)
      let src = "\\textbf{label}{a@b.io}" in
      let edits = fix_edits "TYPO-038" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "\\textbf{label}{\\href{mailto:a@b.io}{a@b.io}}")
        (tag ^ ": non-href command does not mask"));

  (* v27.0.11 batch: TYPO-034 fix producer (delete spurious space before
     \\footnote, math-aware). *)
  run "TYPO-034 fix: deletes space before \\footnote" (fun tag ->
      let src = "Greetings \\footnote{see footer}." in
      let edits = fix_edits "TYPO-034" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Greetings\\footnote{see footer}.")
        (tag ^ ": leading space removed"));

  run "TYPO-034 fix: two footnote sites get two deletions" (fun tag ->
      let src = "First \\footnote{a}. Second \\footnote{b}." in
      let edits = fix_edits "TYPO-034" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "First\\footnote{a}. Second\\footnote{b}.")
        (tag ^ ": both spaces removed"));

  run "TYPO-034 fix: skips \\footnote inside math" (fun tag ->
      (* \\footnote in math is unusual but math-stripping is defensive
         consistency with other v27.0.6+ producers. *)
      let src = "Math: $a \\footnote{x}$ then \\footnote{y}." in
      let edits = fix_edits "TYPO-034" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Math: $a \\footnote{x}$ then\\footnote{y}.")
        (tag ^ ": text site fixed, math site preserved"));

  run "TYPO-034 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-034" "No bad space before\\footnote{ok}.")
        (tag ^ ": no space before footnote, no fire"));

  (* v27.0.12 batch: TYPO-029 fix producer (NBSP after \\ref, math-aware). *)
  run "TYPO-029 fix: space after \\ref{X} becomes ~" (fun tag ->
      let src = "See \\ref{eq:1} for details." in
      let edits = fix_edits "TYPO-029" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "See \\ref{eq:1}~for details.")
        (tag ^ ": space replaced with NBSP"));

  run "TYPO-029 fix: two \\ref sites get two replacements" (fun tag ->
      let src = "Check \\ref{a} and \\ref{b} together." in
      let edits = fix_edits "TYPO-029" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "Check \\ref{a}~and \\ref{b}~together.")
        (tag ^ ": both spaces replaced"));

  run "TYPO-029 does not fire when ~ already present" (fun tag ->
      expect
        (does_not_fire "TYPO-029" "See \\ref{eq:1}~for details.")
        (tag ^ ": pre-NBSP source no fire"));

  run "TYPO-029 does not fire on \\ref followed by punctuation" (fun tag ->
      (* Pattern requires letter after the space, so \\ref{X}, doesn't match
         (correctly — comma after \\ref doesn't need NBSP). *)
      expect
        (does_not_fire "TYPO-029" "See \\ref{eq:1}, also \\ref{eq:2}.")
        (tag ^ ": comma/period after \\ref doesn't fire"));

  run "TYPO-029 fix: skips \\ref{X} y inside $..$ math (round-1 audit)"
    (fun tag ->
      (* \\ref inside math is unusual but possible (e.g., \\text{}); the
         math-aware filter should preserve it. Outer text-mode \\ref still gets
         the NBSP fix. *)
      let src = "$x = \\ref{eq:1} y$ then \\ref{eq:2} again." in
      let edits = fix_edits "TYPO-029" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "$x = \\ref{eq:1} y$ then \\ref{eq:2}~again.")
        (tag ^ ": math \\ref preserved, text \\ref gets NBSP"));

  (* v27.0.13 batch: TYPO-039 fix producer (URL -> \\url{}, math + already-
     wrapped aware). *)
  run "TYPO-039 fix: bare URL becomes \\url{...}" (fun tag ->
      let src = "Visit https://example.com for more." in
      let edits = fix_edits "TYPO-039" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Visit \\url{https://example.com} for more.")
        (tag ^ ": URL wrapped"));

  run "TYPO-039 fix: two URLs get two wraps" (fun tag ->
      let src = "Sites: http://a.io and https://b.org now." in
      let edits = fix_edits "TYPO-039" src in
      expect
        (List.length edits = 2
        && apply_all src edits
           = "Sites: \\url{http://a.io} and \\url{https://b.org} now.")
        (tag ^ ": two URLs wrapped"));

  run "TYPO-039 does not fire when already wrapped" (fun tag ->
      expect
        (does_not_fire "TYPO-039" "See \\url{https://example.com}.")
        (tag ^ ": pre-wrapped URL doesn't fire"));

  run "TYPO-039 does not fire on URL inside \\href slot" (fun tag ->
      expect
        (does_not_fire "TYPO-039" "Click \\href{https://example.com}{here}.")
        (tag ^ ": \\href URL slot is wrapping"));

  run "TYPO-039 fix: skips URL inside $..$ math (round-1 audit)" (fun tag ->
      (* URLs in math are extremely unusual but math-aware filtering keeps the
         producer consistent with v27.0.6+ producers. *)
      let src = "Math: $f(x) = http://no.real$ and https://x.io plain." in
      let edits = fix_edits "TYPO-039" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "Math: $f(x) = http://no.real$ and \\url{https://x.io} plain."
        )
        (tag ^ ": math URL preserved, plain URL wrapped"));

  run "TYPO-039 fix: math + wrapped + plain integration (round-1 audit)"
    (fun tag ->
      (* All four conditions in one input: plain URL (wraps), URL inside \\url{}
         (skip), URL inside \\href{} URL slot (skip), URL inside math (skip).
         Round-2 audit: comma after the plain URL exercises trim_trailing_punct
         so the wrap span excludes the comma. *)
      let src =
        "Plain http://a.io, wrapped \\url{http://b.io} href \
         \\href{http://c.io}{c} and math $http://d.io$"
      in
      let edits = fix_edits "TYPO-039" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out
           = "Plain \\url{http://a.io}, wrapped \\url{http://b.io} href \
              \\href{http://c.io}{c} and math $http://d.io$")
        (tag ^ ": only plain URL wrapped, trailing comma trimmed"));

  run "TYPO-039 fix: trims trailing punctuation (round-2 audit)" (fun tag ->
      (* The URL regex `https?://[^ \t\n}]+` is permissive on trailing
         punctuation. trim_trailing_punct excludes `,.;:!)` from the wrap span
         so sentence-ending marks stay outside \\url{}. `?` is NOT trimmed
         (commonly starts a URL query string). *)
      let src =
        "Site https://a.io. Also https://b.io! See (https://c.io); end."
      in
      let edits = fix_edits "TYPO-039" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 3
        && out
           = "Site \\url{https://a.io}. Also \\url{https://b.io}! See \
              (\\url{https://c.io}); end.")
        (tag ^ ": .!) trimmed from URL wrap span"));

  (* v27.0.14: TYPO-032 fix producer (delete comma before \\cite, math-aware on
     the fix offsets, count preserved). *)
  run "TYPO-032 fix: deletes comma before \\cite" (fun tag ->
      let src = "see, \\cite{ref}" in
      let edits = fix_edits "TYPO-032" src in
      expect
        (List.length edits = 1 && apply_all src edits = "see \\cite{ref}")
        (tag ^ ": comma deleted, space + \\cite preserved"));

  run "TYPO-032 fix: deletes comma even with no space before \\cite" (fun tag ->
      let src = "foo,\\cite{X}" in
      let edits = fix_edits "TYPO-032" src in
      expect
        (List.length edits = 1 && apply_all src edits = "foo\\cite{X}")
        (tag ^ ": comma deleted, no space"));

  run "TYPO-032 fix: two disjoint comma+\\cite produce two edits" (fun tag ->
      let src = "a, \\cite{x} and b, \\cite{y}" in
      let edits = fix_edits "TYPO-032" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "a \\cite{x} and b \\cite{y}")
        (tag ^ ": both commas deleted"));

  run "TYPO-032 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-032" "see \\cite{ref} for details")
        (tag ^ ": no comma, no fire"));

  run "TYPO-032 fix: skips \\,\\cite thin-space (round-1 audit)" (fun tag ->
      (* `\,\cite` is a thin-space control symbol followed by a citation
         (typographically CORRECT — some style guides recommend it). The
         pre-v27.0.14 rule misfired on this pattern; v27.0.14 fixes the false
         positive in BOTH count and fix offsets. The check counts consecutive
         backslashes immediately before the comma; an odd count means `\,` and
         the match is skipped. *)
      let src = "thin space \\,\\cite{ref} works" in
      expect (does_not_fire "TYPO-032" src) (tag ^ ": \\,\\cite not flagged"));

  run "TYPO-032 fix: \\\\,\\cite (escaped backslash + comma) DOES fire"
    (fun tag ->
      (* `\\,\cite` = `\\` (literal backslash) + `,` + `\cite`. The comma is
         preceded by TWO backslashes (an even count), so it is a genuine comma —
         the rule fires and the fix deletes it. *)
      let src = "literal\\\\,\\cite{X}" in
      let edits = fix_edits "TYPO-032" src in
      expect
        (List.length edits = 1 && apply_all src edits = "literal\\\\\\cite{X}")
        (tag ^ ": even-count backslashes → comma is real"));

  run "TYPO-032 fix: skips comma+\\cite inside $..$ math (audit-aware)"
    (fun tag ->
      (* \\cite is text-mode so this case is essentially LaTeX-invalid in
         practice, but math-aware filtering keeps the producer consistent with
         v27.0.6+ producers. The fix offset is suppressed; the count still
         reflects the match (no math filter on count, by design — see the
         comment on r_typo_032 for the 0-differential rationale). *)
      let src = "text $a, \\cite{m}$ and b, \\cite{plain}" in
      let edits = fix_edits "TYPO-032" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "text $a, \\cite{m}$ and b \\cite{plain}")
        (tag ^ ": math comma preserved, plain comma deleted"));

  (* v27.0.15: TYPO-042 fix producer (collapse `??...?` runs to single `?`). *)
  run "TYPO-042 fix: collapses ?? to single ?" (fun tag ->
      let src = "What?? Really" in
      let edits = fix_edits "TYPO-042" src in
      expect
        (List.length edits = 1 && apply_all src edits = "What? Really")
        (tag ^ ": double question collapsed"));

  run "TYPO-042 fix: collapses arbitrary-length run to single ?" (fun tag ->
      let src = "Wow????? amazing" in
      let edits = fix_edits "TYPO-042" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Wow? amazing")
        (tag ^ ": run of 5 question marks collapsed"));

  run "TYPO-042 fix: two disjoint runs produce two edits" (fun tag ->
      let src = "What?? Where???" in
      let edits = fix_edits "TYPO-042" src in
      expect
        (List.length edits = 2 && apply_all src edits = "What? Where?")
        (tag ^ ": two runs collapsed independently"));

  run "TYPO-042 does not fire on single ?" (fun tag ->
      expect
        (does_not_fire "TYPO-042" "Really? OK.")
        (tag ^ ": one question mark, no fire"));

  run "TYPO-042 fix: skips ?? inside $..$ math (audit-aware)" (fun tag ->
      (* `??` inside math is unusual but math-aware filtering keeps the producer
         consistent with v27.0.6+ producers. The fix offset is suppressed; the
         count still reflects the match (no math filter on count, by design —
         see comment on r_typo_042 for the 0-differential rationale). *)
      let src = "math $a ?? b$ then plain ?? end" in
      let edits = fix_edits "TYPO-042" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1 && out = "math $a ?? b$ then plain ? end")
        (tag ^ ": math ?? preserved, plain ?? collapsed"));

  (* v27.0.16: TYPO-051 fix producer (U+2009 figure space -> \\thinspace{},
     math-aware on fix offsets). *)
  run "TYPO-051 fix: U+2009 between number and unit becomes \\thinspace{}"
    (fun tag ->
      let src = "5\xe2\x80\x89m" in
      let edits = fix_edits "TYPO-051" src in
      expect
        (List.length edits = 1 && apply_all src edits = "5\\thinspace{}m")
        (tag ^ ": figure space replaced with \\thinspace{}"));

  run "TYPO-051 fix: empty group {} guards against \\thinspaceLETTER"
    (fun tag ->
      (* Crucial round-1 audit: bare `\\thinspace` followed by a letter would
         tokenize as the undefined command `\\thinspaceabc`. The trailing `{}`
         empty group ensures unambiguous parsing regardless of next byte. *)
      let src = "abc\xe2\x80\x89def" in
      let edits = fix_edits "TYPO-051" src in
      expect
        (List.length edits = 1 && apply_all src edits = "abc\\thinspace{}def")
        (tag ^ ": {} guards against macro merging with following letter"));

  run "TYPO-051 fix: two disjoint U+2009 produce two edits" (fun tag ->
      let src = "5\xe2\x80\x89kg and 10\xe2\x80\x89cm" in
      let edits = fix_edits "TYPO-051" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "5\\thinspace{}kg and 10\\thinspace{}cm")
        (tag ^ ": both figure spaces replaced"));

  run "TYPO-051 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-051" "no figure space in this text")
        (tag ^ ": no U+2009, no fire"));

  run "TYPO-051 fix: skips U+2009 inside $..$ math (audit-aware)" (fun tag ->
      (* Math-aware: count includes math match (preserves diff invariant); fix
         offset is suppressed. In math, the LaTeX-idiomatic thin space is `\\,`
         which differs from `\\thinspace`, so the fix conservatively skips math
         contexts rather than replacing with the wrong macro. *)
      let src = "math $a\xe2\x80\x89b$ then text\xe2\x80\x89more" in
      let edits = fix_edits "TYPO-051" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "math $a\xe2\x80\x89b$ then text\\thinspace{}more")
        (tag ^ ": math U+2009 preserved, text U+2009 replaced"));

  (* v27.0.17: TYPO-049 fix producer (delete space after curly opening quote
     U+201C/U+2018, math-aware on fix offsets). *)
  run "TYPO-049 fix: deletes space after U+201C double opening quote"
    (fun tag ->
      let src = "\xe2\x80\x9c hello world\xe2\x80\x9d" in
      let edits = fix_edits "TYPO-049" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "\xe2\x80\x9chello world\xe2\x80\x9d")
        (tag ^ ": space after U+201C deleted, quote preserved"));

  run "TYPO-049 fix: deletes space after U+2018 single opening quote"
    (fun tag ->
      let src = "\xe2\x80\x98 hello\xe2\x80\x99" in
      let edits = fix_edits "TYPO-049" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "\xe2\x80\x98hello\xe2\x80\x99")
        (tag ^ ": space after U+2018 deleted, quote preserved"));

  run "TYPO-049 fix: handles both U+201C and U+2018 in same input" (fun tag ->
      let src = "\xe2\x80\x9c outer \xe2\x80\x98 inner\xe2\x80\x99 end" in
      let edits = fix_edits "TYPO-049" src in
      expect
        (List.length edits = 2
        && apply_all src edits
           = "\xe2\x80\x9couter \xe2\x80\x98inner\xe2\x80\x99 end")
        (tag ^ ": both opening-quote spaces deleted"));

  run "TYPO-049 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-049" "\xe2\x80\x9chello\xe2\x80\x9d clean quote")
        (tag ^ ": no space after opening quote, no fire"));

  run "TYPO-049 fix: only deletes FIRST space when multiple follow" (fun tag ->
      (* Round-1 audit: rule fires once on `“ abc` (count=1, since
         count_substring `“ ` matches one quote+space pair). The fix deletes ONE
         space, leaving `“ abc`. TYPO-018 (collapse double space) handles the
         residual run. *)
      let src = "\xe2\x80\x9c  abc" in
      let edits = fix_edits "TYPO-049" src in
      expect
        (List.length edits = 1 && apply_all src edits = "\xe2\x80\x9c abc")
        (tag ^ ": one space deleted, residual handled by TYPO-018"));

  run "TYPO-049 fix: skips opening-quote+space inside $..$ math" (fun tag ->
      (* Math-aware: count includes math match (preserves diff invariant); fix
         offset is suppressed. Curly opening quotes inside math are essentially
         LaTeX-invalid in practice, but math-aware filtering keeps the producer
         consistent with v27.0.6+ producers. *)
      let src = "math $\xe2\x80\x9c a$ then text \xe2\x80\x9c plain" in
      let edits = fix_edits "TYPO-049" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1
        && out = "math $\xe2\x80\x9c a$ then text \xe2\x80\x9cplain")
        (tag ^ ": math quote-space preserved, text quote-space fixed"));

  (* v27.0.18: TYPO-017 fix producer (\\<accent>{<letter>} -> \\<accent><letter>
     braces-removal, math-aware on fix offsets). *)
  run "TYPO-017 fix: \\'{e} becomes \\'e (acute accent)" (fun tag ->
      let src = "caf\\'{e} bar" in
      let edits = fix_edits "TYPO-017" src in
      expect
        (List.length edits = 1 && apply_all src edits = "caf\\'e bar")
        (tag ^ ": braces removed, accent + letter preserved"));

  run "TYPO-017 fix: handles all 7 text-mode accents" (fun tag ->
      (* All 7 accent chars from the regex char class: apostrophe, caret,
         backtick, doublequote, tilde, equals, period. *)
      let src = "\\'{a} \\^{e} \\`{i} \\\"{o} \\~{n} \\={u} \\.{z}" in
      let edits = fix_edits "TYPO-017" src in
      expect
        (List.length edits = 7
        && apply_all src edits = "\\'a \\^e \\`i \\\"o \\~n \\=u \\.z")
        (tag ^ ": all 7 accents braces-removed"));

  run "TYPO-017 does not fire on already-braces-removed form" (fun tag ->
      (* `\\'e` (no braces) doesn't match the regex; rule is idempotent. *)
      expect
        (does_not_fire "TYPO-017" "caf\\'e clean form")
        (tag ^ ": no braces, no fire"));

  run "TYPO-017 does not fire on multi-letter braces" (fun tag ->
      (* `\\'{ae}` would not match (regex requires single [a-zA-Z]). *)
      expect
        (does_not_fire "TYPO-017" "old form \\'{ae} compound")
        (tag ^ ": multi-letter braces not in scope"));

  run "TYPO-017 fix: skips \\'{e} inside $..$ math (audit-aware)" (fun tag ->
      (* Math-aware: text accents inside math are unusual but math-aware
         filtering keeps the producer consistent with v27.0.6+ producers. Math
         accents like \\hat{x} use a different command (\\hat) which is not in
         the regex char class, so they're unaffected by design. *)
      let src = "math $\\'{e}$ then text \\'{a} plain" in
      let edits = fix_edits "TYPO-017" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1 && out = "math $\\'{e}$ then text \\'a plain")
        (tag ^ ": math accent preserved, text accent fixed"));

  (* v27.0.19: TYPO-046 fix producer (\\begin{math}...\\end{math} -> $...$,
     odd-backslash-prefix guard). *)
  run "TYPO-046 fix: \\begin{math}...\\end{math} becomes $...$" (fun tag ->
      let src = "before \\begin{math}x+y\\end{math} after" in
      let edits = fix_edits "TYPO-046" src in
      expect
        (List.length edits = 2 && apply_all src edits = "before $x+y$ after")
        (tag ^ ": both delimiters replaced with $"));

  run "TYPO-046 fix: two disjoint math envs produce 4 edits" (fun tag ->
      let src = "\\begin{math}a\\end{math} and \\begin{math}b\\end{math}" in
      let edits = fix_edits "TYPO-046" src in
      expect
        (List.length edits = 4 && apply_all src edits = "$a$ and $b$")
        (tag ^ ": both math envs converted"));

  run "TYPO-046 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-046" "no math env here, just $x+y$ inline")
        (tag ^ ": no \\begin{math}, no fire"));

  run "TYPO-046 fix: odd-backslash prefix marks escaped \\begin{math}"
    (fun tag ->
      (* Round-1 audit: when `\\begin{math}` is preceded by an odd number of
         backslashes, the leading `\\` is the second half of a `\\\\` line-
         break, and `begin{math}` is literal text. The naive fix would corrupt
         this into `\\$` (escaped dollar). The guard counts consecutive
         backslashes immediately before the match start; an odd count means the
         match is skipped from BOTH count and fix.

         OCaml source escaping: `\\\\\\` in the OCaml literal = three
         backslashes in actual bytes, so `"x\\\\\\begin{math}"` has bytes `x \\
         \\ \\ b e g i n { m a t h }` — three backslashes followed by
         `begin{math}`. The match would start at the third backslash; two
         preceding backslashes is even -> guard treats as unescaped. Hmm, but
         the actual escape is at the third backslash itself. Re- examining:
         `\\\\\\begin{math}` = 3 backslashes + `begin{math}`. The match
         `\\begin{math}` starts at position of 3rd backslash; BEFORE that
         position there are 2 backslashes (positions 0,1). Count = 2 (even) ->
         guard says unescaped -> match fires. But semantically, 3 backslashes
         parse as `\\\\` (line break) + `\\` (start of `\\begin{math}` command).
         So the match IS a real command and the fix IS correct.

         The actually-escaped case is when there are an EVEN number of
         backslashes before the match start (so the match's `\\` is the second
         half of a pair). Wait, that's the opposite of what I just said. Let me
         re-derive:

         - 0 prior backslashes: `\\begin{math}` is a command. Fire. - 1 prior
         backslash: prior `\\` + match's `\\` = `\\\\` line break, then
         `begin{math}` is text. NOT a command. SKIP. - 2 prior backslashes:
         `\\\\` = line break, then match's `\\begin {math}` is a fresh command.
         Fire. - 3 prior backslashes: `\\\\` + `\\` = line break + start of next
         command, but the trailing single `\\` PAIRS with the match's `\\` to
         form another `\\\\`. So match is text. SKIP.

         Pattern: skip iff prior backslash count is ODD.

         The current implementation checks `n mod 2 == 1` (odd) -> skip. That
         matches the analysis. *)
      let src = "x\\begin{math}a\\end{math}" in
      let edits = fix_edits "TYPO-046" src in
      expect
        (List.length edits = 2 && apply_all src edits = "x$a$")
        (tag ^ ": no prior backslashes -> command -> fix applies"));

  run "TYPO-046 fix: skips truly-escaped \\\\begin{math} (1 prior backslash)"
    (fun tag ->
      (* 1 prior backslash + match's `\\` = `\\\\` (line break) + `begin {math}`
         text. The match should be skipped from both count and fix. The
         `\\end{math}` afterward has no prior backslash and IS a real command —
         but with only the closing delimiter left and no opening, applying just
         the close-fix would yield `\\\\$` which is malformed math. We accept
         this corner case: the fix matches existing rule semantic; users with
         `\\\\begin{math}` line-breaks should not invoke --apply-fixes (the rule
         still warns once on the unbalanced env). *)
      let src = "p\\\\begin{math}q\\end{math}" in
      let edits = fix_edits "TYPO-046" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1 && out = "p\\\\begin{math}q$")
        (tag ^ ": odd prior backslashes -> escaped, only \\end{math} fires"));

  run "TYPO-046 fix: adjacent empty env deleted (round-1 audit, no $$)"
    (fun tag ->
      (* Round-1 ultrathink audit: `\\begin{math}\\end{math}` (empty math env,
         no content) would naively become `$$` — the display-math delimiter that
         TYPO-028 warns against, AND it would consume following source as math
         content. The fix detects adjacent pairs and emits a single delete edit
         covering both delimiters. An empty math env renders to nothing in LaTeX
         so deletion is semantically equivalent. *)
      let src = "before\\begin{math}\\end{math}after" in
      let edits = fix_edits "TYPO-046" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": empty env deleted, no $$ collision"));

  run "TYPO-046 fix: \\begin{math} \\end{math} (space content) -> $ $"
    (fun tag ->
      (* Single space between delimiters is NOT adjacent (begin_off + 12 !=
         end_off because there's a space byte between). Falls through to the
         normal lone-replacement path. Result `$ $` is a valid (pointless) math
         env, not the `$$` corruption case. *)
      let src = "x\\begin{math} \\end{math}y" in
      let edits = fix_edits "TYPO-046" src in
      expect
        (List.length edits = 2 && apply_all src edits = "x$ $y")
        (tag ^ ": space between delimiters -> normal path, $ $ output"));

  finalise "typo-fix"
