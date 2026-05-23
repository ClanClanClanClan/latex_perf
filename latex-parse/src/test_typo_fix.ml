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

  (* v27.0.20: TYPO-028 fix producer ($$..$$ -> \[..\] pair-matching,
     escape-aware). *)
  run "TYPO-028 fix: $$ X $$ becomes \\[ X \\]" (fun tag ->
      let src = "before $$ X $$ after" in
      let edits = fix_edits "TYPO-028" src in
      expect
        (List.length edits = 2 && apply_all src edits = "before \\[ X \\] after")
        (tag ^ ": pair converted to \\[..\\]"));

  run "TYPO-028 fix: two disjoint pairs produce 4 edits" (fun tag ->
      let src = "$$a$$ and $$b$$" in
      let edits = fix_edits "TYPO-028" src in
      expect
        (List.length edits = 4 && apply_all src edits = "\\[a\\] and \\[b\\]")
        (tag ^ ": two pairs each converted"));

  run "TYPO-028 fix: $$$$ (empty display math) -> \\[\\]" (fun tag ->
      (* 4 consecutive $: non-overlapping offsets [0, 2]. Pair (0, 2). Fix emits
         \\[ at [0,2) and \\] at [2,4). Result: \\[\\] = empty display math.
         Valid LaTeX. *)
      let src = "x$$$$y" in
      let edits = fix_edits "TYPO-028" src in
      expect
        (List.length edits = 2 && apply_all src edits = "x\\[\\]y")
        (tag ^ ": empty display math converted, no corruption"));

  run "TYPO-028 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-028" "no display math here")
        (tag ^ ": no $$, no fire"));

  run "TYPO-028 fix: skips \\$$ (escaped $, round-1 audit)" (fun tag ->
      (* `\$$` parses as `\$` (escaped dollar) + `$` (open inline math), NOT a
         display-math delimiter. The substring `$$` at the position after `\`
         would naively match, but the escape guard skips it (odd prior backslash
         count -> escaped). *)
      let src = "literal\\$$ value" in
      expect
        (does_not_fire "TYPO-028" src)
        (tag ^ ": \\$$ correctly identified as escaped, no fire"));

  run "TYPO-028 fix: \\\\$$ (line break + $$, round-1 audit)" (fun tag ->
      (* `\\\\$$` in OCaml literal = `\\$$` in source: `\\` (line break) + `$$`
         (real display math delimiter). Even count of prior backslashes (2)
         means unescaped -> match fires. *)
      let src = "x\\\\$$ a $$y" in
      let edits = fix_edits "TYPO-028" src in
      expect
        (List.length edits = 2 && apply_all src edits = "x\\\\\\[ a \\]y")
        (tag ^ ": even-count backslashes -> real $$, fix applies"));

  run "TYPO-028 fix: odd $$$ (3 chars) only counts but doesn't fix" (fun tag ->
      (* 3 consecutive $: count_substring overlap = 2, count = 2/2 = 1 (rule
         still warns); find_all_non_overlapping = 1 offset; pairs = []; no fix
         emitted. *)
      let src = "x$$$y" in
      let edits = fix_edits "TYPO-028" src in
      expect (List.length edits = 0) (tag ^ ": odd run -> no pair, no fix"));

  (* v27.0.21: TYPO-012 fix producer (digit + apostrophe -> digit + ^\prime,
     math-only fix). *)
  run "TYPO-012 fix: 5' inside math becomes 5^\\prime" (fun tag ->
      let src = "$f(5') = g$" in
      let edits = fix_edits "TYPO-012" src in
      expect
        (List.length edits = 1 && apply_all src edits = "$f(5^\\prime) = g$")
        (tag ^ ": math digit-prime fixed"));

  run "TYPO-012 fix: outside math, 5' is NOT fixed (ambiguous)" (fun tag ->
      (* `5'` outside math could be possessive (1980s) or feet/minutes (5 ft 2
         in). Math-only fix is conservative. The rule still warns (count
         includes outside-math matches) but the fix doesn't apply. *)
      let src = "the 1980's were great" in
      let edits = fix_edits "TYPO-012" src in
      expect (List.length edits = 0) (tag ^ ": text-mode digit-prime not fixed"));

  run "TYPO-012 fix: two math primes produce two edits" (fun tag ->
      let src = "$x = 5'$ and $y = 7'$" in
      let edits = fix_edits "TYPO-012" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "$x = 5^\\prime$ and $y = 7^\\prime$")
        (tag ^ ": both math primes fixed"));

  run "TYPO-012 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-012" "no apostrophe-after-digit here")
        (tag ^ ": no [0-9]', no fire"));

  run "TYPO-012 fix: idempotent on already-fixed math" (fun tag ->
      (* After fix, `5^\prime` doesn't match `[0-9]'` (no apostrophe right after
         digit). Rule doesn't fire on the fixed form. *)
      expect
        (does_not_fire "TYPO-012" "$x = 5^\\prime$")
        (tag ^ ": fixed form doesn't re-fire"));

  run "TYPO-012 fix: mixed math/text counts both, fixes only math" (fun tag ->
      (* Math `5'` is fixed; text `1980's` is not. Count includes both
         (preserves pre-v27.0.21 semantic for 0-differential). *)
      let src = "the 1980's $f(5')$ end" in
      let edits = fix_edits "TYPO-012" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 1 && out = "the 1980's $f(5^\\prime)$ end")
        (tag ^ ": math fixed, text untouched"));

  (* v27.0.22: ENC-007 fix producer (delete U+200B zero-width space, single
     3-byte UTF-8 needle, mechanical deletion). First fix in ENC family beyond
     ENC-002 (BOM deletion). *)
  run "ENC-007 fix: deletes single U+200B zero-width space" (fun tag ->
      let src = "hello\xe2\x80\x8bworld" in
      let edits = fix_edits "ENC-007" src in
      expect
        (List.length edits = 1 && apply_all src edits = "helloworld")
        (tag ^ ": ZWSP deleted"));

  run "ENC-007 fix: multiple ZWSP all deleted" (fun tag ->
      let src = "a\xe2\x80\x8bb\xe2\x80\x8bc\xe2\x80\x8bd" in
      let edits = fix_edits "ENC-007" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three ZWSP deleted"));

  run "ENC-007 fix: ZWSP at start, middle, and end" (fun tag ->
      let src = "\xe2\x80\x8bstart middle\xe2\x80\x8bend\xe2\x80\x8b" in
      let edits = fix_edits "ENC-007" src in
      expect
        (List.length edits = 3 && apply_all src edits = "start middleend")
        (tag ^ ": boundary ZWSPs all deleted"));

  run "ENC-007 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-007" "hello world without ZWSP")
        (tag ^ ": no U+200B, no fire"));

  run "ENC-007 fix: idempotent on already-cleaned source" (fun tag ->
      (* After fix, no U+200B remains. Rule does not fire on the result. *)
      expect
        (does_not_fire "ENC-007" "no zero-width spaces here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.23: ENC-017 fix producer (delete U+00AD soft hyphen, 2-byte UTF-8
     needle, mechanical deletion). Mirrors ENC-007 shape. *)
  run "ENC-017 fix: deletes single U+00AD soft hyphen" (fun tag ->
      let src = "hello\xc2\xadworld" in
      let edits = fix_edits "ENC-017" src in
      expect
        (List.length edits = 1 && apply_all src edits = "helloworld")
        (tag ^ ": soft hyphen deleted"));

  run "ENC-017 fix: multiple soft hyphens all deleted" (fun tag ->
      let src = "hy\xc2\xadphen\xc2\xadated\xc2\xadword" in
      let edits = fix_edits "ENC-017" src in
      expect
        (List.length edits = 3 && apply_all src edits = "hyphenatedword")
        (tag ^ ": three soft hyphens deleted"));

  run "ENC-017 fix: soft hyphen at start, middle, and end" (fun tag ->
      let src = "\xc2\xadlead middle\xc2\xadtail\xc2\xad" in
      let edits = fix_edits "ENC-017" src in
      expect
        (List.length edits = 3 && apply_all src edits = "lead middletail")
        (tag ^ ": boundary soft hyphens all deleted"));

  run "ENC-017 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-017" "hyphenated-word with ASCII hyphen")
        (tag ^ ": no U+00AD, no fire"));

  run "ENC-017 fix: idempotent on already-cleaned source" (fun tag ->
      expect
        (does_not_fire "ENC-017" "no soft hyphens here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.24: ENC-021 fix producer (delete U+2060 WORD JOINER, 3-byte UTF-8
     needle, mechanical deletion). Mirrors ENC-007/ENC-017 shape. *)
  run "ENC-021 fix: deletes single U+2060 word joiner" (fun tag ->
      let src = "joined\xe2\x81\xa0word" in
      let edits = fix_edits "ENC-021" src in
      expect
        (List.length edits = 1 && apply_all src edits = "joinedword")
        (tag ^ ": word joiner deleted"));

  run "ENC-021 fix: multiple word joiners all deleted" (fun tag ->
      let src = "a\xe2\x81\xa0b\xe2\x81\xa0c\xe2\x81\xa0d" in
      let edits = fix_edits "ENC-021" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three word joiners deleted"));

  run "ENC-021 fix: word joiner at start, middle, and end" (fun tag ->
      let src = "\xe2\x81\xa0lead middle\xe2\x81\xa0tail\xe2\x81\xa0" in
      let edits = fix_edits "ENC-021" src in
      expect
        (List.length edits = 3 && apply_all src edits = "lead middletail")
        (tag ^ ": boundary word joiners all deleted"));

  run "ENC-021 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-021" "regular source without word joiner")
        (tag ^ ": no U+2060, no fire"));

  run "ENC-021 fix: idempotent on already-cleaned source" (fun tag ->
      expect
        (does_not_fire "ENC-021" "no word joiner here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.25: ENC-020 fix producer (delete U+200E LRM / U+200F RLM
     bidirectional marks, dual 3-byte UTF-8 needle, mechanical deletion). First
     multi-needle ENC fix; mirrors v27.0.17 TYPO-049 dual-needle pattern. *)
  run "ENC-020 fix: deletes single U+200E (LRM)" (fun tag ->
      let src = "left\xe2\x80\x8eright" in
      let edits = fix_edits "ENC-020" src in
      expect
        (List.length edits = 1 && apply_all src edits = "leftright")
        (tag ^ ": LRM deleted"));

  run "ENC-020 fix: deletes single U+200F (RLM)" (fun tag ->
      let src = "left\xe2\x80\x8fright" in
      let edits = fix_edits "ENC-020" src in
      expect
        (List.length edits = 1 && apply_all src edits = "leftright")
        (tag ^ ": RLM deleted"));

  run "ENC-020 fix: handles both LRM and RLM in same input" (fun tag ->
      let src = "a\xe2\x80\x8eb\xe2\x80\x8fc\xe2\x80\x8ed" in
      let edits = fix_edits "ENC-020" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": all three (LRM, RLM, LRM) deleted"));

  run "ENC-020 fix: LRM and RLM at boundaries" (fun tag ->
      let src = "\xe2\x80\x8estart\xe2\x80\x8fmid\xe2\x80\x8eend\xe2\x80\x8f" in
      let edits = fix_edits "ENC-020" src in
      expect
        (List.length edits = 4 && apply_all src edits = "startmidend")
        (tag ^ ": boundary marks all deleted"));

  run "ENC-020 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-020" "regular text without bidi marks")
        (tag ^ ": no LRM/RLM, no fire"));

  run "ENC-020 fix: idempotent on already-cleaned source" (fun tag ->
      expect
        (does_not_fire "ENC-020" "no bidi marks here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.26: ENC-022 fix producer (delete U+FFF9/FFFA/FFFB interlinear
     annotation chars, 3-needle list, mechanical deletion). Extends v27.0.25
     ENC-020 dual-needle pattern to N-needle list. *)
  run "ENC-022 fix: deletes U+FFF9 ANCHOR" (fun tag ->
      let src = "x\xef\xbf\xb9y" in
      let edits = fix_edits "ENC-022" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": ANCHOR deleted"));

  run "ENC-022 fix: deletes U+FFFA SEPARATOR" (fun tag ->
      let src = "x\xef\xbf\xbay" in
      let edits = fix_edits "ENC-022" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": SEPARATOR deleted"));

  run "ENC-022 fix: deletes U+FFFB TERMINATOR" (fun tag ->
      let src = "x\xef\xbf\xbby" in
      let edits = fix_edits "ENC-022" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": TERMINATOR deleted"));

  run "ENC-022 fix: handles all three chars in same input" (fun tag ->
      let src = "a\xef\xbf\xb9b\xef\xbf\xbac\xef\xbf\xbbd" in
      let edits = fix_edits "ENC-022" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": ANCHOR + SEPARATOR + TERMINATOR all deleted"));

  run "ENC-022 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-022" "regular text without interlinear marks")
        (tag ^ ": no U+FFF9-FFFB, no fire"));

  run "ENC-022 fix: idempotent on already-cleaned source" (fun tag ->
      expect
        (does_not_fire "ENC-022" "no interlinear marks here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.27: ENC-024 fix producer (delete U+202A-U+202E bidi embedding /
     override chars, 5-needle list, mechanical deletion). Extends v27.0.26
     ENC-022 N-needle pattern to 5 needles. *)
  run "ENC-024 fix: deletes U+202A LRE" (fun tag ->
      let src = "x\xe2\x80\xaay" in
      let edits = fix_edits "ENC-024" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": LRE deleted"));

  run "ENC-024 fix: deletes U+202B RLE" (fun tag ->
      let src = "x\xe2\x80\xaby" in
      let edits = fix_edits "ENC-024" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": RLE deleted"));

  run "ENC-024 fix: deletes U+202C PDF" (fun tag ->
      let src = "x\xe2\x80\xacy" in
      let edits = fix_edits "ENC-024" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": PDF deleted"));

  run "ENC-024 fix: deletes U+202D LRO" (fun tag ->
      let src = "x\xe2\x80\xady" in
      let edits = fix_edits "ENC-024" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": LRO deleted"));

  run "ENC-024 fix: deletes U+202E RLO" (fun tag ->
      let src = "x\xe2\x80\xaey" in
      let edits = fix_edits "ENC-024" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": RLO deleted"));

  run "ENC-024 fix: handles all five chars in same input" (fun tag ->
      let src =
        "a\xe2\x80\xaab\xe2\x80\xabc\xe2\x80\xacd\xe2\x80\xade\xe2\x80\xaef"
      in
      let edits = fix_edits "ENC-024" src in
      expect
        (List.length edits = 5 && apply_all src edits = "abcdef")
        (tag ^ ": LRE+RLE+PDF+LRO+RLO all deleted"));

  run "ENC-024 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-024" "regular text without bidi embeddings")
        (tag ^ ": no U+202A-U+202E, no fire"));

  run "ENC-024 fix: idempotent on already-cleaned source" (fun tag ->
      expect
        (does_not_fire "ENC-024" "no bidi embeddings here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.28: ENC-012 fix producer (delete U+0080-U+009F C1 control characters,
     32-char range via custom scanner, mechanical deletion). Pivots from
     N-needle list to custom range scanner (single source pass more efficient
     than 32 List.concat_map scans). *)
  run "ENC-012 fix: deletes single U+0080 (range start)" (fun tag ->
      let src = "x\xc2\x80y" in
      let edits = fix_edits "ENC-012" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": U+0080 deleted"));

  run "ENC-012 fix: deletes single U+009F (range end)" (fun tag ->
      let src = "x\xc2\x9fy" in
      let edits = fix_edits "ENC-012" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": U+009F deleted"));

  run "ENC-012 fix: deletes mid-range U+0090" (fun tag ->
      let src = "x\xc2\x90y" in
      let edits = fix_edits "ENC-012" src in
      expect
        (List.length edits = 1 && apply_all src edits = "xy")
        (tag ^ ": U+0090 deleted"));

  run "ENC-012 fix: handles multiple C1 chars in same input" (fun tag ->
      let src = "a\xc2\x80b\xc2\x90c\xc2\x9fd" in
      let edits = fix_edits "ENC-012" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three C1 chars deleted"));

  run "ENC-012 does not fire on U+007F (just below range)" (fun tag ->
      (* U+007F is ASCII DEL, encoded as single byte `\x7f` (not `\xc2 7f`).
         Different prefix; not in scope. *)
      let src = "x\x7fy" in
      expect (does_not_fire "ENC-012" src) (tag ^ ": U+007F not in C1 range"));

  run "ENC-012 does not fire on U+00A0 (just above range)" (fun tag ->
      (* U+00A0 NBSP encodes as `\xc2\xa0`. The lead byte matches `\xc2` but the
         second byte `\xa0` is OUTSIDE the C1 range `\x80..\x9f`. The scanner
         correctly skips it. *)
      let src = "x\xc2\xa0y" in
      expect
        (does_not_fire "ENC-012" src)
        (tag ^ ": U+00A0 NBSP outside C1 range"));

  run "ENC-012 fix: idempotent on already-cleaned source" (fun tag ->
      expect
        (does_not_fire "ENC-012" "no C1 controls here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.29: ENC-014 fix producer (delete UTF-16 BOM at file start, single
     edit at offset 0). Distinct from prior ENC fixes: fixed match position. *)
  run "ENC-014 fix: deletes UTF-16 LE BOM at file start" (fun tag ->
      let src = "\xff\xferest of file" in
      let edits = fix_edits "ENC-014" src in
      expect
        (List.length edits = 1 && apply_all src edits = "rest of file")
        (tag ^ ": LE BOM deleted"));

  run "ENC-014 fix: deletes UTF-16 BE BOM at file start" (fun tag ->
      let src = "\xfe\xffrest of file" in
      let edits = fix_edits "ENC-014" src in
      expect
        (List.length edits = 1 && apply_all src edits = "rest of file")
        (tag ^ ": BE BOM deleted"));

  run "ENC-014 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-014" "regular UTF-8 source no BOM")
        (tag ^ ": no UTF-16 BOM, no fire"));

  run "ENC-014 does not fire on UTF-8 BOM (different bytes)" (fun tag ->
      (* UTF-8 BOM is `\xef\xbb\xbf` (3 bytes, U+FEFF in UTF-8 form). Different
         from UTF-16 LE/BE BOMs `\xff\xfe`/`\xfe\xff`. ENC-014 specifically
         targets UTF-16 BOMs; UTF-8 BOM is handled by ENC-002 (interior) or
         accepted at file start. *)
      let src = "\xef\xbb\xbfutf-8 source" in
      expect (does_not_fire "ENC-014" src) (tag ^ ": UTF-8 BOM not in scope"));

  run "ENC-014 fix: BOM-only-then-tiny-text source" (fun tag ->
      (* Minimal: BOM (2 bytes) immediately followed by content. Edit deletes
         [0, 2), result is just the content. *)
      let src = "\xff\xfex" in
      let edits = fix_edits "ENC-014" src in
      expect
        (List.length edits = 1 && apply_all src edits = "x")
        (tag ^ ": BOM-only-prefix deleted, content preserved"));

  (* v27.0.30: ENC-013 fix producer (normalize mixed CRLF/LF endings to LF). *)
  run "ENC-013 fix: replaces all CRLF with LF when mixed" (fun tag ->
      let src = "line1\r\nline2\nline3\r\nline4" in
      let edits = fix_edits "ENC-013" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "line1\nline2\nline3\nline4")
        (tag ^ ": both CRLFs converted to LF"));

  run "ENC-013 fix: single CRLF + LF -> normalized" (fun tag ->
      let src = "a\r\nb\nc" in
      let edits = fix_edits "ENC-013" src in
      expect
        (List.length edits = 1 && apply_all src edits = "a\nb\nc")
        (tag ^ ": one CRLF converted"));

  run "ENC-013 does not fire on pure LF source" (fun tag ->
      expect
        (does_not_fire "ENC-013" "line1\nline2\nline3")
        (tag ^ ": pure LF, no mixed-endings warning"));

  run "ENC-013 does not fire on pure CRLF source" (fun tag ->
      (* No bare LF, so the mixed condition isn't triggered. The rule
         specifically warns about MIXED endings — pure CRLF is consistent
         (Windows convention) and outside this rule's scope. *)
      expect
        (does_not_fire "ENC-013" "line1\r\nline2\r\nline3")
        (tag ^ ": pure CRLF, no mix"));

  run "ENC-013 fix: multiple consecutive CRLF runs" (fun tag ->
      let src = "a\r\n\r\nb\nc" in
      let edits = fix_edits "ENC-013" src in
      expect
        (List.length edits = 2 && apply_all src edits = "a\n\nb\nc")
        (tag ^ ": consecutive CRLFs each normalized"));

  (* v27.0.31: ENC-018 fix producer (NBHY U+2011 → `-` outside math + URLs). *)
  run "ENC-018 fix: replaces U+2011 with - in plain text" (fun tag ->
      let src = "well\xe2\x80\x91known" in
      let edits = fix_edits "ENC-018" src in
      expect
        (List.length edits = 1 && apply_all src edits = "well-known")
        (tag ^ ": NBHY -> hyphen-minus"));

  run "ENC-018 fix: skips U+2011 inside \\url{...}" (fun tag ->
      let src = "see \\url{http://x.com/a\xe2\x80\x91b/} here" in
      expect (does_not_fire "ENC-018" src) (tag ^ ": URL NBHY preserved"));

  run "ENC-018 fix: skips U+2011 inside $..$ math" (fun tag ->
      let src = "math $a\xe2\x80\x91b$ skipped" in
      expect (does_not_fire "ENC-018" src) (tag ^ ": math NBHY preserved"));

  run "ENC-018 fix: text NBHY fixed even when URL exists elsewhere" (fun tag ->
      let src =
        "url \\url{http://a.com/x\xe2\x80\x91y/} text\xe2\x80\x91hyphen end"
      in
      let edits = fix_edits "ENC-018" src in
      expect
        (List.length edits = 1
        && apply_all src edits
           = "url \\url{http://a.com/x\xe2\x80\x91y/} text-hyphen end")
        (tag ^ ": URL NBHY preserved, text NBHY fixed"));

  run "ENC-018 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-018" "regular text without NBHY")
        (tag ^ ": no U+2011, no fire"));

  run "ENC-018 fix: multiple text NBHYs all replaced" (fun tag ->
      let src = "a\xe2\x80\x91b and c\xe2\x80\x91d" in
      let edits = fix_edits "ENC-018" src in
      expect
        (List.length edits = 2 && apply_all src edits = "a-b and c-d")
        (tag ^ ": both NBHYs replaced"));

  (* v27.0.33: ENC-023 fix producer (U+202F narrow NBSP -> U+00A0 regular). *)
  run "ENC-023 fix: replaces single U+202F with U+00A0" (fun tag ->
      let src = "a\xe2\x80\xafb" in
      let edits = fix_edits "ENC-023" src in
      expect
        (List.length edits = 1 && apply_all src edits = "a\xc2\xa0b")
        (tag ^ ": narrow NBSP -> regular NBSP"));

  run "ENC-023 fix: multiple U+202F all replaced" (fun tag ->
      let src = "a\xe2\x80\xafb\xe2\x80\xafc\xe2\x80\xafd" in
      let edits = fix_edits "ENC-023" src in
      expect
        (List.length edits = 3
        && apply_all src edits = "a\xc2\xa0b\xc2\xa0c\xc2\xa0d")
        (tag ^ ": three narrow NBSPs converted"));

  run "ENC-023 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-023" "regular text without narrow NBSP")
        (tag ^ ": no U+202F, no fire"));

  run "ENC-023 fix: idempotent (U+00A0 not in scope)" (fun tag ->
      (* After fix, source contains U+00A0 not U+202F. ENC-023 specifically
         targets U+202F; U+00A0 is the conventional NBSP and out of scope.
         Re-running on the fixed output produces no further edits. *)
      let src = "after\xc2\xa0fix" in
      expect (does_not_fire "ENC-023" src) (tag ^ ": U+00A0 not flagged"));

  (* v27.0.35: ENC-016 fix producer (fullwidth digits U+FF10-FF19 → ASCII). *)
  run "ENC-016 fix: replaces U+FF10 with '0'" (fun tag ->
      let src = "x\xef\xbc\x90y" in
      let edits = fix_edits "ENC-016" src in
      expect
        (List.length edits = 1 && apply_all src edits = "x0y")
        (tag ^ ": U+FF10 → '0'"));

  run "ENC-016 fix: replaces U+FF19 with '9'" (fun tag ->
      let src = "x\xef\xbc\x99y" in
      let edits = fix_edits "ENC-016" src in
      expect
        (List.length edits = 1 && apply_all src edits = "x9y")
        (tag ^ ": U+FF19 → '9'"));

  run "ENC-016 fix: full digit range U+FF10..FF19 → '0'..'9'" (fun tag ->
      let src =
        "\xef\xbc\x90\xef\xbc\x91\xef\xbc\x92\xef\xbc\x93\xef\xbc\x94"
        ^ "\xef\xbc\x95\xef\xbc\x96\xef\xbc\x97\xef\xbc\x98\xef\xbc\x99"
      in
      let edits = fix_edits "ENC-016" src in
      expect
        (List.length edits = 10 && apply_all src edits = "0123456789")
        (tag ^ ": all 10 fullwidth digits → ASCII"));

  run "ENC-016 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "ENC-016" "regular ASCII digits 0123456789")
        (tag ^ ": no fullwidth digits, no fire"));

  run "ENC-016 does not fire on adjacent non-digit fullwidth chars" (fun tag ->
      (* U+FF0F SOLIDUS = `\xef\xbc\x8f` (b2=0x8f, just below 0x90 range) U+FF1A
         COLON = `\xef\xbc\x9a` (b2=0x9a, just above 0x99 range) Both share the
         `\xef\xbc` prefix but fall outside the digit range. *)
      let src = "x\xef\xbc\x8fy\xef\xbc\x9az" in
      expect
        (does_not_fire "ENC-016" src)
        (tag ^ ": prefix-byte coincidence outside digit range, no fire"));

  run "ENC-016 fix: idempotent on ASCII-fixed source" (fun tag ->
      expect
        (does_not_fire "ENC-016" "ASCII 0123456789 here")
        (tag ^ ": ASCII digits not flagged"));

  (* v27.0.37: CHAR-006 fix producer (Backspace U+0008 delete) — CHAR family
     pioneer pick (single-byte control character deletion). *)
  run "CHAR-006 fix: deletes single backspace byte" (fun tag ->
      let src = "before\x08after" in
      let edits = fix_edits "CHAR-006" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": backspace deleted"));

  run "CHAR-006 fix: multiple backspaces all deleted" (fun tag ->
      let src = "a\x08b\x08c\x08d" in
      let edits = fix_edits "CHAR-006" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three backspaces deleted"));

  run "CHAR-006 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "CHAR-006" "regular text with no control chars")
        (tag ^ ": no backspace, no fire"));

  run "CHAR-006 fix: backspace at file boundaries" (fun tag ->
      let src = "\x08mid\x08end\x08" in
      let edits = fix_edits "CHAR-006" src in
      expect
        (List.length edits = 3 && apply_all src edits = "midend")
        (tag ^ ": leading/middle/trailing backspaces all deleted"));

  run "CHAR-006 fix: idempotent" (fun tag ->
      expect
        (does_not_fire "CHAR-006" "no backspace here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.38: CHAR-007 fix producer (Bell U+0007 delete) — second CHAR-family
     producer, identical single-byte-delete shape as v27.0.37 CHAR-006. *)
  run "CHAR-007 fix: deletes single bell byte" (fun tag ->
      let src = "before\x07after" in
      let edits = fix_edits "CHAR-007" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": bell deleted"));

  run "CHAR-007 fix: multiple bells all deleted" (fun tag ->
      let src = "a\x07b\x07c\x07d" in
      let edits = fix_edits "CHAR-007" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three bells deleted"));

  run "CHAR-007 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "CHAR-007" "regular text with no control chars")
        (tag ^ ": no bell, no fire"));

  run "CHAR-007 fix: bell at file boundaries" (fun tag ->
      let src = "\x07mid\x07end\x07" in
      let edits = fix_edits "CHAR-007" src in
      expect
        (List.length edits = 3 && apply_all src edits = "midend")
        (tag ^ ": leading/middle/trailing bells all deleted"));

  run "CHAR-007 fix: idempotent" (fun tag ->
      expect
        (does_not_fire "CHAR-007" "no bell here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.39: CHAR-008 fix producer (Form feed U+000C delete) — third
     CHAR-family producer; identical shape as CHAR-006/007. *)
  run "CHAR-008 fix: deletes single form feed byte" (fun tag ->
      let src = "before\x0cafter" in
      let edits = fix_edits "CHAR-008" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": form feed deleted"));

  run "CHAR-008 fix: multiple form feeds all deleted" (fun tag ->
      let src = "a\x0cb\x0cc\x0cd" in
      let edits = fix_edits "CHAR-008" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three form feeds deleted"));

  run "CHAR-008 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "CHAR-008" "regular text with no control chars")
        (tag ^ ": no form feed, no fire"));

  run "CHAR-008 fix: form feed at file boundaries" (fun tag ->
      let src = "\x0cmid\x0cend\x0c" in
      let edits = fix_edits "CHAR-008" src in
      expect
        (List.length edits = 3 && apply_all src edits = "midend")
        (tag ^ ": leading/middle/trailing form feeds all deleted"));

  run "CHAR-008 fix: idempotent" (fun tag ->
      expect
        (does_not_fire "CHAR-008" "no form feed here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.40: CHAR-009 fix producer (Delete U+007F delete) — fourth and final
     CHAR-family single-byte-delete producer; closes the CHAR-006..009 block
     opened in v27.0.37. *)
  run "CHAR-009 fix: deletes single DEL byte" (fun tag ->
      let src = "before\x7fafter" in
      let edits = fix_edits "CHAR-009" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": DEL deleted"));

  run "CHAR-009 fix: multiple DELs all deleted" (fun tag ->
      let src = "a\x7fb\x7fc\x7fd" in
      let edits = fix_edits "CHAR-009" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three DELs deleted"));

  run "CHAR-009 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "CHAR-009" "regular text with no control chars")
        (tag ^ ": no DEL, no fire"));

  run "CHAR-009 fix: DEL at file boundaries" (fun tag ->
      let src = "\x7fmid\x7fend\x7f" in
      let edits = fix_edits "CHAR-009" src in
      expect
        (List.length edits = 3 && apply_all src edits = "midend")
        (tag ^ ": leading/middle/trailing DELs all deleted"));

  run "CHAR-009 fix: idempotent" (fun tag ->
      expect
        (does_not_fire "CHAR-009" "no DEL here")
        (tag ^ ": cleaned source doesn't re-fire"));

  (* v27.0.41: First batch release — CHAR-005 + CHAR-013 + CHAR-014 ship
     together as a 3-rule pure-delete batch. Each is a different proven pattern
     (single-byte range with exclusions, N-needle list, single 3-byte needle).
     Disjoint byte ranges, zero cross-rule overlap. *)

  (* CHAR-005: control range 0x00-0x1F minus {0x07,0x08,0x09,0x0A,0x0C,0x0D}. *)
  run "CHAR-005 fix: deletes single in-range control" (fun tag ->
      let src = "a\x01b" in
      let edits = fix_edits "CHAR-005" src in
      expect
        (List.length edits = 1 && apply_all src edits = "ab")
        (tag ^ ": SOH (0x01) deleted"));

  run "CHAR-005 fix: deletes multiple in-range controls" (fun tag ->
      let src = "\x00a\x0bb\x1fc" in
      let edits = fix_edits "CHAR-005" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abc")
        (tag ^ ": NUL/VT/US all deleted"));

  run "CHAR-005 does not fire on excluded bytes" (fun tag ->
      (* TAB/LF/CR + the CHAR-006/007/008 bytes are excluded. *)
      expect
        (does_not_fire "CHAR-005" "tab\there\nLF\rCR\x07bel\x08bs\x0cff")
        (tag ^ ": excluded bytes don't trigger"));

  run "CHAR-005 fix: at file boundaries" (fun tag ->
      let src = "\x01mid\x02end\x03" in
      let edits = fix_edits "CHAR-005" src in
      expect
        (List.length edits = 3 && apply_all src edits = "midend")
        (tag ^ ": leading/middle/trailing controls all deleted"));

  run "CHAR-005 fix: clean source no-fire" (fun tag ->
      expect
        (does_not_fire "CHAR-005" "regular text with no control chars")
        (tag ^ ": clean source"));

  (* CHAR-013: bidi isolates U+2066/2067/2068/2069. *)
  run "CHAR-013 fix: deletes LRI (U+2066)" (fun tag ->
      let src = "before\xe2\x81\xa6after" in
      let edits = fix_edits "CHAR-013" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": LRI deleted"));

  run "CHAR-013 fix: deletes all four isolates" (fun tag ->
      let src = "a\xe2\x81\xa6b\xe2\x81\xa7c\xe2\x81\xa8d\xe2\x81\xa9e" in
      let edits = fix_edits "CHAR-013" src in
      expect
        (List.length edits = 4 && apply_all src edits = "abcde")
        (tag ^ ": LRI/RLI/FSI/PDI all deleted"));

  run "CHAR-013 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "CHAR-013" "regular text with no bidi")
        (tag ^ ": no isolate, no fire"));

  run "CHAR-013 fix: idempotent" (fun tag ->
      expect
        (does_not_fire "CHAR-013" "no isolates here")
        (tag ^ ": clean source doesn't re-fire"));

  (* CHAR-014: U+FFFD replacement character. *)
  run "CHAR-014 fix: deletes single replacement char" (fun tag ->
      let src = "before\xef\xbf\xbdafter" in
      let edits = fix_edits "CHAR-014" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": U+FFFD deleted"));

  run "CHAR-014 fix: multiple replacement chars all deleted" (fun tag ->
      let src = "a\xef\xbf\xbdb\xef\xbf\xbdc\xef\xbf\xbdd" in
      let edits = fix_edits "CHAR-014" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": three U+FFFD deleted"));

  run "CHAR-014 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "CHAR-014" "regular text with no replacements")
        (tag ^ ": no U+FFFD, no fire"));

  run "CHAR-014 fix: idempotent" (fun tag ->
      expect
        (does_not_fire "CHAR-014" "no replacement here")
        (tag ^ ": clean source doesn't re-fire"));

  (* Combined cross-rule test: all 3 batch rules fire on the same source, fixes
     apply non-overlapping (the rewrite engine merges them). *)
  run "v27.0.41 batch combined: CHAR-005 + CHAR-013 + CHAR-014" (fun tag ->
      let src = "start\x01one\xe2\x81\xa6two\xef\xbf\xbdthree\x1fend" in
      let e5 = fix_edits "CHAR-005" src in
      let e13 = fix_edits "CHAR-013" src in
      let e14 = fix_edits "CHAR-014" src in
      let merged = apply_all src (e5 @ e13 @ e14) in
      expect
        (List.length e5 = 2
        && List.length e13 = 1
        && List.length e14 = 1
        && merged = "startonetwothreeend")
        (tag ^ ": 4 disjoint deletes all apply"));

  (* v27.0.43: TYPO-055 collapses consecutive thin-spaces `\,\,` (4 bytes) to a
     single `\,` (2 bytes). Pure non-overlap replace. *)
  Unix.putenv "L0_VALIDATORS" "pilot";

  run "TYPO-055 fix: single \\,\\, collapses to \\," (fun tag ->
      let src = "Foo\\,\\,bar" in
      let edits = fix_edits "TYPO-055" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Foo\\,bar")
        (tag ^ ": one edit, 4 bytes → 2 bytes"));

  run "TYPO-055 fix: triple \\,\\,\\, collapses one non-overlap pair"
    (fun tag ->
      (* `\,\,\,` (6 bytes) contains `\,\,` at offset 0 (non-overlap advance by
         4); the second `\,` from offsets 4-5 is the only remainder. Result:
         `\,\,` (4 bytes), which itself would re-fire next pass. Idempotence is
         not claimed for this rule — a single pass collapses one pair. *)
      let src = "Foo\\,\\,\\,bar" in
      let edits = fix_edits "TYPO-055" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Foo\\,\\,bar")
        (tag ^ ": one non-overlap pair collapsed"));

  run "TYPO-055 fix: two disjoint \\,\\, pairs" (fun tag ->
      let src = "a\\,\\,b\\,\\,c" in
      let edits = fix_edits "TYPO-055" src in
      expect
        (List.length edits = 2 && apply_all src edits = "a\\,b\\,c")
        (tag ^ ": both pairs collapsed"));

  run "TYPO-055 does not fire on single \\," (fun tag ->
      expect
        (does_not_fire "TYPO-055" "Foo\\,bar baz\\,qux")
        (tag ^ ": single thin-spaces are fine"));

  run "TYPO-055 fix: idempotent on collapsed source" (fun tag ->
      expect
        (does_not_fire "TYPO-055" "Foo\\,bar")
        (tag ^ ": clean source doesn't re-fire"));

  (* v27.0.44: math-aware replace batch. TYPO-053 (U+22EF → \dots) + CHAR-019
     (U+2212 → -). Both single-needle, both skip math via find_math_ranges, both
     mirror v27.0.7 TYPO-005 shape. Disjoint byte sequences (e2 8b af vs e2 88
     92). *)

  (* TYPO-053. *)
  run "TYPO-053 fix: U+22EF outside math → \\dots" (fun tag ->
      let src = "Series 1, 2, \xe2\x8b\xaf, 9, 10." in
      let edits = fix_edits "TYPO-053" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Series 1, 2, \\dots, 9, 10.")
        (tag ^ ": 3 bytes → 5 bytes"));

  run "TYPO-053 fix: multiple outside math" (fun tag ->
      let src = "a \xe2\x8b\xaf b \xe2\x8b\xaf c" in
      let edits = fix_edits "TYPO-053" src in
      expect
        (List.length edits = 2 && apply_all src edits = "a \\dots b \\dots c")
        (tag ^ ": both replaced"));

  run "TYPO-053 fix: inside math is skipped" (fun tag ->
      let src = "Series $1, 2, \xe2\x8b\xaf, n$." in
      let edits = fix_edits "TYPO-053" src in
      expect (List.length edits = 0) (tag ^ ": math content preserved"));

  run "TYPO-053 fires (count) even when fix-set empty (math-only)" (fun tag ->
      expect
        (fires "TYPO-053" "Series $1, 2, \xe2\x8b\xaf, n$.")
        (tag ^ ": rule still warns inside math"));

  run "TYPO-053 does not fire on clean source" (fun tag ->
      expect
        (does_not_fire "TYPO-053" "Series 1, 2, 3, 4, 5.")
        (tag ^ ": clean source"));

  (* CHAR-019. *)
  run "CHAR-019 fix: U+2212 outside math → -" (fun tag ->
      let src = "Temperature: \xe2\x88\x9212 degrees" in
      let edits = fix_edits "CHAR-019" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Temperature: -12 degrees")
        (tag ^ ": 3 bytes → 1 byte"));

  run "CHAR-019 fix: multiple outside math" (fun tag ->
      let src = "From \xe2\x88\x925 to \xe2\x88\x9210 below." in
      let edits = fix_edits "CHAR-019" src in
      expect
        (List.length edits = 2 && apply_all src edits = "From -5 to -10 below.")
        (tag ^ ": both replaced"));

  run "CHAR-019 fix: inside math is skipped" (fun tag ->
      let src = "We have $x \xe2\x88\x92 y$ as math." in
      let edits = fix_edits "CHAR-019" src in
      expect (List.length edits = 0) (tag ^ ": math content preserved"));

  run "CHAR-019 does not fire on clean text" (fun tag ->
      expect
        (does_not_fire "CHAR-019" "Plain ASCII minus -10.")
        (tag ^ ": ASCII hyphen ok"));

  (* Combined cross-rule: both fire on the same source, fixes apply
     non-overlapping (different needles). *)
  run "v27.0.44 batch combined: TYPO-053 + CHAR-019" (fun tag ->
      let src = "Range \xe2\x88\x9210 to \xe2\x88\x925 \xe2\x8b\xaf 5 to 10." in
      let e53 = fix_edits "TYPO-053" src in
      let e19 = fix_edits "CHAR-019" src in
      let merged = apply_all src (e53 @ e19) in
      expect
        (List.length e53 = 1
        && List.length e19 = 2
        && merged = "Range -10 to -5 \\dots 5 to 10.")
        (tag ^ ": 3 disjoint replaces all apply"));

  (* v27.0.46: ENC-002 / SPC-012 redundancy resolution. SPC-012 must no longer
     emit a fix (it falls back to count-only); ENC-002 retains its fix. Both
     still detect the same BOM-at-non-leading-offset condition. *)
  run "v27.0.46: SPC-012 no longer emits fix edits" (fun tag ->
      let src = "Header line.\nBody \xef\xbb\xbf inline BOM.\nEnd." in
      let spc_edits = fix_edits "SPC-012" src in
      let enc_edits = fix_edits "ENC-002" src in
      expect
        (List.length spc_edits = 0
        && List.length enc_edits = 1
        && apply_all src enc_edits = "Header line.\nBody  inline BOM.\nEnd.")
        (tag ^ ": SPC-012 no fix, ENC-002 single fix, no duplicate"));

  (* v27.0.46: MATH-082 fix producer — collapse `\!\!` in math to `\!`. *)
  run "MATH-082 fix: collapses inside math" (fun tag ->
      let src = "Eq: $a \\!\\! b$" in
      let edits = fix_edits "MATH-082" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Eq: $a \\! b$")
        (tag ^ ": 4 bytes → 2 bytes inside math"));

  run "MATH-082 fix: outside math is skipped" (fun tag ->
      let src = "Text with \\!\\! literally outside math." in
      let edits = fix_edits "MATH-082" src in
      expect (List.length edits = 0) (tag ^ ": \\!\\! outside math not touched"));

  run "MATH-082 fix: two pairs in math" (fun tag ->
      let src = "$a\\!\\!b \\!\\! c$ tail" in
      let edits = fix_edits "MATH-082" src in
      expect
        (List.length edits = 2 && apply_all src edits = "$a\\!b \\! c$ tail")
        (tag ^ ": both pairs collapsed"));

  run "MATH-082 does not fire on clean math" (fun tag ->
      expect
        (does_not_fire "MATH-082" "$a \\! b \\! c$")
        (tag ^ ": single thin-spaces ok"));

  (* v27.0.47: MATH-106 + MATH-108 math-aware single-needle replace batch. Same
     shape as MATH-082 (math-mode-only positive filter). *)

  (* MATH-106. *)
  run "MATH-106 fix: \\not= → \\neq inside math" (fun tag ->
      let src = "Compare $a \\not= b$ now." in
      let edits = fix_edits "MATH-106" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Compare $a \\neq b$ now.")
        (tag ^ ": 5 bytes → 4 bytes"));

  run "MATH-106 fix: outside math is skipped" (fun tag ->
      let src = "Literal \\not= in text" in
      let edits = fix_edits "MATH-106" src in
      expect (List.length edits = 0) (tag ^ ": not in math, no fix"));

  run "MATH-106 fix: multiple \\not= inside math" (fun tag ->
      let src = "$a \\not= b \\not= c$" in
      let edits = fix_edits "MATH-106" src in
      expect
        (List.length edits = 2 && apply_all src edits = "$a \\neq b \\neq c$")
        (tag ^ ": both replaced"));

  run "MATH-106 does not fire on clean \\neq" (fun tag ->
      expect (does_not_fire "MATH-106" "$x \\neq y$") (tag ^ ": already correct"));

  (* MATH-108. *)
  run "MATH-108 fix: U+00B7 → \\cdot inside math" (fun tag ->
      let src = "Product $a \xc2\xb7 b$ end." in
      let edits = fix_edits "MATH-108" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Product $a \\cdot b$ end.")
        (tag ^ ": 2 bytes → 5 bytes"));

  run "MATH-108 fix: outside math is skipped" (fun tag ->
      let src = "Text with \xc2\xb7 middle dot in prose." in
      let edits = fix_edits "MATH-108" src in
      expect (List.length edits = 0) (tag ^ ": text-mode middle dot not touched"));

  run "MATH-108 fix: multiple inside math" (fun tag ->
      let src = "$a \xc2\xb7 b \xc2\xb7 c$" in
      let edits = fix_edits "MATH-108" src in
      expect
        (List.length edits = 2 && apply_all src edits = "$a \\cdot b \\cdot c$")
        (tag ^ ": both replaced"));

  run "MATH-108 does not fire on clean \\cdot" (fun tag ->
      expect
        (does_not_fire "MATH-108" "$x \\cdot y$")
        (tag ^ ": already correct"));

  (* Combined cross-rule: MATH-106 + MATH-108 in same math segment. *)
  run "v27.0.47 batch combined: MATH-106 + MATH-108" (fun tag ->
      let src = "$a \\not= b \xc2\xb7 c$" in
      let e106 = fix_edits "MATH-106" src in
      let e108 = fix_edits "MATH-108" src in
      let merged = apply_all src (e106 @ e108) in
      expect
        (List.length e106 = 1
        && List.length e108 = 1
        && merged = "$a \\neq b \\cdot c$")
        (tag ^ ": disjoint replaces compose"));

  (* v27.0.48: MATH-015 fix producer (\stackrel{ → \overset{ inside math). *)
  run "MATH-015 fix: \\stackrel → \\overset inside math" (fun tag ->
      let src = "$x \\stackrel{?}{=} y$" in
      let edits = fix_edits "MATH-015" src in
      expect
        (List.length edits = 1 && apply_all src edits = "$x \\overset{?}{=} y$")
        (tag ^ ": macro name swapped, braces preserved"));

  run "MATH-015 fix: outside math is skipped" (fun tag ->
      let src = "Plain text \\stackrel{a}{b}." in
      let edits = fix_edits "MATH-015" src in
      expect (List.length edits = 0) (tag ^ ": text-mode \\stackrel not touched"));

  run "MATH-015 fix: two occurrences inside math" (fun tag ->
      let src = "$\\stackrel{A}{B} + \\stackrel{C}{D}$" in
      let edits = fix_edits "MATH-015" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "$\\overset{A}{B} + \\overset{C}{D}$")
        (tag ^ ": both replaced"));

  run "MATH-015 does not fire on clean \\overset" (fun tag ->
      expect
        (does_not_fire "MATH-015" "$\\overset{a}{b}$")
        (tag ^ ": already correct"));

  (* v27.0.49: MATH-078 fix producer (--> → \longrightarrow inside math). *)
  run "MATH-078 fix: --> → \\longrightarrow inside math" (fun tag ->
      let src = "Map: $f --> g$" in
      let edits = fix_edits "MATH-078" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Map: $f \\longrightarrow g$")
        (tag ^ ": 3 bytes → 15 bytes"));

  run "MATH-078 fix: outside math is skipped" (fun tag ->
      let src = "Text with --> arrow in prose." in
      let edits = fix_edits "MATH-078" src in
      expect (List.length edits = 0) (tag ^ ": text-mode --> not touched"));

  run "MATH-078 fix: multiple inside math" (fun tag ->
      let src = "$a --> b --> c$" in
      let edits = fix_edits "MATH-078" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "$a \\longrightarrow b \\longrightarrow c$")
        (tag ^ ": both replaced"));

  run "MATH-078 does not fire on clean \\longrightarrow" (fun tag ->
      expect
        (does_not_fire "MATH-078" "$x \\longrightarrow y$")
        (tag ^ ": already correct"));

  (* v27.0.50: MATH-010 (÷ → \div inside math). *)
  run "MATH-010 fix: ÷ → \\div inside math" (fun tag ->
      let src = "Divide: $a \xc3\xb7 b$." in
      let edits = fix_edits "MATH-010" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Divide: $a \\div b$.")
        (tag ^ ": 2 bytes → 4 bytes"));

  run "MATH-010 fix: outside math is skipped" (fun tag ->
      let src = "Text with \xc3\xb7 in prose." in
      let edits = fix_edits "MATH-010" src in
      expect (List.length edits = 0) (tag ^ ": text-mode ÷ not touched"));

  run "MATH-010 fix: multiple inside math" (fun tag ->
      let src = "$1 \xc3\xb7 2 \xc3\xb7 3$" in
      let edits = fix_edits "MATH-010" src in
      expect
        (List.length edits = 2 && apply_all src edits = "$1 \\div 2 \\div 3$")
        (tag ^ ": both replaced"));

  run "MATH-010 does not fire on clean \\div" (fun tag ->
      expect (does_not_fire "MATH-010" "$a \\div b$") (tag ^ ": already correct"));

  (* v27.0.51: MATH-097 (=> → \implies inside math). *)
  run "MATH-097 fix: => → \\implies inside math" (fun tag ->
      let src = "$P => Q$" in
      let edits = fix_edits "MATH-097" src in
      expect
        (List.length edits = 1 && apply_all src edits = "$P \\implies Q$")
        (tag ^ ": 2 bytes → 8 bytes"));

  run "MATH-097 fix: outside math is skipped" (fun tag ->
      let src = "Text P => Q in prose." in
      let edits = fix_edits "MATH-097" src in
      expect (List.length edits = 0) (tag ^ ": text-mode => not touched"));

  run "MATH-097 fix: multiple inside math" (fun tag ->
      let src = "$A => B => C$" in
      let edits = fix_edits "MATH-097" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "$A \\implies B \\implies C$")
        (tag ^ ": both replaced"));

  run "MATH-097 skips ==> / <=> / \\=> (excluded before-byte)" (fun tag ->
      (* `==>` has `=` before `=>`; `<=>` has `<`; `\=>` has `\` — none should
         match. *)
      let src = "$x ==> y <=> z \\=> w$" in
      let edits = fix_edits "MATH-097" src in
      expect (List.length edits = 0) (tag ^ ": guarded cases all skipped"));

  run "MATH-097 does not fire on clean \\implies" (fun tag ->
      expect
        (does_not_fire "MATH-097" "$P \\implies Q$")
        (tag ^ ": already correct"));

  (* v27.0.52: TYPO-061 (× U+00D7 → $\times$ in text mode). *)
  run "TYPO-061 fix: × → $\\times$ in text" (fun tag ->
      let src = "Area: 5 \xc3\x97 7 cm." in
      let edits = fix_edits "TYPO-061" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Area: 5 $\\times$ 7 cm.")
        (tag ^ ": 2 bytes → 8 bytes"));

  run "TYPO-061 fix: inside math is skipped" (fun tag ->
      let src = "Inline: $a \xc3\x97 b$ stays as \xc3\x97." in
      let edits = fix_edits "TYPO-061" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "Inline: $a \xc3\x97 b$ stays as $\\times$.")
        (tag ^ ": math × untouched, text × replaced"));

  run "TYPO-061 fix: multiple in text" (fun tag ->
      let src = "Dim: 3 \xc3\x97 4 \xc3\x97 5." in
      let edits = fix_edits "TYPO-061" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "Dim: 3 $\\times$ 4 $\\times$ 5.")
        (tag ^ ": both text-mode × replaced"));

  run "TYPO-061 does not fire on \\times in math" (fun tag ->
      expect
        (does_not_fire "TYPO-061" "$a \\times b$")
        (tag ^ ": pure math already correct"));

  (* v27.0.53: CHAR-018 (precomposed ligatures U+FB00..U+FB04 → ASCII). *)
  run "CHAR-018 fix: fi ligature → fi" (fun tag ->
      let src = "Word: \xef\xac\x81nal." in
      let edits = fix_edits "CHAR-018" src in
      expect
        (List.length edits = 1 && apply_all src edits = "Word: final.")
        (tag ^ ": single fi ligature replaced"));

  run "CHAR-018 fix: all five ligatures in one source" (fun tag ->
      (* Each ligature appears exactly once, with ASCII-only surrounding text
         (using Unicode chars as labels would self-match the needles). *)
      let src =
        "L1=\xef\xac\x80 L2=\xef\xac\x81 L3=\xef\xac\x82 L4=\xef\xac\x83 \
         L5=\xef\xac\x84."
      in
      let edits = fix_edits "CHAR-018" src in
      expect
        (List.length edits = 5
        && apply_all src edits = "L1=ff L2=fi L3=fl L4=ffi L5=ffl.")
        (tag ^ ": all five replaced"));

  run "CHAR-018 fix: multiple ﬁ in text" (fun tag ->
      let src = "\xef\xac\x81rst, \xef\xac\x81nal, \xef\xac\x81xed." in
      let edits = fix_edits "CHAR-018" src in
      expect
        (List.length edits = 3 && apply_all src edits = "first, final, fixed.")
        (tag ^ ": three fi ligatures replaced"));

  run "CHAR-018 does not fire on plain ASCII text" (fun tag ->
      expect
        (does_not_fire "CHAR-018" "Just plain fi text with no ligatures.")
        (tag ^ ": ASCII already correct"));

  (* v27.0.54: CHAR-017 (fullwidth Latin letters U+FF21..FF3A + U+FF41..FF5A →
     ASCII). *)
  run "CHAR-017 fix: uppercase fullwidth → ASCII" (fun tag ->
      (* Ａ U+FF21 = EF BC A1, Ｚ U+FF3A = EF BC BA *)
      let src = "Start: \xef\xbc\xa1 \xef\xbc\xba end." in
      let edits = fix_edits "CHAR-017" src in
      expect
        (List.length edits = 2 && apply_all src edits = "Start: A Z end.")
        (tag ^ ": Ａ→A and Ｚ→Z"));

  run "CHAR-017 fix: lowercase fullwidth → ASCII" (fun tag ->
      (* ａ U+FF41 = EF BD 81, ｚ U+FF5A = EF BD 9A *)
      let src = "Start: \xef\xbd\x81 \xef\xbd\x9a end." in
      let edits = fix_edits "CHAR-017" src in
      expect
        (List.length edits = 2 && apply_all src edits = "Start: a z end.")
        (tag ^ ": ａ→a and ｚ→z"));

  run "CHAR-017 fix: mixed-case word" (fun tag ->
      (* Ｈ Ｅ Ｌ Ｌ Ｏ = EF BC A8 / A5 / AC / AC / AF *)
      let src =
        "Hello: \xef\xbc\xa8\xef\xbc\xa5\xef\xbc\xac\xef\xbc\xac\xef\xbc\xaf"
      in
      let edits = fix_edits "CHAR-017" src in
      expect
        (List.length edits = 5 && apply_all src edits = "Hello: HELLO")
        (tag ^ ": fullwidth HELLO → ASCII HELLO"));

  run "CHAR-017 does not fire on plain ASCII text" (fun tag ->
      expect
        (does_not_fire "CHAR-017" "Just plain Latin letters Aa Zz.")
        (tag ^ ": ASCII already correct"));

  (* v27.0.55: SPC-019 (trailing U+3000 ideographic space deletion). *)
  run "SPC-019 fix: single trailing U+3000 deleted" (fun tag ->
      let src = "line one\xe3\x80\x80\nline two\n" in
      let edits = fix_edits "SPC-019" src in
      expect
        (List.length edits = 1 && apply_all src edits = "line one\nline two\n")
        (tag ^ ": one line trimmed"));

  run "SPC-019 fix: multiple trailing U+3000 collapsed" (fun tag ->
      let src = "text\xe3\x80\x80\xe3\x80\x80\xe3\x80\x80\nnext\n" in
      let edits = fix_edits "SPC-019" src in
      expect
        (List.length edits = 1 && apply_all src edits = "text\nnext\n")
        (tag ^ ": entire trailing run deleted"));

  run "SPC-019 fix: middle U+3000 untouched" (fun tag ->
      let src = "a\xe3\x80\x80b\nc\xe3\x80\x80\n" in
      let edits = fix_edits "SPC-019" src in
      expect
        (List.length edits = 1 && apply_all src edits = "a\xe3\x80\x80b\nc\n")
        (tag ^ ": only trailing run removed"));

  run "SPC-019 fix: last line without newline still trimmed" (fun tag ->
      let src = "trailing\xe3\x80\x80" in
      let edits = fix_edits "SPC-019" src in
      expect
        (List.length edits = 1 && apply_all src edits = "trailing")
        (tag ^ ": EOF line handled"));

  run "SPC-019 does not fire on clean text" (fun tag ->
      expect
        (does_not_fire "SPC-019" "no fullwidth space here\nclean line\n")
        (tag ^ ": ASCII-only clean"));

  (* v27.0.56: SPC-030 (leading U+3000) + SPC-035 (leading U+2009) batch. *)
  run "SPC-030 fix: single leading U+3000 deleted" (fun tag ->
      let src = "\xe3\x80\x80line one\nplain line\n" in
      let edits = fix_edits "SPC-030" src in
      expect
        (List.length edits = 1 && apply_all src edits = "line one\nplain line\n")
        (tag ^ ": one leading U+3000 trimmed"));

  run "SPC-030 fix: multiple leading U+3000 collapsed" (fun tag ->
      let src = "\xe3\x80\x80\xe3\x80\x80\xe3\x80\x80text\nnext\n" in
      let edits = fix_edits "SPC-030" src in
      expect
        (List.length edits = 1 && apply_all src edits = "text\nnext\n")
        (tag ^ ": entire leading run deleted"));

  run "SPC-030 fix: middle U+3000 untouched" (fun tag ->
      let src = "abc\xe3\x80\x80def\n\xe3\x80\x80lead\n" in
      let edits = fix_edits "SPC-030" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "abc\xe3\x80\x80def\nlead\n")
        (tag ^ ": only leading run removed"));

  run "SPC-035 fix: single leading U+2009 deleted" (fun tag ->
      let src = "\xe2\x80\x89indented\nnormal\n" in
      let edits = fix_edits "SPC-035" src in
      expect
        (List.length edits = 1 && apply_all src edits = "indented\nnormal\n")
        (tag ^ ": one leading U+2009 trimmed"));

  run "SPC-035 fix: multiple leading U+2009 collapsed" (fun tag ->
      let src = "\xe2\x80\x89\xe2\x80\x89text\nnext\n" in
      let edits = fix_edits "SPC-035" src in
      expect
        (List.length edits = 1 && apply_all src edits = "text\nnext\n")
        (tag ^ ": entire leading run deleted"));

  run "SPC-030 + SPC-035: disjoint needles" (fun tag ->
      let src = "\xe3\x80\x80fw\n\xe2\x80\x89thin\nclean\n" in
      let s30 = fix_edits "SPC-030" src in
      let s35 = fix_edits "SPC-035" src in
      expect
        (List.length s30 = 1
        && List.length s35 = 1
        && apply_all src s30 = "fw\n\xe2\x80\x89thin\nclean\n"
        && apply_all src s35 = "\xe3\x80\x80fw\nthin\nclean\n")
        (tag ^ ": SPC-030 leaves thin alone; SPC-035 leaves fw alone"));

  run "SPC-030 does not fire on clean text" (fun tag ->
      expect
        (does_not_fire "SPC-030" "plain start\nclean\n")
        (tag ^ ": no U+3000 at line start"));

  run "SPC-035 does not fire on clean text" (fun tag ->
      expect
        (does_not_fire "SPC-035" "plain start\nclean\n")
        (tag ^ ": no U+2009 at line start"));

  (* v27.0.56: TYPO-051 leading-run filter (cross-rule with SPC-035). *)
  run "TYPO-051 skips leading-run U+2009 (delegates to SPC-035)" (fun tag ->
      (* Leading U+2009 at line start: TYPO-051 must NOT emit a fix-edit (would
         conflict with SPC-035's delete). Middle U+2009 still wrapped. *)
      let src = "\xe2\x80\x89lead\n5\xe2\x80\x89m\n" in
      let edits = fix_edits "TYPO-051" src in
      (* Only the middle U+2009 (offset 7) should get an edit. *)
      expect
        (List.length edits = 1
        && apply_all src edits = "\xe2\x80\x89lead\n5\\thinspace{}m\n")
        (tag ^ ": leading skipped, middle wrapped"));

  run "TYPO-051 skips multi-leading-run U+2009" (fun tag ->
      let src = "\xe2\x80\x89\xe2\x80\x89lead\nplain\n" in
      let edits = fix_edits "TYPO-051" src in
      expect
        (List.length edits = 0)
        (tag ^ ": all leading-run positions skipped"));

  run "TYPO-051 + SPC-035 coexist non-overlapping (full source)" (fun tag ->
      let src = "\xe2\x80\x89lead\n5\xe2\x80\x89m\n" in
      let s35 = fix_edits "SPC-035" src in
      let t51 = fix_edits "TYPO-051" src in
      (* SPC-035 deletes leading (offset 0-3); TYPO-051 wraps middle (offset 7).
         Disjoint ranges, both can apply. *)
      expect
        (List.length s35 = 1
        && List.length t51 = 1
        && apply_all src (s35 @ t51) = "lead\n5\\thinspace{}m\n")
        (tag ^ ": leading delete + middle wrap, no overlap"));

  (* v27.0.57: CHAR-012 (U+200D Zero-Width Joiner → delete). *)
  run "CHAR-012 fix: single ZWJ deleted" (fun tag ->
      let src = "before\xe2\x80\x8dafter" in
      let edits = fix_edits "CHAR-012" src in
      expect
        (List.length edits = 1 && apply_all src edits = "beforeafter")
        (tag ^ ": single U+200D deleted"));

  run "CHAR-012 fix: multiple ZWJ all deleted" (fun tag ->
      let src = "a\xe2\x80\x8db\xe2\x80\x8dc\xe2\x80\x8dd" in
      let edits = fix_edits "CHAR-012" src in
      expect
        (List.length edits = 3 && apply_all src edits = "abcd")
        (tag ^ ": all three U+200D deleted"));

  run "CHAR-012 fix: ZWJ at file boundaries" (fun tag ->
      let src = "\xe2\x80\x8dleading and trailing\xe2\x80\x8d" in
      let edits = fix_edits "CHAR-012" src in
      expect
        (List.length edits = 2 && apply_all src edits = "leading and trailing")
        (tag ^ ": leading + trailing both deleted"));

  run "CHAR-012 does not fire on plain ASCII text" (fun tag ->
      expect
        (does_not_fire "CHAR-012" "Just plain ASCII text with no joiners.")
        (tag ^ ": ASCII-only clean"));

  (* v27.0.58: SPC-028 (collapse runs of 2+ consecutive ~ NBSPs → single ~). *)
  run "SPC-028 fix: double ~~ → ~" (fun tag ->
      let src = "Dr.~~Smith and Prof.~~Jones." in
      let edits = fix_edits "SPC-028" src in
      expect
        (List.length edits = 2
        && apply_all src edits = "Dr.~Smith and Prof.~Jones.")
        (tag ^ ": both pairs collapsed"));

  run "SPC-028 fix: triple ~~~ → ~" (fun tag ->
      let src = "A~~~B" in
      let edits = fix_edits "SPC-028" src in
      expect
        (List.length edits = 1 && apply_all src edits = "A~B")
        (tag ^ ": run of 3 collapsed to 1"));

  run "SPC-028 fix: long run ~~~~~ → ~" (fun tag ->
      let src = "X~~~~~Y" in
      let edits = fix_edits "SPC-028" src in
      expect
        (List.length edits = 1 && apply_all src edits = "X~Y")
        (tag ^ ": run of 5 collapsed to 1"));

  run "SPC-028 fix: single ~ untouched" (fun tag ->
      let src = "Dr.~Smith and Prof.~Jones." in
      let edits = fix_edits "SPC-028" src in
      expect
        (List.length edits = 0 && apply_all src edits = src)
        (tag ^ ": no run, no edit"));

  run "SPC-028 does not fire on text without NBSPs" (fun tag ->
      expect
        (does_not_fire "SPC-028" "Plain text with no tildes here.")
        (tag ^ ": tilde-free clean"));

  (* v27.0.59: SPC-025 (delete space before \dots or U+2026 ellipsis). *)
  run "SPC-025 fix: space before \\dots → \\dots" (fun tag ->
      let src = "and so on \\dots end." in
      let edits = fix_edits "SPC-025" src in
      expect
        (List.length edits = 1 && apply_all src edits = "and so on\\dots end.")
        (tag ^ ": leading space deleted"));

  run "SPC-025 fix: space before U+2026 → U+2026" (fun tag ->
      let src = "and so on \xe2\x80\xa6 end." in
      let edits = fix_edits "SPC-025" src in
      expect
        (List.length edits = 1
        && apply_all src edits = "and so on\xe2\x80\xa6 end.")
        (tag ^ ": leading space deleted before U+2026"));

  run "SPC-025 fix: multiple matches both deleted" (fun tag ->
      let src = "a \\dots b \\dots c \xe2\x80\xa6 d" in
      let edits = fix_edits "SPC-025" src in
      expect
        (List.length edits = 3
        && apply_all src edits = "a\\dots b\\dots c\xe2\x80\xa6 d")
        (tag ^ ": three matches all collapsed"));

  run "SPC-025 does not fire on clean usage" (fun tag ->
      (* `\dots` directly attached to preceding non-space character — no
         fire. *)
      expect
        (does_not_fire "SPC-025" "Sentence.\\dots more here.")
        (tag ^ ": no leading space before \\dots, no fire"));

  finalise "typo-fix"
