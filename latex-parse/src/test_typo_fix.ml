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

  finalise "typo-fix"
