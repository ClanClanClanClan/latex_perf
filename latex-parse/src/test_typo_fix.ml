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

  finalise "typo-fix"
