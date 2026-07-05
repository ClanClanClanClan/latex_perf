(** Unit tests for locale validator rules (FR, PT, RU, PL, CS, EL, RO, AR, HE,
    ZH, JA, KO, HI). *)

open Test_helpers

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     FR-007: FR-BE thin NB-space before/after euro sign
     ══════════════════════════════════════════════════════════════════════ *)
  run "FR-007 fires on space before euro" (fun tag ->
      expect (fires "FR-007" "prix 50 \xe2\x82\xac") (tag ^ ": space+euro"));
  run "FR-007 fires on space after euro" (fun tag ->
      expect (fires "FR-007" "\xe2\x82\xac 50") (tag ^ ": euro+space"));
  run "FR-007 count=2" (fun tag ->
      expect
        (fires_with_count "FR-007" "50 \xe2\x82\xac et \xe2\x82\xac 20" 2)
        (tag ^ ": count=2"));
  run "FR-007 clean with NBSP" (fun tag ->
      expect
        (does_not_fire "FR-007" "50\xc2\xa0\xe2\x82\xac")
        (tag ^ ": NBSP before euro ok"));
  run "FR-007 clean no euro" (fun tag ->
      expect (does_not_fire "FR-007" "50 dollars") (tag ^ ": no euro sign"));
  (* FR-007 fix producer (v27.1.11). The fix replaces each ASCII space adjacent
     to € (E2 82 AC) with the narrow no-break space U+202F (E2 80 AF). *)
  let apply_fr007 src =
    match Latex_parse_lib.Cst_edit.apply_all src (fix_edits "FR-007" src) with
    | Ok s -> s
    | Error _ -> src
  in
  run "FR-007 fix: space before euro -> U+202F" (fun tag ->
      expect
        (apply_fr007 "prix 50 \xe2\x82\xac" = "prix 50\xe2\x80\xaf\xe2\x82\xac")
        (tag ^ ": space+euro replaced"));
  run "FR-007 fix: space after euro -> U+202F" (fun tag ->
      expect
        (apply_fr007 "\xe2\x82\xac 50" = "\xe2\x82\xac\xe2\x80\xaf50")
        (tag ^ ": euro+space replaced"));
  run "FR-007 fix: both sides of one euro repaired in one pass" (fun tag ->
      let out = apply_fr007 "50 \xe2\x82\xac 20" in
      expect
        (out = "50\xe2\x80\xaf\xe2\x82\xac\xe2\x80\xaf20"
        && does_not_fire "FR-007" out)
        (tag ^ ": both spaces fixed, no re-fire"));
  run "FR-007 fix: idempotent (2nd pass no-op)" (fun tag ->
      let once = apply_fr007 "50 \xe2\x82\xac et \xe2\x82\xac 20" in
      let twice = apply_fr007 once in
      expect
        (twice = once
        && fix_edits "FR-007" once = []
        && does_not_fire "FR-007" once)
        (tag ^ ": fixpoint reached after one pass"));
  run "FR-007 fix: count unchanged by producer" (fun tag ->
      expect
        (fires_with_count "FR-007" "50 \xe2\x82\xac et \xe2\x82\xac 20" 2)
        (tag ^ ": diagnostic count preserved"));

  (* ══════════════════════════════════════════════════════════════════════
     FR-008: French ligature oe/OE mandatory
     ══════════════════════════════════════════════════════════════════════ *)
  run "FR-008 fires on coeur" (fun tag ->
      expect (fires "FR-008" "le coeur bat") (tag ^ ": coeur"));
  run "FR-008 fires on oeuvre" (fun tag ->
      expect (fires "FR-008" "une oeuvre dart") (tag ^ ": oeuvre"));
  run "FR-008 fires on COEUR uppercase" (fun tag ->
      expect (fires "FR-008" "le COEUR bat") (tag ^ ": COEUR uppercase"));
  run "FR-008 count=2" (fun tag ->
      expect
        (fires_with_count "FR-008" "le coeur et une oeuvre" 2)
        (tag ^ ": count=2"));
  run "FR-008 clean with ligature" (fun tag ->
      expect
        (does_not_fire "FR-008" "le c\xc5\x93ur bat")
        (tag ^ ": correct ligature"));
  run "FR-008 clean no French" (fun tag ->
      expect (does_not_fire "FR-008" "the heart beats") (tag ^ ": no oe words"));

  (* ══════════════════════════════════════════════════════════════════════
     PT-003: pt-PT ordinal must use ordinal indicators
     ══════════════════════════════════════════════════════════════════════ *)
  run "PT-003 fires on textsuperscript o" (fun tag ->
      expect
        (fires "PT-003" "1\\textsuperscript{o} lugar")
        (tag ^ ": superscript o"));
  run "PT-003 fires on textsuperscript a" (fun tag ->
      expect
        (fires "PT-003" "2\\textsuperscript{a} edicao")
        (tag ^ ": superscript a"));
  run "PT-003 count=2" (fun tag ->
      expect
        (fires_with_count "PT-003"
           "1\\textsuperscript{o} e 2\\textsuperscript{a}" 2)
        (tag ^ ": count=2"));
  run "PT-003 clean" (fun tag ->
      expect
        (does_not_fire "PT-003" "1\xc2\xba lugar")
        (tag ^ ": correct ordinal indicator"));

  (* ══════════════════════════════════════════════════════════════════════
     RU-001: NB-space required before em-dash
     ══════════════════════════════════════════════════════════════════════ *)
  run "RU-001 fires on space before em-dash" (fun tag ->
      expect
        (fires "RU-001"
           "\xd0\x9c\xd0\xbe\xd1\x81\xd0\xba\xd0\xb2\xd0\xb0 \xe2\x80\x94 \
            \xd0\xb3\xd0\xbe\xd1\x80\xd0\xbe\xd0\xb4")
        (tag ^ ": space before em-dash"));
  run "RU-001 clean with NBSP" (fun tag ->
      expect
        (does_not_fire "RU-001"
           "\xd0\x9c\xd0\xbe\xd1\x81\xd0\xba\xd0\xb2\xd0\xb0\xc2\xa0\xe2\x80\x94 \
            \xd0\xb3\xd0\xbe\xd1\x80\xd0\xbe\xd0\xb4")
        (tag ^ ": NBSP before em-dash ok"));
  run "RU-001 clean no em-dash" (fun tag ->
      expect (does_not_fire "RU-001" "just text") (tag ^ ": no em-dash"));
  (* v27.1.11: fix producer — replace the ASCII space before the em-dash with
     NBSP U+00A0 (C2 A0). Москва<sp>—<sp>город → Москва<NBSP>—<sp>город. *)
  let ru_001_src =
    "\xd0\x9c\xd0\xbe\xd1\x81\xd0\xba\xd0\xb2\xd0\xb0 \xe2\x80\x94 \
     \xd0\xb3\xd0\xbe\xd1\x80\xd0\xbe\xd0\xb4"
  in
  let ru_001_fixed =
    "\xd0\x9c\xd0\xbe\xd1\x81\xd0\xba\xd0\xb2\xd0\xb0\xc2\xa0\xe2\x80\x94 \
     \xd0\xb3\xd0\xbe\xd1\x80\xd0\xbe\xd0\xb4"
  in
  run "RU-001 emits a fix" (fun tag ->
      expect (fires_with_fix "RU-001" ru_001_src) (tag ^ ": has fix"));
  run "RU-001 fix replaces space with NBSP" (fun tag ->
      expect (apply_fix "RU-001" ru_001_src = ru_001_fixed) (tag ^ ": NBSP"));
  run "RU-001 fix is idempotent" (fun tag ->
      (* second pass: detector no longer fires, apply is a no-op *)
      expect
        (does_not_fire "RU-001" ru_001_fixed
        && apply_fix "RU-001" ru_001_fixed = ru_001_fixed)
        (tag ^ ": idempotent"));
  run "RU-001 count unchanged by fix producer" (fun tag ->
      (* two em-dashes: count stays 2, both get a fix *)
      let two = "\xd0\xb0 \xe2\x80\x94 b \xd0\xb2 \xe2\x80\x94 \xd0\xb3" in
      expect
        (fires_with_count "RU-001" two 2
        && List.length (fix_edits "RU-001" two) = 2)
        (tag ^ ": count=2 & 2 fixes"));
  run "RU-001 no fix for line-leading space (no oscillation)" (fun tag ->
      (* leading-space+em-dash: fixing it would create a line-leading NBSP that
         SPC-029/032 would revert — guard suppresses the fix, count preserved *)
      let leading = " \xe2\x80\x94 \xd0\xb0" in
      expect
        (fires_with_count "RU-001" leading 1 && fix_edits "RU-001" leading = [])
        (tag ^ ": guarded"));
  run "RU-001 no fix in non-Cyrillic context (SPC-033 mutual exclusion)"
    (fun tag ->
      (* Latin context: SPC-033 (inverse) owns the em-dash spacing here, so
         RU-001 fires+counts but emits NO fix — prevents space<->NBSP cycling *)
      expect
        (fires_with_count "RU-001" "a \xe2\x80\x94 b" 1
        && fix_edits "RU-001" "a \xe2\x80\x94 b" = [])
        (tag ^ ": Latin context, count preserved, no fix"));

  (* ══════════════════════════════════════════════════════════════════════
     PL-001: NB-space before abbreviations r., nr, s.
     ══════════════════════════════════════════════════════════════════════ *)
  run "PL-001 fires on space before r." (fun tag ->
      expect (fires "PL-001" "w r. 2024") (tag ^ ": space+r."));
  run "PL-001 fires on space before nr " (fun tag ->
      expect (fires "PL-001" "pod nr 5") (tag ^ ": space+nr"));
  run "PL-001 fires on space before s." (fun tag ->
      expect (fires "PL-001" "na s. 12") (tag ^ ": space+s."));
  run "PL-001 clean no abbreviations" (fun tag ->
      expect (does_not_fire "PL-001" "just text") (tag ^ ": no Polish abbr"));
  (* PL-001 fix producer (v27.1.11): replaces the regular ASCII space before a
     Polish abbreviation (`r.`, `nr `, `s.`) with a NBSP (0xC2 0xA0). *)
  let pl001_apply src =
    match Latex_parse_lib.Cst_edit.apply_all src (fix_edits "PL-001" src) with
    | Ok r -> r
    | Error _ -> src
  in
  run "PL-001 emits fix on space before r." (fun tag ->
      expect (fires_with_fix "PL-001" "w r. 2024") (tag ^ ": has fix"));
  run "PL-001 fix replaces space with NBSP before r." (fun tag ->
      expect
        (pl001_apply "w r. 2024" = "w\xc2\xa0r. 2024")
        (tag ^ ": r. -> NBSP"));
  run "PL-001 fix replaces space with NBSP before nr" (fun tag ->
      expect (pl001_apply "pod nr 5" = "pod\xc2\xa0nr 5") (tag ^ ": nr -> NBSP"));
  run "PL-001 fix replaces space with NBSP before s." (fun tag ->
      expect (pl001_apply "na s. 12" = "na\xc2\xa0s. 12") (tag ^ ": s. -> NBSP"));
  run "PL-001 fix idempotent / convergent" (fun tag ->
      let once = pl001_apply "w r. 2024" in
      (* NBSP before the abbreviation cannot re-fire (detector needs 0x20). *)
      expect (pl001_apply once = once) (tag ^ ": second apply no-op"));
  run "PL-001 count preserved (2 triggers)" (fun tag ->
      expect
        (fires_with_count "PL-001" "w r. 2024 i na s. 12" 2)
        (tag ^ ": count=2"));

  (* ══════════════════════════════════════════════════════════════════════
     CS-001: CS/SK thin NB-space before degree-C forbidden
     ══════════════════════════════════════════════════════════════════════ *)
  run "CS-001 fires on thin space before degree-C" (fun tag ->
      expect (fires "CS-001" "teplota 20\\,\xc2\xb0C") (tag ^ ": thin+degC"));
  run "CS-001 fires on NBSP before degree-C" (fun tag ->
      expect (fires "CS-001" "teplota 20\xc2\xa0\xc2\xb0C") (tag ^ ": NBSP+degC"));
  run "CS-001 clean with no space" (fun tag ->
      expect
        (does_not_fire "CS-001" "teplota 20\xc2\xb0C")
        (tag ^ ": no space ok"));
  (* CS-001 fix producer (v27.1.10): deletes the offending 2-byte space token
     (`\,` or NBSP) before °C. The digit-preceded `\,` case is left
     diagnose-only to stay convergent against the universal TYPO-057 (which
     re-inserts `\,` into any `[0-9]°C`). *)
  let cs001_apply src =
    match Latex_parse_lib.Cst_edit.apply_all src (fix_edits "CS-001" src) with
    | Ok r -> r
    | Error _ -> src
  in
  run "CS-001 emits fix on NBSP before degree-C" (fun tag ->
      expect
        (fires_with_fix "CS-001" "teplota 20\xc2\xa0\xc2\xb0C")
        (tag ^ ": has fix"));
  run "CS-001 fix deletes NBSP token" (fun tag ->
      let src = "teplota 20\xc2\xa0\xc2\xb0C" in
      expect (cs001_apply src = "teplota 20\xc2\xb0C") (tag ^ ": nbsp->clean"));
  run "CS-001 fix deletes non-digit thin-space token" (fun tag ->
      (* `\,` not preceded by a digit is safe to delete (no TYPO-057
         conflict). *)
      let src = "okolo\\,\xc2\xb0C" in
      expect (cs001_apply src = "okolo\xc2\xb0C") (tag ^ ": thin->clean"));
  run "CS-001 fix idempotent / convergent" (fun tag ->
      let src = "teplota 20\xc2\xa0\xc2\xb0C" in
      let once = cs001_apply src in
      (* second application is a no-op (fixpoint reached in one step) *)
      expect (cs001_apply once = once) (tag ^ ": second apply no-op"));
  run "CS-001 digit thin-space stays diagnose-only (no fix, still fires)"
    (fun tag ->
      (* `20\,°C`: fires + counts, but emits NO fix (TYPO-057 convergence guard)
         — the byte string is returned unchanged. *)
      let src = "teplota 20\\,\xc2\xb0C" in
      expect
        (fires "CS-001" src && cs001_apply src = src)
        (tag ^ ": fires but unchanged"));
  run "CS-001 count preserved (2 triggers)" (fun tag ->
      expect
        (fires_with_count "CS-001" "20\\,\xc2\xb0C a 30\xc2\xa0\xc2\xb0C" 2)
        (tag ^ ": count=2"));

  (* ══════════════════════════════════════════════════════════════════════
     CS-002: CS/SK date format must be 30.\,1.\,2026
     ══════════════════════════════════════════════════════════════════════ *)
  run "CS-002 fires on bare date" (fun tag ->
      expect (fires "CS-002" "dne 30.1.2026") (tag ^ ": bare date"));
  run "CS-002 clean with thin space" (fun tag ->
      expect
        (does_not_fire "CS-002" "dne 30.\\,1.\\,2026")
        (tag ^ ": correct thin space"));
  run "CS-002 clean no date" (fun tag ->
      expect (does_not_fire "CS-002" "just text") (tag ^ ": no date pattern"));

  (* ══════════════════════════════════════════════════════════════════════
     EL-001: Greek oxia vs tonos normalisation
     ══════════════════════════════════════════════════════════════════════ *)
  run "EL-001 fires on polytonic accent" (fun tag ->
      (* U+1F00 Greek Small Letter Alpha with Psili = E1 BC 80 *)
      expect (fires "EL-001" "\xe1\xbc\x80") (tag ^ ": polytonic alpha"));
  run "EL-001 fires on oxia" (fun tag ->
      (* U+1F71 Greek Small Letter Alpha with Oxia = E1 BD B1 *)
      expect (fires "EL-001" "\xe1\xbd\xb1") (tag ^ ": oxia alpha"));
  run "EL-001 clean with tonos" (fun tag ->
      (* U+03AC Greek Small Letter Alpha with Tonos = CE AC (in range CE 84-CE
         BF) *)
      expect (does_not_fire "EL-001" "\xce\xac") (tag ^ ": tonos alpha ok"));
  run "EL-001 clean ASCII" (fun tag ->
      expect (does_not_fire "EL-001" "just text") (tag ^ ": ASCII only"));
  (* v27.1.10 fix producer: oxia -> tonos NFC normalisation. *)
  let el_apply s edits =
    match Latex_parse_lib.Cst_edit.apply_all s edits with
    | Ok s' -> s'
    | Error _ -> s
  in
  run "EL-001 fix rewrites all seven lowercase oxia vowels" (fun tag ->
      (* input: U+1F71 1F73 1F75 1F77 1F79 1F7B 1F7D separated by spaces.
         expected tonos: U+03AC 03AD 03AE 03AF 03CC 03CD 03CE (CE AC / CE AD /
         CE AE / CE AF / CF 8C / CF 8D / CF 8E). *)
      let input =
        "\xe1\xbd\xb1 \xe1\xbd\xb3 \xe1\xbd\xb5 \xe1\xbd\xb7 \xe1\xbd\xb9 \
         \xe1\xbd\xbb \xe1\xbd\xbd"
      in
      let expected =
        "\xce\xac \xce\xad \xce\xae \xce\xaf \xcf\x8c \xcf\x8d \xcf\x8e"
      in
      let out = el_apply input (fix_edits "EL-001" input) in
      expect (out = expected) (tag ^ ": oxia->tonos"));
  run "EL-001 fix rewrites a capital oxia vowel" (fun tag ->
      (* U+1FBB Alpha with Oxia = E1 BE BB -> U+0386 Alpha with Tonos = CE 86 *)
      let input = "\xe1\xbe\xbb" in
      let out = el_apply input (fix_edits "EL-001" input) in
      expect (out = "\xce\x86") (tag ^ ": capital oxia->tonos"));
  run "EL-001 fix is idempotent and convergent" (fun tag ->
      (* U+1F79 omicron oxia -> U+03CC omicron tonos *)
      let input = "\xce\xbb\xe1\xbd\xb9\xce\xb3\xce\xbf\xcf\x82" in
      let out1 = el_apply input (fix_edits "EL-001" input) in
      let out2 = el_apply out1 (fix_edits "EL-001" out1) in
      (* second pass: the tonos target does not fire EL-001 (out of oxia range),
         so no further edits and output is stable. *)
      expect
        (out1 = out2 && does_not_fire "EL-001" out1)
        (tag ^ ": idempotent/convergent"));
  run "EL-001 count preserved after adding fix" (fun tag ->
      (* Two oxia + one non-oxia polytonic (U+1F00 psili, no fix) all still
         counted: count must be 3. *)
      expect
        (fires_with_count "EL-001" "\xe1\xbd\xb1\xe1\xbc\x80\xe1\xbd\xb3" 3)
        (tag ^ ": count=3 incl. non-oxia polytonic"));

  (* ══════════════════════════════════════════════════════════════════════
     RO-001: use S-comma not S-cedilla
     ══════════════════════════════════════════════════════════════════════ *)
  run "RO-001 fires on S-cedilla upper" (fun tag ->
      (* U+015E = C5 9E *)
      expect (fires "RO-001" "\xc5\x9e") (tag ^ ": S-cedilla upper"));
  run "RO-001 fires on s-cedilla lower" (fun tag ->
      (* U+015F = C5 9F *)
      expect (fires "RO-001" "\xc5\x9f") (tag ^ ": s-cedilla lower"));
  run "RO-001 fires on T-cedilla" (fun tag ->
      (* U+0162 = C5 A2 *)
      expect (fires "RO-001" "\xc5\xa2") (tag ^ ": T-cedilla"));
  run "RO-001 count=3" (fun tag ->
      expect
        (fires_with_count "RO-001" "\xc5\x9e\xc5\x9f\xc5\xa2" 3)
        (tag ^ ": count=3"));
  run "RO-001 clean with S-comma" (fun tag ->
      (* U+0218 = C8 98, U+0219 = C8 99 *)
      expect (does_not_fire "RO-001" "\xc8\x98\xc8\x99") (tag ^ ": S-comma ok"));
  (* v27.1.9 fix producer: cedilla -> comma-below replacements. *)
  let apply_all s edits =
    match Latex_parse_lib.Cst_edit.apply_all s edits with
    | Ok s' -> s'
    | Error _ -> s
  in
  run "RO-001 fix rewrites all four cedilla forms" (fun tag ->
      (* input: Ş ş Ţ ţ separated by spaces. expected: Ș ș Ț ț
         (U+0218/0219/021A/021B = C8 98/99/9A/9B). *)
      let input = "\xc5\x9e \xc5\x9f \xc5\xa2 \xc5\xa3" in
      let expected = "\xc8\x98 \xc8\x99 \xc8\x9a \xc8\x9b" in
      let out = apply_all input (fix_edits "RO-001" input) in
      expect (out = expected) (tag ^ ": cedilla->comma-below"));
  run "RO-001 fix is idempotent" (fun tag ->
      let input = "Ru\xc5\x9fine \xc5\xa2ar\xc4\x83" in
      let out1 = apply_all input (fix_edits "RO-001" input) in
      (* second pass: rule must no longer fire, so no further edits. *)
      let out2 = apply_all out1 (fix_edits "RO-001" out1) in
      expect (out1 = out2 && does_not_fire "RO-001" out1) (tag ^ ": idempotent"));
  run "RO-001 count preserved after adding fix" (fun tag ->
      expect
        (fires_with_count "RO-001" "\xc5\x9e\xc5\x9f\xc5\xa2\xc5\xa3" 4)
        (tag ^ ": count=4 all four forms"));

  (* ══════════════════════════════════════════════════════════════════════
     AR-002: ASCII hyphen in phone numbers
     ══════════════════════════════════════════════════════════════════════ *)
  run "AR-002 fires on hyphen between Arabic digits" (fun tag ->
      (* Arabic digit 1 = D9 A1, digit 2 = D9 A2 *)
      expect
        (fires "AR-002" "\xd9\xa1-\xd9\xa2")
        (tag ^ ": arabic digits+hyphen"));
  run "AR-002 clean no Arabic digits" (fun tag ->
      expect (does_not_fire "AR-002" "123-456") (tag ^ ": ASCII digits ok"));
  run "AR-002 clean no hyphen" (fun tag ->
      expect (does_not_fire "AR-002" "\xd9\xa1\xd9\xa2") (tag ^ ": no hyphen"));
  (* v27.1.11 fix producer: ASCII hyphen between Arabic digits -> \arabicdash *)
  run "AR-002 fix replaces hyphen with macro" (fun tag ->
      (* input: ١-٢ (D9 A1, '-', D9 A2). expected: ١\arabicdash٢ *)
      let input = "\xd9\xa1-\xd9\xa2" in
      let expected = "\xd9\xa1\\arabicdash\xd9\xa2" in
      let out = apply_all input (fix_edits "AR-002" input) in
      expect (out = expected) (tag ^ ": hyphen->\\arabicdash"));
  run "AR-002 fix is idempotent" (fun tag ->
      (* two independent digit pairs: ١-٢ ٣-٤ (the detector consumes the
         trailing digit, so hyphens must not share a flanking digit). *)
      let input = "\xd9\xa1-\xd9\xa2\xd9\xa3-\xd9\xa4" in
      let out1 = apply_all input (fix_edits "AR-002" input) in
      (* second pass: rule must no longer fire, so no further edits. *)
      let out2 = apply_all out1 (fix_edits "AR-002" out1) in
      expect (out1 = out2 && does_not_fire "AR-002" out1) (tag ^ ": idempotent"));
  run "AR-002 count preserved after adding fix" (fun tag ->
      expect
        (fires_with_count "AR-002" "\xd9\xa1-\xd9\xa2\xd9\xa3-\xd9\xa4" 2)
        (tag ^ ": count=2 two hyphens"));

  (* ══════════════════════════════════════════════════════════════════════
     HE-001: apostrophe used instead of geresh
     ══════════════════════════════════════════════════════════════════════ *)
  run "HE-001 fires on apostrophe after Hebrew" (fun tag ->
      (* Hebrew Alef = D7 90, then apostrophe ' *)
      expect (fires "HE-001" "\xd7\x90'") (tag ^ ": Hebrew+apostrophe"));
  run "HE-001 fires on apostrophe after Bet" (fun tag ->
      (* Hebrew Bet = D7 91 *)
      expect (fires "HE-001" "\xd7\x91'") (tag ^ ": Bet+apostrophe"));
  run "HE-001 clean with geresh" (fun tag ->
      (* Geresh U+05F3 = D7 B3 *)
      expect (does_not_fire "HE-001" "\xd7\x90\xd7\xb3") (tag ^ ": geresh ok"));
  run "HE-001 clean no Hebrew" (fun tag ->
      expect (does_not_fire "HE-001" "it's fine") (tag ^ ": ASCII context"));
  (* v27.1.10 fix producer: apostrophe -> geresh U+05F3 (\xd7\xb3) *)
  run "HE-001 fix replaces apostrophe with geresh" (fun tag ->
      let src = "\xd7\x90'" in
      let out =
        match
          Latex_parse_lib.Cst_edit.apply_all src (fix_edits "HE-001" src)
        with
        | Ok s -> s
        | Error _ -> src
      in
      expect (out = "\xd7\x90\xd7\xb3") (tag ^ ": Alef+geresh output"));
  run "HE-001 fix count unchanged (2 apostrophes)" (fun tag ->
      expect
        (fires_with_count "HE-001" "\xd7\x90' \xd7\x91'" 2)
        (tag ^ ": count=2"));
  run "HE-001 fix idempotent / convergent" (fun tag ->
      let src = "\xd7\x90' \xd7\x91'" in
      let out =
        match
          Latex_parse_lib.Cst_edit.apply_all src (fix_edits "HE-001" src)
        with
        | Ok s -> s
        | Error _ -> src
      in
      expect
        (out = "\xd7\x90\xd7\xb3 \xd7\x91\xd7\xb3")
        (tag ^ ": both replaced");
      expect (does_not_fire "HE-001" out) (tag ^ ": no refire on geresh"));

  (* ══════════════════════════════════════════════════════════════════════
     ZH-001: western period after CJK character
     ══════════════════════════════════════════════════════════════════════ *)
  run "ZH-001 fires on CJK+period" (fun tag ->
      (* U+4E2D (zhong) = E4 B8 AD, then ASCII . *)
      expect (fires "ZH-001" "\xe4\xb8\xad.") (tag ^ ": CJK+period"));
  run "ZH-001 count=2" (fun tag ->
      expect
        (fires_with_count "ZH-001" "\xe4\xb8\xad. \xe4\xba\xba." 2)
        (tag ^ ": count=2"));
  run "ZH-001 clean with ideographic full stop" (fun tag ->
      (* U+3002 = E3 80 82 *)
      expect
        (does_not_fire "ZH-001" "\xe4\xb8\xad\xe3\x80\x82")
        (tag ^ ": Chinese full stop ok"));
  run "ZH-001 clean ASCII only" (fun tag ->
      expect (does_not_fire "ZH-001" "text. more") (tag ^ ": ASCII context"));

  (* ══════════════════════════════════════════════════════════════════════
     JA-001: half-width katakana present
     ══════════════════════════════════════════════════════════════════════ *)
  run "JA-001 fires on half-width katakana" (fun tag ->
      (* U+FF76 half-width Ka = EF BD B6 *)
      expect (fires "JA-001" "\xef\xbd\xb6") (tag ^ ": half-width Ka"));
  run "JA-001 fires on half-width A" (fun tag ->
      (* U+FF71 half-width A = EF BD B1 *)
      expect (fires "JA-001" "\xef\xbd\xb1") (tag ^ ": half-width A"));
  run "JA-001 clean with full-width" (fun tag ->
      (* Full-width katakana Ka = U+30AB = E3 82 AB *)
      expect (does_not_fire "JA-001" "\xe3\x82\xab") (tag ^ ": full-width Ka ok"));
  run "JA-001 clean ASCII" (fun tag ->
      expect (does_not_fire "JA-001" "just text") (tag ^ ": ASCII only"));

  (* ══════════════════════════════════════════════════════════════════════
     JA-002: U+FF5E tilde normalise to wave-dash
     ══════════════════════════════════════════════════════════════════════ *)
  run "JA-002 fires on fullwidth tilde" (fun tag ->
      (* U+FF5E = EF BD 9E *)
      expect (fires "JA-002" "10\xef\xbd\x9e20") (tag ^ ": fullwidth tilde"));
  run "JA-002 count=2" (fun tag ->
      expect
        (fires_with_count "JA-002" "10\xef\xbd\x9e20\xef\xbd\x9e30" 2)
        (tag ^ ": count=2"));
  run "JA-002 clean with wave-dash" (fun tag ->
      (* U+301C wave dash = E3 80 9C *)
      expect (does_not_fire "JA-002" "10\xe3\x80\x9c20") (tag ^ ": wave-dash ok"));
  run "JA-002 clean ASCII tilde" (fun tag ->
      expect (does_not_fire "JA-002" "10~20") (tag ^ ": ASCII tilde ok"));
  (* v27.1.9 fix producer: U+FF5E (EF BD 9E) -> U+301C wave dash (E3 80 9C). *)
  let ja002_apply src =
    match Latex_parse_lib.Cst_edit.apply_all src (fix_edits "JA-002" src) with
    | Ok s -> s
    | Error _ -> src
  in
  run "JA-002 fix rewrites tilde to wave-dash" (fun tag ->
      let src = "10\xef\xbd\x9e20" in
      expect
        (List.length (fix_edits "JA-002" src) = 1
        && ja002_apply src = "10\xe3\x80\x9c20")
        (tag ^ ": EF BD 9E -> E3 80 9C"));
  run "JA-002 fix rewrites all occurrences" (fun tag ->
      let src = "10\xef\xbd\x9e20\xef\xbd\x9e30" in
      expect
        (List.length (fix_edits "JA-002" src) = 2
        && ja002_apply src = "10\xe3\x80\x9c20\xe3\x80\x9c30")
        (tag ^ ": both tildes rewritten"));
  run "JA-002 fix idempotent" (fun tag ->
      let src = "10\xef\xbd\x9e20" in
      let out = ja002_apply src in
      expect
        (does_not_fire "JA-002" out && ja002_apply out = out)
        (tag ^ ": second pass is a no-op"));
  run "JA-002 count unchanged after adding fix" (fun tag ->
      expect
        (fires_with_count "JA-002" "10\xef\xbd\x9e20\xef\xbd\x9e30" 2)
        (tag ^ ": count still 2"));
  run "JA-002 exempt: no fix inside comment but still fires" (fun tag ->
      (* tilde inside a comment line: still counted, but no edit emitted. *)
      let src = "% a\xef\xbd\x9eb\n" in
      expect
        (fires "JA-002" src && fix_edits "JA-002" src = [])
        (tag ^ ": comment is exempt from fix"));

  (* ══════════════════════════════════════════════════════════════════════
     KO-001: Old-Hangul jamo outside scholarly context
     ══════════════════════════════════════════════════════════════════════ *)
  run "KO-001 fires on archaic lead jamo" (fun tag ->
      (* U+1113 = E1 84 93 (archaic consonant) *)
      expect (fires "KO-001" "\xe1\x84\x93") (tag ^ ": archaic lead"));
  run "KO-001 fires on archaic vowel" (fun tag ->
      (* U+1176 = E1 85 B6 (archaic vowel) *)
      expect (fires "KO-001" "\xe1\x85\xb6") (tag ^ ": archaic vowel"));
  run "KO-001 clean with modern jamo" (fun tag ->
      (* U+1100 = E1 84 80 (modern Kiyeok, lead) *)
      expect (does_not_fire "KO-001" "\xe1\x84\x80") (tag ^ ": modern jamo ok"));
  run "KO-001 clean ASCII" (fun tag ->
      expect (does_not_fire "KO-001" "just text") (tag ^ ": ASCII only"));

  (* ══════════════════════════════════════════════════════════════════════
     HI-001: ZWJ/ZWNJ misuse next to Devanagari halant
     ══════════════════════════════════════════════════════════════════════ *)
  run "HI-001 fires on halant+ZWJ" (fun tag ->
      (* Devanagari Ka = E0 A4 95, Halant = E0 A5 8D, ZWJ = E2 80 8D *)
      expect
        (fires "HI-001" "\xe0\xa4\x95\xe0\xa5\x8d\xe2\x80\x8d\xe0\xa4\x96")
        (tag ^ ": halant+ZWJ"));
  run "HI-001 fires on halant+ZWNJ" (fun tag ->
      (* Halant = E0 A5 8D, ZWNJ = E2 80 8C *)
      expect
        (fires "HI-001" "\xe0\xa4\x95\xe0\xa5\x8d\xe2\x80\x8c\xe0\xa4\x96")
        (tag ^ ": halant+ZWNJ"));
  run "HI-001 clean without ZWJ" (fun tag ->
      (* Normal halant conjunct without ZWJ/ZWNJ *)
      expect
        (does_not_fire "HI-001" "\xe0\xa4\x95\xe0\xa5\x8d\xe0\xa4\x96")
        (tag ^ ": normal halant ok"));
  run "HI-001 clean ASCII" (fun tag ->
      expect (does_not_fire "HI-001" "just text") (tag ^ ": ASCII only"));
  (* v27.1.10 fix producer: remove_char deletes the misused ZWJ/ZWNJ. *)
  run "HI-001 fix removes ZWJ after halant" (fun tag ->
      (* Ka=E0 A4 95, Halant=E0 A5 8D, ZWJ=E2 80 8D, Kha=E0 A4 96 *)
      let input = "\xe0\xa4\x95\xe0\xa5\x8d\xe2\x80\x8d\xe0\xa4\x96" in
      let expected = "\xe0\xa4\x95\xe0\xa5\x8d\xe0\xa4\x96" in
      let out = apply_all input (fix_edits "HI-001" input) in
      expect (out = expected) (tag ^ ": ZWJ deleted"));
  run "HI-001 fix removes ZWNJ after halant" (fun tag ->
      (* ZWNJ = E2 80 8C *)
      let input = "\xe0\xa4\x95\xe0\xa5\x8d\xe2\x80\x8c\xe0\xa4\x96" in
      let expected = "\xe0\xa4\x95\xe0\xa5\x8d\xe0\xa4\x96" in
      let out = apply_all input (fix_edits "HI-001" input) in
      expect (out = expected) (tag ^ ": ZWNJ deleted"));
  run "HI-001 fix is idempotent" (fun tag ->
      let input = "\xe0\xa4\x95\xe0\xa5\x8d\xe2\x80\x8d\xe0\xa4\x96" in
      let out1 = apply_all input (fix_edits "HI-001" input) in
      let out2 = apply_all out1 (fix_edits "HI-001" out1) in
      expect (out1 = out2 && does_not_fire "HI-001" out1) (tag ^ ": idempotent"));
  run "HI-001 count preserved after adding fix" (fun tag ->
      (* two triggers → count=2 *)
      let s =
        "\xe0\xa4\x95\xe0\xa5\x8d\xe2\x80\x8d\xe0\xa4\x96\xe0\xa5\x8d\xe2\x80\x8c\xe0\xa4\x97"
      in
      expect (fires_with_count "HI-001" s 2) (tag ^ ": count=2 unchanged"));
  run "HI-001 exempt: no fix inside comment but still fires" (fun tag ->
      let src = "% \xe0\xa4\x95\xe0\xa5\x8d\xe2\x80\x8d\xe0\xa4\x96" in
      expect
        (fires "HI-001" src && fix_edits "HI-001" src = [])
        (tag ^ ": comment is exempt from fix"))

let () = finalise "locale"
