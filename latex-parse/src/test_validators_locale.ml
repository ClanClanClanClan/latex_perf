(** Unit tests for locale validator rules (FR, PT, RU, PL, CS, EL, RO, AR, HE,
    ZH, JA, KO, HI). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[locale] FAIL: %s\n%!" msg;
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

  (* ══════════════════════════════════════════════════════════════════════ *)
  if !fails > 0 then (
    Printf.eprintf "[locale] %d failure(s) in %d cases\n%!" !fails !cases;
    exit 1)
  else Printf.printf "[locale] PASS %d cases\n%!" !cases
