(* ══════════════════════════════════════════════════════════════════════
   Language_detect — document language detection from LaTeX preamble
   ══════════════════════════════════════════════════════════════════════

   Extracts document language from: - \usepackage[lang]{babel} -
   \usepackage{polyglossia} + \setdefaultlanguage{lang} - \setmainlanguage{lang}
   - CJK glyph heuristic (presence of CJK codepoints) - Fallback: "en"

   Returns ISO 639-1 codes: "en", "fr", "de", "ja", "zh", "ar", etc. *)

(* ── Babel language name → ISO 639-1 mapping ────────────────────────── *)

let babel_to_iso =
  [
    (* Romance *)
    ("french", "fr");
    ("francais", "fr");
    ("frenchb", "fr");
    ("acadian", "fr");
    ("spanish", "es");
    ("castilian", "es");
    ("castillan", "es");
    ("portuguese", "pt");
    ("brazilian", "pt");
    ("portuges", "pt");
    ("italian", "it");
    ("romanian", "ro");
    ("catalan", "ca");
    (* Germanic *)
    ("english", "en");
    ("british", "en");
    ("american", "en");
    ("UKenglish", "en");
    ("USenglish", "en");
    ("australian", "en");
    ("newzealand", "en");
    ("german", "de");
    ("ngerman", "de");
    ("ogerman", "de");
    ("austrian", "de");
    ("naustrian", "de");
    ("swissgerman", "de");
    ("dutch", "nl");
    ("afrikaans", "nl");
    ("swedish", "sv");
    ("norsk", "no");
    ("nynorsk", "no");
    ("danish", "da");
    ("icelandic", "is");
    (* Slavic *)
    ("russian", "ru");
    ("ukrainian", "uk");
    ("polish", "pl");
    ("czech", "cs");
    ("slovak", "sk");
    ("serbian", "sr");
    ("croatian", "hr");
    ("slovenian", "sl");
    ("bulgarian", "bg");
    (* CJK *)
    ("japanese", "ja");
    ("chinese", "zh");
    ("korean", "ko");
    (* RTL *)
    ("arabic", "ar");
    ("hebrew", "he");
    ("farsi", "fa");
    ("persian", "fa");
    (* Greek *)
    ("greek", "el");
    ("polutonikogreek", "el");
    (* Indic *)
    ("hindi", "hi");
    ("tamil", "ta");
    ("bengali", "bn");
    (* Turkish *)
    ("turkish", "tr");
    (* Other *)
    ("finnish", "fi");
    ("hungarian", "hu");
    ("estonian", "et");
    ("latvian", "lv");
    ("lithuanian", "lt");
    ("thai", "th");
    ("vietnamese", "vi");
    ("welsh", "cy");
    ("irish", "ga");
    ("scottish", "gd");
  ]

let babel_tbl = Hashtbl.create 128
let () = List.iter (fun (k, v) -> Hashtbl.replace babel_tbl k v) babel_to_iso

let resolve_babel_name name =
  let name_lc = String.lowercase_ascii name in
  match Hashtbl.find_opt babel_tbl name_lc with
  | Some iso -> Some iso
  | None -> None (* unknown language name *)

(* ── Preamble extraction ────────────────────────────────────────────── *)

let extract_preamble s =
  let tag = "\\begin{document}" in
  let tlen = String.length tag in
  let n = String.length s in
  let i = ref 0 in
  let pos = ref n in
  while !i <= n - tlen do
    if String.sub s !i tlen = tag then (
      pos := !i;
      i := n)
    else incr i
  done;
  String.sub s 0 !pos

(* ── Babel detection ────────────────────────────────────────────────── *)

let detect_babel preamble =
  (* Match \usepackage[lang]{babel} or \usepackage[lang1,lang2]{babel} *)
  let re = Re_compat.regexp {|\\usepackage\[\([^]]*\)\]{babel}|} in
  try
    let _mr, _ = Re_compat.search_forward re preamble 0 in
    ignore _mr;
    let opts = Re_compat.matched_group _mr 1 preamble in
    (* Parse comma-separated language names, last one is main *)
    let langs = String.split_on_char ',' opts in
    let langs = List.map String.trim langs in
    (* In babel, the LAST option is the main language *)
    match List.rev langs with
    | main :: _ -> resolve_babel_name main
    | [] -> None
  with Not_found -> None

(* ── Polyglossia detection ──────────────────────────────────────────── *)

let detect_polyglossia preamble =
  (* Match \setdefaultlanguage{lang} or \setmainlanguage{lang} *)
  let re1 =
    Re_compat.regexp {|\\setdefaultlanguage\(\[[^]]*\]\)?{\([^}]+\)}|}
  in
  let re2 = Re_compat.regexp {|\\setmainlanguage\(\[[^]]*\]\)?{\([^}]+\)}|} in
  let try_re re =
    try
      let _mr, _ = Re_compat.search_forward re preamble 0 in
      ignore _mr;
      let lang = Re_compat.matched_group _mr 2 preamble in
      resolve_babel_name lang
    with Not_found | Invalid_argument _ -> None
  in
  match try_re re1 with Some _ as r -> r | None -> try_re re2

(* ── CJK heuristic detection ────────────────────────────────────────── *)

(* ── OPEN-061: both scans were COMMENT-BLIND, and the byte scans accepted
   invalid UTF-8 ─────────────────────────────────────────────────────

   Measured over 409 real corpus roots (2026-09-05): - ALL 32 CJK-heuristic
   detections were driven by CJK characters appearing ONLY inside `%` comments —
   translator notes and author comments in otherwise-English papers. - 6 papers
   carry a babel line that exists only in a comment; the comment-blind regex
   read 3 of them as declarations. - The byte helpers tested the LEAD byte only,
   so a latin-1 'é' (0xE9) satisfied `has_cjk_codepoints` and the paper was
   labelled Chinese. That is the same lead-byte-without-continuation defect
   recorded for ENC-008 in OPEN-059.

   Together these made detect_language wrong on 8.6% of papers. Nothing in
   production consumed it yet (its only callers are tests and
   run_all_for_language, itself test-only), so this is a prerequisite fix with
   no behaviour change today — it is what makes language gating affordable. *)
let strip_line_comments (s : string) : string =
  let n = String.length s in
  let b = Buffer.create n in
  let i = ref 0 in
  let in_comment = ref false in
  while !i < n do
    let c = s.[!i] in
    if !in_comment then
      if c = '\n' then (
        in_comment := false;
        Buffer.add_char b c)
      else ()
    else if c = '\\' && !i + 1 < n then (
      (* an escaped %% is literal text, not a comment opener *)
      Buffer.add_char b c;
      Buffer.add_char b s.[!i + 1];
      incr i)
    else if c = '%' then in_comment := true
    else Buffer.add_char b c;
    incr i
  done;
  Buffer.contents b

(* A UTF-8 continuation byte. Checking these is what stops a latin-1 or binary
   byte in a lead-byte range from being read as CJK. *)
let is_cont b = b land 0xC0 = 0x80

let has_cjk_codepoints s =
  (* Check for CJK Unified Ideographs (U+4E00-U+9FFF) in UTF-8: 3-byte sequences
     starting with 0xE4-0xE9 *)
  let n = String.length s in
  let rec loop i =
    if i >= n - 2 then false
    else
      let b0 = Char.code s.[i] in
      if
        b0 >= 0xE4
        && b0 <= 0xE9
        && is_cont (Char.code s.[i + 1])
        && is_cont (Char.code s.[i + 2])
      then true
      else loop (i + 1)
  in
  loop 0

let has_katakana s =
  (* Katakana (U+30A0-U+30FF): 3-byte UTF-8 starting with 0xE3 0x82 0xA0+ *)
  let n = String.length s in
  let rec loop i =
    if i >= n - 2 then false
    else
      let b0 = Char.code s.[i] in
      let b1 = Char.code s.[i + 1] in
      if
        b0 = 0xE3
        && b1 >= 0x82
        && b1 <= 0x83
        && is_cont b1
        && is_cont (Char.code s.[i + 2])
      then true
      else loop (i + 1)
  in
  loop 0

let has_hangul s =
  (* Hangul Syllables (U+AC00-U+D7AF): 3-byte UTF-8 starting with 0xEA-0xED *)
  let n = String.length s in
  let rec loop i =
    if i >= n - 2 then false
    else
      let b0 = Char.code s.[i] in
      if
        b0 >= 0xEA
        && b0 <= 0xED
        && is_cont (Char.code s.[i + 1])
        && is_cont (Char.code s.[i + 2])
      then true
      else loop (i + 1)
  in
  loop 0

let has_arabic s =
  (* Arabic (U+0600-U+06FF): 2-byte UTF-8 starting with 0xD8-0xDB *)
  let n = String.length s in
  let rec loop i =
    if i >= n - 1 then false
    else
      let b0 = Char.code s.[i] in
      if b0 >= 0xD8 && b0 <= 0xDB && is_cont (Char.code s.[i + 1]) then true
      else loop (i + 1)
  in
  loop 0

let detect_cjk_heuristic s =
  if has_hangul s then Some "ko"
  else if has_katakana s then Some "ja"
  else if has_cjk_codepoints s then Some "zh"
  else if has_arabic s then Some "ar"
  else None

(* ── Main detection ─────────────────────────────────────────────────── *)

let detect_language ?(default = "en") (s : string) : string =
  (* OPEN-061: strip comments before BOTH scans. A babel line or a CJK character
     inside a `%` comment is not a declaration about the document. *)
  let live = strip_line_comments s in
  let preamble = extract_preamble live in
  (* Priority: explicit declaration > heuristic > default *)
  match detect_babel preamble with
  | Some lang -> lang
  | None -> (
      match detect_polyglossia preamble with
      | Some lang -> lang
      | None -> (
          match detect_cjk_heuristic live with
          | Some lang -> lang
          | None -> default))

(* ── Language pack registry ─────────────────────────────────────────── *)

let live_packs = [ "en"; "fr"; "de"; "es"; "ja"; "zh"; "ar" ]

let stubbed_packs =
  [
    "ko";
    "ru";
    "pl";
    "pt";
    "cs";
    "el";
    "ro";
    "he";
    "hi";
    "tr";
    "nl";
    "cy";
    "sv";
    "it";
  ]

let all_packs = live_packs @ stubbed_packs
