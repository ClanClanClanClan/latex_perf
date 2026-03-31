(* ══════════════════════════════════════════════════════════════════════
   Language_detect — document language detection from LaTeX preamble
   ══════════════════════════════════════════════════════════════════════

   Extracts document language from:
     - \usepackage[lang]{babel}
     - \usepackage{polyglossia} + \setdefaultlanguage{lang}
     - \setmainlanguage{lang}
     - CJK glyph heuristic (presence of CJK codepoints)
     - Fallback: "en"

   Returns ISO 639-1 codes: "en", "fr", "de", "ja", "zh", "ar", etc.
*)

(* ── Babel language name → ISO 639-1 mapping ────────────────────────── *)

let babel_to_iso = [
  (* Romance *)
  ("french", "fr"); ("francais", "fr"); ("frenchb", "fr"); ("acadian", "fr");
  ("spanish", "es"); ("castilian", "es"); ("castillan", "es");
  ("portuguese", "pt"); ("brazilian", "pt"); ("portuges", "pt");
  ("italian", "it"); ("romanian", "ro"); ("catalan", "ca");
  (* Germanic *)
  ("english", "en"); ("british", "en"); ("american", "en"); ("UKenglish", "en");
  ("USenglish", "en"); ("australian", "en"); ("newzealand", "en");
  ("german", "de"); ("ngerman", "de"); ("ogerman", "de");
  ("austrian", "de"); ("naustrian", "de"); ("swissgerman", "de");
  ("dutch", "nl"); ("afrikaans", "nl");
  ("swedish", "sv"); ("norsk", "no"); ("nynorsk", "no"); ("danish", "da");
  ("icelandic", "is");
  (* Slavic *)
  ("russian", "ru"); ("ukrainian", "uk"); ("polish", "pl");
  ("czech", "cs"); ("slovak", "sk"); ("serbian", "sr");
  ("croatian", "hr"); ("slovenian", "sl"); ("bulgarian", "bg");
  (* CJK *)
  ("japanese", "ja"); ("chinese", "zh"); ("korean", "ko");
  (* RTL *)
  ("arabic", "ar"); ("hebrew", "he"); ("farsi", "fa"); ("persian", "fa");
  (* Greek *)
  ("greek", "el"); ("polutonikogreek", "el");
  (* Indic *)
  ("hindi", "hi"); ("tamil", "ta"); ("bengali", "bn");
  (* Turkish *)
  ("turkish", "tr");
  (* Other *)
  ("finnish", "fi"); ("hungarian", "hu"); ("estonian", "et");
  ("latvian", "lv"); ("lithuanian", "lt");
  ("thai", "th"); ("vietnamese", "vi");
  ("welsh", "cy"); ("irish", "ga"); ("scottish", "gd");
]

let babel_tbl = Hashtbl.create 128
let () = List.iter (fun (k, v) -> Hashtbl.replace babel_tbl k v) babel_to_iso

let resolve_babel_name name =
  let name_lc = String.lowercase_ascii name in
  match Hashtbl.find_opt babel_tbl name_lc with
  | Some iso -> Some iso
  | None -> None  (* unknown language name *)


(* ── Preamble extraction ────────────────────────────────────────────── *)

let extract_preamble s =
  let tag = "\\begin{document}" in
  let tlen = String.length tag in
  let n = String.length s in
  let i = ref 0 in
  let pos = ref n in
  while !i <= n - tlen do
    if String.sub s !i tlen = tag then (pos := !i; i := n)
    else incr i
  done;
  String.sub s 0 !pos


(* ── Babel detection ────────────────────────────────────────────────── *)

let detect_babel preamble =
  (* Match \usepackage[lang]{babel} or \usepackage[lang1,lang2]{babel} *)
  let re = Str.regexp {|\\usepackage\[\([^]]*\)\]{babel}|} in
  try
    ignore (Str.search_forward re preamble 0);
    let opts = Str.matched_group 1 preamble in
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
  let re1 = Str.regexp {|\\setdefaultlanguage\(\[[^]]*\]\)?{\([^}]+\)}|} in
  let re2 = Str.regexp {|\\setmainlanguage\(\[[^]]*\]\)?{\([^}]+\)}|} in
  let try_re re =
    try
      ignore (Str.search_forward re preamble 0);
      let lang = Str.matched_group 2 preamble in
      resolve_babel_name lang
    with Not_found | Invalid_argument _ -> None
  in
  match try_re re1 with
  | Some _ as r -> r
  | None -> try_re re2


(* ── CJK heuristic detection ────────────────────────────────────────── *)

let has_cjk_codepoints s =
  (* Check for CJK Unified Ideographs (U+4E00-U+9FFF) in UTF-8:
     3-byte sequences starting with 0xE4-0xE9 *)
  let n = String.length s in
  let rec loop i =
    if i >= n - 2 then false
    else
      let b0 = Char.code s.[i] in
      if b0 >= 0xE4 && b0 <= 0xE9 then true
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
      let b1 = Char.code s.[i+1] in
      if b0 = 0xE3 && (b1 >= 0x82 && b1 <= 0x83) then true
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
      if b0 >= 0xEA && b0 <= 0xED then true
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
      if b0 >= 0xD8 && b0 <= 0xDB then true
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

let detect_language ?(default="en") (s : string) : string =
  let preamble = extract_preamble s in
  (* Priority: explicit declaration > heuristic > default *)
  match detect_babel preamble with
  | Some lang -> lang
  | None ->
    match detect_polyglossia preamble with
    | Some lang -> lang
    | None ->
      match detect_cjk_heuristic s with
      | Some lang -> lang
      | None -> default


(* ── Language pack registry ─────────────────────────────────────────── *)

let live_packs = ["en"; "fr"; "de"; "es"; "ja"; "zh"; "ar"]
let stubbed_packs =
  ["ko"; "ru"; "pl"; "pt"; "cs"; "el"; "ro"; "he"; "hi";
   "tr"; "nl"; "cy"; "sv"; "it"]
let all_packs = live_packs @ stubbed_packs
