(* ══════════════════════════════════════════════════════════════════════
   test_language_detect — tests for document language detection
   ══════════════════════════════════════════════════════════════════════ *)

open Latex_parse_lib

let pass = ref 0
let fail = ref 0

let check name cond =
  if cond then (
    incr pass;
    Printf.printf "  [PASS] %s\n" name)
  else (
    incr fail;
    Printf.printf "  [FAIL] %s\n" name)

let () =
  Printf.printf "[lang-detect] running tests...\n";

  (* ── Babel detection ─────────────────────────────────────────────── *)
  check "babel french"
    (Language_detect.detect_language
       {|\documentclass{article}
\usepackage[french]{babel}
\begin{document}Bonjour\end{document}|}
     = "fr");

  check "babel ngerman"
    (Language_detect.detect_language
       {|\usepackage[ngerman]{babel}
\begin{document}Hallo\end{document}|}
     = "de");

  check "babel russian"
    (Language_detect.detect_language
       {|\usepackage[russian]{babel}
\begin{document}Привет\end{document}|}
     = "ru");

  check "babel multi-lang (last is main)"
    (Language_detect.detect_language
       {|\usepackage[english,french]{babel}
\begin{document}Bonjour\end{document}|}
     = "fr");

  check "babel spanish"
    (Language_detect.detect_language
       {|\usepackage[spanish]{babel}
\begin{document}Hola\end{document}|}
     = "es");

  check "babel japanese"
    (Language_detect.detect_language
       {|\usepackage[japanese]{babel}
\begin{document}こんにちは\end{document}|}
     = "ja");

  check "babel arabic"
    (Language_detect.detect_language
       {|\usepackage[arabic]{babel}
\begin{document}مرحبا\end{document}|}
     = "ar");

  (* ── Polyglossia detection ───────────────────────────────────────── *)
  check "polyglossia setdefaultlanguage arabic"
    (Language_detect.detect_language
       {|\usepackage{polyglossia}
\setdefaultlanguage{arabic}
\begin{document}مرحبا\end{document}|}
     = "ar");

  check "polyglossia setmainlanguage french"
    (Language_detect.detect_language
       {|\usepackage{polyglossia}
\setmainlanguage{french}
\begin{document}Bonjour\end{document}|}
     = "fr");

  check "polyglossia with options"
    (Language_detect.detect_language
       {|\usepackage{polyglossia}
\setdefaultlanguage[variant=british]{english}
\begin{document}Hello\end{document}|}
     = "en");

  (* ── CJK heuristic ──────────────────────────────────────────────── *)
  check "CJK Chinese characters"
    (Language_detect.detect_language
       {|\documentclass{article}
\begin{document}这是中文文档。\end{document}|}
     = "zh");

  check "katakana -> Japanese"
    (Language_detect.detect_language
       {|\documentclass{article}
\begin{document}カタカナテスト\end{document}|}
     = "ja");

  check "Arabic script -> ar"
    (Language_detect.detect_language
       {|\documentclass{article}
\begin{document}مرحبا بالعالم\end{document}|}
     = "ar");

  (* ── Fallback ────────────────────────────────────────────────────── *)
  check "no language declaration -> en"
    (Language_detect.detect_language
       {|\documentclass{article}
\begin{document}Hello world\end{document}|}
     = "en");

  check "empty document -> en"
    (Language_detect.detect_language "" = "en");

  check "pure ASCII no preamble -> en"
    (Language_detect.detect_language "Just some text." = "en");

  (* ── Priority: explicit > heuristic ──────────────────────────────── *)
  check "babel overrides CJK heuristic"
    (Language_detect.detect_language
       {|\usepackage[english]{babel}
\begin{document}这是中文 but babel says English\end{document}|}
     = "en");

  (* ── Language pack registry ──────────────────────────────────────── *)
  check "live packs includes ar"
    (List.mem "ar" Language_detect.live_packs);

  check "live packs includes ja"
    (List.mem "ja" Language_detect.live_packs);

  check "live packs includes zh"
    (List.mem "zh" Language_detect.live_packs);

  check "all_packs >= 21"
    (List.length Language_detect.all_packs >= 21);

  (* ── Babel mapping coverage ──────────────────────────────────────── *)
  check "resolve french"
    (Language_detect.resolve_babel_name "french" = Some "fr");

  check "resolve unknown returns None"
    (Language_detect.resolve_babel_name "klingon" = None);

  check "resolve is case-insensitive"
    (Language_detect.resolve_babel_name "FRENCH" = Some "fr");

  (* ── Summary ─────────────────────────────────────────────────────── *)
  Printf.printf "[lang-detect] %d passed, %d failed\n" !pass !fail;
  if !fail > 0 then exit 1
