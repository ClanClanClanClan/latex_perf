open Validators_common

(* Basic validators (legacy) *)

let no_tabs : rule =
  let run s =
    let cnt = ref 0 in
    String.iter (fun c -> if c = '\t' then incr cnt) s;
    if !cnt > 0 then
      Some
        {
          id = "no_tabs";
          severity = Error;
          message = "Tab characters found";
          count = !cnt;
        }
    else None
  in
  { id = "no_tabs"; run }

let require_documentclass : rule =
  let run s =
    let pilot_mode =
      match Sys.getenv_opt "L0_VALIDATORS" with
      | Some ("1" | "true" | "TRUE" | "on" | "ON" | "pilot" | "PILOT") -> true
      | _ -> false
    in
    if pilot_mode then None
    else
      let needle = "\\documentclass" in
      if
        String.length s >= String.length needle
        &&
        try
          ignore (Str.search_forward (Str.regexp_string needle) s 0);
          true
        with Not_found -> false
      then None
      else
        Some
          {
            id = "require_documentclass";
            severity = Warning;
            message = "Missing \\documentclass";
            count = 1;
          }
  in
  { id = "require_documentclass"; run }

let unmatched_braces : rule =
  let run s =
    let open String in
    let n = length s in
    let bal = ref 0 in
    for i = 0 to n - 1 do
      match s.[i] with '{' -> incr bal | '}' -> decr bal | _ -> ()
    done;
    if !bal <> 0 then
      Some
        {
          id = "unmatched_braces";
          severity = Warning;
          message = "Unmatched braces count";
          count = abs !bal;
        }
    else None
  in
  { id = "unmatched_braces"; run }

let missing_section_title : rule =
  let run s =
    let open Str in
    let re_empty = regexp "\\\\section{[ \\t\\n]*}" in
    let re_missing = regexp "\\\\section{}" in
    if string_match re_empty s 0 || string_match re_missing s 0 then
      Some
        {
          id = "missing_section_title";
          severity = Warning;
          message = "Empty section title";
          count = 1;
        }
    else None
  in
  { id = "missing_section_title"; run }

let rules_basic : rule list =
  [ no_tabs; require_documentclass; unmatched_braces; missing_section_title ]

(* Pilot L0 rules (IDs aligned with rules_v3.yaml). Info-level mapped to
   Warning. *)

let r_typo_001 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_char s '"' in
    if cnt > 0 then
      Some
        {
          id = "TYPO-001";
          severity = Error;
          message = {|ASCII straight quotes (" … ") must be curly quotes|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-001"; run }

let r_typo_002 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.ch, b.ch) with
                | Some '-', Some '-' -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-002";
              severity = Warning;
              message = "Double hyphen -- should be en‑dash –";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s "--" in
        if cnt > 0 then
          Some
            {
              id = "TYPO-002";
              severity = Warning;
              message = "Double hyphen -- should be en‑dash –";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-002"; run }

let r_typo_003 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: c' :: rest -> (
                match (a.ch, b.ch, c'.ch) with
                | Some '-', Some '-', Some '-' -> loop (c + 1) (b :: c' :: rest)
                | _ -> loop c (b :: c' :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-003";
              severity = Warning;
              message = "Triple hyphen --- should be em‑dash —";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s "---" in
        if cnt > 0 then
          Some
            {
              id = "TYPO-003";
              severity = Warning;
              message = "Triple hyphen --- should be em‑dash —";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-003"; run }

let r_typo_004 : rule =
  let run s =
    let cnt = count_substring s "``" + count_substring s "''" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-004";
          severity = Warning;
          message =
            "TeX double back‑tick ``…'' not allowed; use opening curly quotes";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-004"; run }

let r_typo_005 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s "..." in
    if cnt > 0 then
      Some
        {
          id = "TYPO-005";
          severity = Warning;
          message = "Ellipsis typed as three periods ...; use \\dots";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-005"; run }

let r_typo_006 : rule =
  let run s =
    let cnt = count_char s '\t' in
    if cnt > 0 then
      Some
        {
          id = "TYPO-006";
          severity = Error;
          message = "Tab character U+0009 forbidden";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-006"; run }

let r_typo_007 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        (* Count Space tokens that directly precede a Newline token *)
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind) with
                | Space, Newline -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-007";
              severity = Info;
              message = "Trailing spaces at end of line";
              count = cnt;
            }
        else None
    | _ ->
        let _total, matched =
          any_line_pred s (fun line ->
              let len = String.length line in
              len > 0
              &&
              let last = String.unsafe_get line (len - 1) in
              last = ' ' || last = '\t')
        in
        if matched > 0 then
          Some
            {
              id = "TYPO-007";
              severity = Info;
              message = "Trailing spaces at end of line";
              count = matched;
            }
        else None
  in
  { id = "TYPO-007"; run }

let r_typo_008 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let cnt =
          (* Count sequences of 3 consecutive newlines *)
          let n = String.length s in
          let rec loop i acc =
            if i + 2 >= n then acc
            else if
              String.unsafe_get s i = '\n'
              && String.unsafe_get s (i + 1) = '\n'
              && String.unsafe_get s (i + 2) = '\n'
            then loop (i + 3) (acc + 1)
            else loop (i + 1) acc
          in
          loop 0 0
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-008";
              severity = Info;
              message = "Multiple consecutive blank lines (> 2) in source";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s "\n\n\n" in
        if cnt > 0 then
          Some
            {
              id = "TYPO-008";
              severity = Info;
              message = "Multiple consecutive blank lines (> 2) in source";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-008"; run }

let r_typo_009 : rule =
  let run s =
    let starts =
      if String.length s > 0 && String.unsafe_get s 0 = '~' then 1 else 0
    in
    let cnt = starts + count_substring s "\n~" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-009";
          severity = Warning;
          message = "Non‑breaking space ~ used incorrectly at line start";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-009"; run }

let r_typo_010 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let is_punct = function
          | Some (',' | '.' | ';' | ':' | '?' | '!') -> true
          | _ -> false
        in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind, b.ch) with
                | Space, Symbol, ch when is_punct ch -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-010";
              severity = Info;
              message = "Space before punctuation , . ; : ? !";
              count = cnt;
            }
        else None
    | _ ->
        let combos = [ " ,"; " ."; " ;"; " :"; " ?"; " !" ] in
        let cnt =
          List.fold_left (fun acc sub -> acc + count_substring s sub) 0 combos
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-010";
              severity = Info;
              message = "Space before punctuation , . ; : ? !";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-010"; run }

(* TYPO-011: Missing thin space before differential d in integrals *)
let r_typo_011 : rule =
  let re = Str.regexp {|\\int[^}]*[^\\,]d[a-z]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-011";
          severity = Info;
          message =
            {|Missing thin space (\,) before differential d in integrals|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-011"; run }

(* TYPO-012: Straight apostrophe used for minutes/feet *)
let r_typo_012 : rule =
  let re = Str.regexp {|[0-9]'|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-012";
          severity = Warning;
          message =
            {|Straight apostrophe ' used for minutes/feet; use ^\prime or ′|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-012"; run }

(* TYPO-013: ASCII back-tick used as opening quote *)
let r_typo_013 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    for i = 0 to n - 1 do
      if s.[i] = '`' then
        (* Only flag single backtick, not `` (TeX opening quote) *)
        let is_double =
          (i + 1 < n && s.[i + 1] = '`') || (i > 0 && s.[i - 1] = '`')
        in
        if not is_double then incr cnt
    done;
    if !cnt > 0 then
      Some
        {
          id = "TYPO-013";
          severity = Warning;
          message = {|ASCII back‑tick ` used as opening quote|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-013"; run }

(* TYPO-014: Space before percent sign — relocated from old TYPO-028 *)
let r_typo_014 : rule =
  let run s =
    let cnt = count_substring s " %" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-014";
          severity = Info;
          message = {|Space before percent sign \%|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-014"; run }

(* TYPO-015: Double \% in source; likely stray percent *)
let r_typo_015 : rule =
  let run s =
    let cnt = count_substring s "\\%\\%" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-015";
          severity = Warning;
          message = {|Double \% in source; likely stray percent|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-015"; run }

(* TYPO-016: Non-breaking space ~ missing before \cite / \ref *)
let r_typo_016 : rule =
  let re = Str.regexp {| \\\(cite\|ref\)[^a-zA-Z]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    let cnt = !cnt in
    if cnt > 0 then
      Some
        {
          id = "TYPO-016";
          severity = Info;
          message = {|Non‑breaking space ~ missing before \cite / \ref|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-016"; run }

(* TYPO-017: TeX accent commands in text; prefer UTF-8 *)
let r_typo_017 : rule =
  let re = Str.regexp {|\\['^`"~=.][{][a-zA-Z][}]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-017";
          severity = Info;
          message = {|TeX accent commands (\'{e}) in text; prefer UTF‑8 é|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-017"; run }

(* TYPO-018: Multiple consecutive spaces — relocated from old TYPO-011 *)
let r_typo_018 : rule =
  let run s =
    let cnt = count_substring s "  " in
    if cnt > 0 then
      Some
        {
          id = "TYPO-018";
          severity = Info;
          message = "Multiple consecutive spaces in text";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-018"; run }

(* ── DEFERRED NLP STUBS ──────────────────────────────────────────────
   TYPO-019, -020, -030, -031 require NLP analysis and return None
   unconditionally. They are included in rules_pilot for API completeness but
   are excluded from rules_vpd_catalogue and have no VPD pattern entries or Coq
   soundness proofs. Status: blocked on NLP integration (tracked in
   WEEKLY_STATUS.md).
   ──────────────────────────────────────────────────────────────────── *)

(* TYPO-019: Comma splice detected — DEFERRED: requires NLP analysis *)
let r_typo_019 : rule =
  let run _s = None in
  { id = "TYPO-019"; run }

(* TYPO-020: Sentence without ending punctuation — DEFERRED: requires NLP *)
let r_typo_020 : rule =
  let run _s = None in
  { id = "TYPO-020"; run }

(* TYPO-021: Capital letter after ellipsis without space *)
let r_typo_021 : rule =
  let re = Str.regexp {|\(\.\.\.\|…\)[A-Z]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-021";
          severity = Info;
          message = "Capital letter after ellipsis without space";
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-021"; run }

(* TYPO-022: Space before closing punctuation — relocated from old TYPO-012 *)
let r_typo_022 : rule =
  let run s =
    let combos = [ " )"; " ]"; " }" ] in
    let cnt =
      List.fold_left (fun acc sub -> acc + count_substring s sub) 0 combos
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-022";
          severity = Info;
          message = "Space before closing punctuation ) ] }";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-022"; run }

(* TYPO-023: ASCII ampersand & outside tabular env; use \& *)
let r_typo_023 : rule =
  let tabular_re =
    Str.regexp
      {|\\begin{tabular\|\\begin{array\|\\begin{align\|\\begin{tabularx\|\\begin{longtable|}
  in
  let end_re =
    Str.regexp
      {|\\end{tabular\|\\end{array\|\\end{align\|\\end{tabularx\|\\end{longtable|}
  in
  let run s =
    (* Strip out tabular/array/align environments *)
    let stripped = ref s in
    (try
       while true do
         let start_pos = Str.search_forward tabular_re !stripped 0 in
         try
           let end_pos = Str.search_forward end_re !stripped start_pos in
           let end_pos =
             try
               let _ = Str.search_forward (Str.regexp "}") !stripped end_pos in
               Str.match_end ()
             with Not_found -> end_pos + 10
           in
           let before = String.sub !stripped 0 start_pos in
           let after =
             if end_pos < String.length !stripped then
               String.sub !stripped end_pos (String.length !stripped - end_pos)
             else ""
           in
           stripped := before ^ after
         with Not_found ->
           (* No matching end — strip from start to end of string *)
           stripped := String.sub !stripped 0 start_pos
       done
     with Not_found -> ());
    (* Count bare & (not \&) in stripped text *)
    let n = String.length !stripped in
    let cnt = ref 0 in
    for i = 0 to n - 1 do
      if !stripped.[i] = '&' && not (i > 0 && !stripped.[i - 1] = '\\') then
        incr cnt
    done;
    if !cnt > 0 then
      Some
        {
          id = "TYPO-023";
          severity = Error;
          message = {|ASCII ampersand & outside tabular env; use \&|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-023"; run }

(* TYPO-024: Dangling dash at line end *)
let r_typo_024 : rule =
  let re = Str.regexp "-+[ \t]*$" in
  let run s =
    let lines = String.split_on_char '\n' s in
    let cnt =
      List.fold_left
        (fun acc line ->
          try
            let _ = Str.search_forward re line 0 in
            acc + 1
          with Not_found -> acc)
        0 lines
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-024";
          severity = Info;
          message = "Dangling dash at line end";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-024"; run }

(* TYPO-025: Space before en-dash in number range *)
let r_typo_025 : rule =
  let re = Str.regexp {|[0-9] +\(–\|--\)[0-9]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-025";
          severity = Warning;
          message = {|Space before en‑dash in number range|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-025"; run }

(* TYPO-026: Wrong dash in page range — should use -- *)
let r_typo_026 : rule =
  let re = Str.regexp {|[0-9]–[0-9]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-026";
          severity = Warning;
          message = {|Wrong dash in page range – should use --|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-026"; run }

(* TYPO-027: Multiple exclamation marks — relocated from old TYPO-016 *)
let r_typo_027 : rule =
  let run s =
    let cnt = count_substring s "!!" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-027";
          severity = Info;
          message = {|Multiple exclamation marks ‼|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-027"; run }

(* TYPO-028: Use of $$ display math delimiter *)
let r_typo_028 : rule =
  let run s =
    let cnt = count_substring s "$$" in
    (* Each pair of $$ counts as one — divide by 2 *)
    let cnt = cnt / 2 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-028";
          severity = Error;
          message = {|Use of ``$$'' display math delimiter|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-028"; run }

(* TYPO-029: Non-breaking space after \ref missing *)
let r_typo_029 : rule =
  let re = Str.regexp {|\\ref{[^}]*} [a-zA-Z]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-029";
          severity = Info;
          message = {|Non‑breaking space after \ref missing|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-029"; run }

(* TYPO-030: UK spelling inconsistency — DEFERRED: requires NLP (see comment
   block before TYPO-019 above) *)
let r_typo_030 : rule =
  let run _s = None in
  { id = "TYPO-030"; run }

(* TYPO-031: American punctuation placement inside quotes — DEFERRED: requires
   NLP (see comment block before TYPO-019 above) *)
let r_typo_031 : rule =
  let run _s = None in
  { id = "TYPO-031"; run }

(* TYPO-032: Comma before \cite *)
let r_typo_032 : rule =
  let re = Str.regexp {|,[ ]*\\cite|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TYPO-032";
          severity = Warning;
          message = {|Comma before \cite|};
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-032"; run }

(* TYPO-033: Abbreviation et.al without space *)
let r_typo_033 : rule =
  let run s =
    let cnt = count_substring s "et.al" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-033";
          severity = Warning;
          message = "Abbreviation et.al without space";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-033"; run }

let rules_pilot : rule list =
  [
    r_typo_001;
    r_typo_002;
    r_typo_003;
    r_typo_004;
    r_typo_005;
    r_typo_006;
    r_typo_007;
    r_typo_008;
    r_typo_009;
    r_typo_010;
    r_typo_011;
    r_typo_012;
    r_typo_013;
    r_typo_014;
    r_typo_015;
    r_typo_016;
    r_typo_017;
    r_typo_018;
    r_typo_019;
    r_typo_020;
    r_typo_021;
    r_typo_022;
    r_typo_023;
    r_typo_024;
    r_typo_025;
    r_typo_026;
    r_typo_027;
    r_typo_028;
    r_typo_029;
    r_typo_030;
    r_typo_031;
    r_typo_032;
    r_typo_033;
  ]

(* BEGIN VPD-generated validators v0.4.0 — DO NOT EDIT BELOW THIS LINE *)
(* 80 VPD-catalogue rules: 56 TYPO + 24 ENC Pattern definitions in
   specs/rules/vpd_patterns.json Soundness proofs in proofs/RegexFamily.v *)

(* Spurious space before footnote command \footnote *)
let r_typo_034 : rule =
  let run s =
    let cnt = count_substring s " \\footnote" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-034";
          severity = Info;
          message = {|Spurious space before footnote command \footnote|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-034"; run }

(* French punctuation requires NBSP before ; : ! ? *)
let r_typo_035 : rule =
  let run s =
    let cnt =
      count_substring s " ;"
      + count_substring s " :"
      + count_substring s " !"
      + count_substring s " ?"
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-035";
          severity = Warning;
          message = "French punctuation requires NBSP before ; : ! ?";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-035"; run }

(* Suspicious consecutive capitalised words (shouting) *)
let r_typo_036 : rule =
  let re =
    Str.regexp
      {|\(^\|[ \t({]\)[A-Z][A-Z]+ [A-Z][A-Z]+ [A-Z][A-Z]+\($\|[ \t.,;:!?)}]\)|}
  in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        loop (Str.match_end ()) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-036";
          severity = Info;
          message = "Suspicious consecutive capitalised words (shouting)";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-036"; run }

(* Space before comma *)
let r_typo_037 : rule =
  let run s =
    let cnt = count_substring s " ," in
    if cnt > 0 then
      Some
        {
          id = "TYPO-037";
          severity = Info;
          message = "Space before comma";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-037"; run }

(* E-mail address not in \href *)
let r_typo_038 : rule =
  let re = Str.regexp "[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]+" in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        loop (Str.match_end ()) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-038";
          severity = Info;
          message = {|E‑mail address not in \href|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-038"; run }

(* Incorrect spacing around \ldots *)
let r_typo_041 : rule =
  let run s =
    let cnt =
      count_substring s ".\\ldots"
      + count_substring s "\\ldots."
      + count_substring s ",\\ldots"
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-041";
          severity = Info;
          message = {|Incorrect spacing around \ldots|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-041"; run }

(* Multiple consecutive question marks ?? *)
let r_typo_042 : rule =
  let run s =
    let cnt = count_substring s "??" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-042";
          severity = Info;
          message = "Multiple consecutive question marks ??";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-042"; run }

(* Smart quotes inside verbatim detected *)
let r_typo_043 : rule =
  let run s =
    let cnt =
      count_substring s "\xe2\x80\x9c"
      + count_substring s "\xe2\x80\x9d"
      + count_substring s "\xe2\x80\x98"
      + count_substring s "\xe2\x80\x99"
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-043";
          severity = Warning;
          message = "Smart quotes inside verbatim detected";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-043"; run }

(* TYPO-044: Acronym not defined on first use — scan for uppercase sequences of
   2+ letters (e.g., "API", "NASA") and check whether their first occurrence in
   the document is accompanied by a parenthetical expansion like "Application
   Programming Interface (API)" or "API (Application Programming Interface)". If
   not, we flag it as undefined on first use. We exclude common well-known
   abbreviations that don't need expansion: e.g., USA, UK, PDF, etc. and LaTeX
   command names. *)
let r_typo_044 : rule =
  let well_known =
    [
      "OK";
      "USA";
      "UK";
      "EU";
      "UN";
      "NATO";
      "NASA";
      "CEO";
      "PhD";
      "Dr";
      "Mr";
      "Mrs";
      "Ms";
      "Jr";
      "Sr";
      "II";
      "III";
      "IV";
      "AM";
      "PM";
      "BC";
      "AD";
      "PDF";
      "HTML";
      "URL";
      "USB";
      "CPU";
      "GPU";
      "RAM";
      "ROM";
      "DVD";
      "CD";
      "TV";
      "FM";
      "AC";
      "DC";
      "ID";
      "IP";
      "OS";
      "PC";
      "AI";
      "ML";
      "API";
      "FAQ";
      "DIY";
      "GPS";
      "VPN";
      "PhD";
      "MBA";
      "MD";
      "IEEE";
      "ACM";
      "ISO";
      "RFC";
      "HTTP";
      "HTTPS";
      "SSH";
      "FTP";
      "DNS";
      "TCP";
      "UDP";
      "XML";
      "JSON";
      "YAML";
      "CSV";
      "SQL";
      "CSS";
      "RSS";
      "SMTP";
      "IMAP";
      "POP";
      "SSL";
      "TLS";
      "AES";
      "RSA";
      "SHA";
      "UNIX";
      "GNU";
      "BSD";
      "MIT";
      "GPL";
      "ASCII";
      "UTF";
      "NFC";
      "NFKC";
    ]
  in
  let re = Str.regexp {|\([A-Z][A-Z0-9]+\)|} in
  let is_alnum c =
    (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
  in
  let run s =
    let s_text = strip_math_segments s in
    let n_text = String.length s_text in
    (* Collect all acronym occurrences with their positions *)
    let first_use = Hashtbl.create 32 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re s_text !i in
         let acr = Str.matched_group 1 s_text in
         let match_end = Str.match_end () in
         (* Manual word-boundary check *)
         let before_ok = pos = 0 || not (is_alnum s_text.[pos - 1]) in
         let after_ok =
           match_end >= n_text || not (is_alnum s_text.[match_end])
         in
         if before_ok && after_ok then
           if not (Hashtbl.mem first_use acr) then Hashtbl.add first_use acr pos;
         i := match_end
       done
     with Not_found -> ());
    (* For each first-use acronym, check if it's well-known or has a nearby
       parenthetical definition *)
    let cnt = ref 0 in
    Hashtbl.iter
      (fun acr pos ->
        if not (List.mem acr well_known) then
          (* Look for "(ACR)" or "ACR (" within 200 chars before/after *)
          let window_start = max 0 (pos - 200) in
          let window_end =
            min (String.length s_text) (pos + String.length acr + 200)
          in
          let window =
            String.sub s_text window_start (window_end - window_start)
          in
          let has_paren_def =
            (* "(ACR)" pattern *)
            let pat1 = "(" ^ acr ^ ")" in
            (* "ACR (" pattern — definition after acronym *)
            let pat2 = acr ^ " (" in
            count_substring window pat1 > 0 || count_substring window pat2 > 0
          in
          if not has_paren_def then incr cnt)
      first_use;
    if !cnt > 0 then
      Some
        {
          id = "TYPO-044";
          severity = Info;
          message = "Acronym not defined on first use";
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-044"; run }

(* En-dash used as minus sign in text *)
let r_typo_048 : rule =
  let run s =
    let cnt =
      (fun s ->
        let s = strip_math_segments s in
        Unicode.count_en_dash s)
        s
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-048";
          severity = Info;
          message = "En‑dash used as minus sign in text";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-048"; run }

(* Figure space U+2009 used instead of \thinspace macro *)
let r_typo_051 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x80\x89" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-051";
          severity = Warning;
          message = {|Figure space U+2009 used instead of \thinspace macro|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-051"; run }

(* Unescaped < or > in text *)
let r_typo_052 : rule =
  let run s =
    let cnt =
      (fun s ->
        let s = strip_math_segments s in
        count_char s '<' + count_char s '>')
        s
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-052";
          severity = Warning;
          message = "Unescaped < or > in text; use \\textless / \\textgreater";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-052"; run }

(* Unicode leader dots U+22EF forbidden *)
let r_typo_053 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x8b\xaf" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-053";
          severity = Warning;
          message = {|Unicode ⋯ (U+22EF) leader forbidden; use \dots instead|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-053"; run }

(* Hair-space required after en-dash in word-word ranges *)
let r_typo_054 : rule =
  let re = Str.regexp "[a-zA-Z]\xe2\x80\x93[a-zA-Z]" in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        loop (Str.match_end ()) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-054";
          severity = Info;
          message = "Hair‑space required after en‑dash in word–word ranges";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-054"; run }

(* Consecutive thin-spaces prohibited *)
let r_typo_055 : rule =
  let run s =
    let cnt = count_substring s "\\,\\," in
    if cnt > 0 then
      Some
        {
          id = "TYPO-055";
          severity = Info;
          message = {|Consecutive thin‑spaces (\,\,) prohibited; collapse|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-055"; run }

(* Missing thin-space before degree symbol *)
let r_typo_057 : rule =
  let re = Str.regexp "[0-9]\xc2\xb0" in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        loop (Str.match_end ()) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-057";
          severity = Info;
          message = {|Missing thin‑space before °C/°F or \si{\celsius}|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-057"; run }

(* Unicode multiplication sign in text *)
let r_typo_061 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s "\xc3\x97" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-061";
          severity = Info;
          message = {|Unicode × (U+00D7) in text; prefer \times via math mode|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-061"; run }

(* Non-breaking hyphen U+2011 found *)
let r_typo_063 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x80\x91" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-063";
          severity = Info;
          message = "Non‑breaking hyphen U+2011 found inside URL";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-063"; run }

(* URL split across lines without \url{} *)
let r_typo_039 : rule =
  let re = Str.regexp "https?://[^ \t\n}]+" in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        loop (Str.match_end ()) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-039";
          severity = Info;
          message = "URL split across lines without \\url{}";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-039"; run }

(* Inline math $...$ exceeds 80 characters *)
let r_typo_040 : rule =
  let re = Str.regexp "\\$\\([^$]+\\)\\$" in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        let inner = Str.matched_group 1 s in
        let acc' = if String.length inner > 80 then acc + 1 else acc in
        loop (Str.match_end ()) acc'
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-040";
          severity = Info;
          message = "Math in text mode $…$ exceeds 80 characters";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-040"; run }

(* Non-ASCII punctuation in math mode *)
let r_typo_045 : rule =
  let run s =
    let cnt =
      (fun s ->
        let n = String.length s in
        let rec scan i inside acc =
          if i >= n then acc
          else
            let c = Char.code s.[i] in
            if c = 0x24 then scan (i + 1) (not inside) acc
            else if inside && c >= 0x80 then scan (i + 1) inside (acc + 1)
            else scan (i + 1) inside acc
        in
        scan 0 false 0)
        s
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-045";
          severity = Warning;
          message = "Non‑ASCII punctuation in math mode (‘ ’ “ ”)";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-045"; run }

(* Use of \begin{math} instead of $...$ *)
let r_typo_046 : rule =
  let run s =
    let cnt =
      count_substring s "\\begin{math}" + count_substring s "\\end{math}"
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-046";
          severity = Info;
          message = "Use of $begin:math:text$ … $end:math:text$ instead of $…$";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-046"; run }

(* Starred \section* used where numbered section expected *)
let r_typo_047 : rule =
  let run s =
    let cnt = count_substring s "\\section*" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-047";
          severity = Info;
          message = "Starred \\section* used where numbered section expected";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-047"; run }

(* Space after opening quote *)
let r_typo_049 : rule =
  let run s =
    let cnt =
      count_substring s "\xe2\x80\x9c " + count_substring s "\xe2\x80\x98 "
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-049";
          severity = Info;
          message = "Space after opening quote";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-049"; run }

(* Legacy TeX accent command found *)
let r_typo_056 : rule =
  let re = Str.regexp "\\\\['^`\"~=.][{][a-zA-Z][}]" in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        loop (Str.match_end ()) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-056";
          severity = Warning;
          message = "Legacy TeX accents present despite UTF‑8 input";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-056"; run }

(* Greek homograph letter found in Latin text *)
let r_typo_058 : rule =
  let run s =
    let cnt =
      count_substring s "\xce\xb1"
      + count_substring s "\xce\xb5"
      + count_substring s "\xce\xb9"
      + count_substring s "\xce\xbf"
      + count_substring s "\xcf\x81"
      + count_substring s "\xcf\x82"
      + count_substring s "\xcf\x85"
    in
    if cnt > 0 then
      Some
        {
          id = "TYPO-058";
          severity = Warning;
          message = "Greek homograph letters used in Latin words (ϲ,ɑ,ᴦ…)";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-058"; run }

(* TYPO-060: Smart quotes inside lstlisting/verbatim environments *)
let r_typo_060 : rule =
  let run s =
    (* Extract content within \begin{lstlisting}...\end{lstlisting} and
       \begin{verbatim}...\end{verbatim}, then scan for curly quotes *)
    let curly_in_env env =
      let open_tag = "\\begin{" ^ env ^ "}" in
      let close_tag = "\\end{" ^ env ^ "}" in
      let olen = String.length open_tag in
      let rec loop i acc =
        match
          try Some (Str.search_forward (Str.regexp_string open_tag) s i)
          with Not_found -> None
        with
        | None -> acc
        | Some start -> (
            let content_start = start + olen in
            match
              try
                Some
                  (Str.search_forward
                     (Str.regexp_string close_tag)
                     s content_start)
              with Not_found -> None
            with
            | None -> acc
            | Some end_pos ->
                let block =
                  String.sub s content_start (end_pos - content_start)
                in
                let cnt =
                  count_substring block "\xe2\x80\x9c"
                  + count_substring block "\xe2\x80\x9d"
                  + count_substring block "\xe2\x80\x98"
                  + count_substring block "\xe2\x80\x99"
                in
                loop (end_pos + String.length close_tag) (acc + cnt))
      in
      loop 0 0
    in
    let cnt = curly_in_env "lstlisting" + curly_in_env "verbatim" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-060";
          severity = Warning;
          message =
            {|Smart quotes present inside \lstlisting / verbatim environments|};
          count = cnt;
        }
    else None
  in
  { id = "TYPO-060"; run }

let rules_vpd_gen : rule list =
  [
    r_typo_034;
    r_typo_035;
    r_typo_036;
    r_typo_037;
    r_typo_038;
    r_typo_039;
    r_typo_040;
    r_typo_041;
    r_typo_042;
    r_typo_043;
    r_typo_044;
    r_typo_045;
    r_typo_046;
    r_typo_047;
    r_typo_048;
    r_typo_049;
    r_typo_051;
    r_typo_052;
    r_typo_053;
    r_typo_054;
    r_typo_055;
    r_typo_056;
    r_typo_057;
    r_typo_058;
    r_typo_060;
    r_typo_061;
    r_typo_063;
  ]

(* END VPD-generated validators *)

(* ── ENC rules: encoding / Unicode character detection ─────────────── *)

(* ENC-007: Zero-width space U+200B *)
let r_enc_007 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x80\x8b" in
    if cnt > 0 then
      Some
        {
          id = "ENC-007";
          severity = Warning;
          message = "Zero‑width space U+200B present";
          count = cnt;
        }
    else None
  in
  { id = "ENC-007"; run }

(* ENC-012: C1 control characters U+0080-009F *)
let r_enc_012 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 1 do
      if
        Char.code s.[!i] = 0xC2
        && Char.code s.[!i + 1] >= 0x80
        && Char.code s.[!i + 1] <= 0x9F
      then (
        incr cnt;
        i := !i + 2)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-012";
          severity = Error;
          message = "C1 control characters U+0080–009F present";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-012"; run }

(* ENC-017: Soft hyphen U+00AD *)
let r_enc_017 : rule =
  let run s =
    let cnt = count_substring s "\xc2\xad" in
    if cnt > 0 then
      Some
        {
          id = "ENC-017";
          severity = Warning;
          message = "Soft hyphen U+00AD found in source";
          count = cnt;
        }
    else None
  in
  { id = "ENC-017"; run }

(* ENC-020: Invisible formatting marks U+200E (LRM) / U+200F (RLM) *)
let r_enc_020 : rule =
  let run s =
    let cnt =
      count_substring s "\xe2\x80\x8e" + count_substring s "\xe2\x80\x8f"
    in
    if cnt > 0 then
      Some
        {
          id = "ENC-020";
          severity = Warning;
          message = "Invisible formatting mark U+200E/U+200F present";
          count = cnt;
        }
    else None
  in
  { id = "ENC-020"; run }

(* ENC-021: Word joiner U+2060 *)
let r_enc_021 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x81\xa0" in
    if cnt > 0 then
      Some
        {
          id = "ENC-021";
          severity = Warning;
          message = "WORD JOINER U+2060 present";
          count = cnt;
        }
    else None
  in
  { id = "ENC-021"; run }

(* ENC-022: Interlinear annotation chars U+FFF9-FFFB *)
let r_enc_022 : rule =
  let run s =
    let cnt =
      count_substring s "\xef\xbf\xb9"
      + count_substring s "\xef\xbf\xba"
      + count_substring s "\xef\xbf\xbb"
    in
    if cnt > 0 then
      Some
        {
          id = "ENC-022";
          severity = Warning;
          message = "Interlinear annotation chars U+FFF9–FFFB detected";
          count = cnt;
        }
    else None
  in
  { id = "ENC-022"; run }

(* ENC-023: Narrow no-break space U+202F *)
let r_enc_023 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x80\xaf" in
    if cnt > 0 then
      Some
        {
          id = "ENC-023";
          severity = Warning;
          message = "NARROW NB‑SPACE U+202F outside French context";
          count = cnt;
        }
    else None
  in
  { id = "ENC-023"; run }

(* ENC-024: Bidirectional embeddings U+202A-U+202E *)
let r_enc_024 : rule =
  let run s =
    let cnt =
      count_substring s "\xe2\x80\xaa"
      + count_substring s "\xe2\x80\xab"
      + count_substring s "\xe2\x80\xac"
      + count_substring s "\xe2\x80\xad"
      + count_substring s "\xe2\x80\xae"
    in
    if cnt > 0 then
      Some
        {
          id = "ENC-024";
          severity = Warning;
          message = "Bidirectional embeddings U+202A–U+202E present";
          count = cnt;
        }
    else None
  in
  { id = "ENC-024"; run }

(* ENC-001: Non-UTF-8 byte sequence detected *)
let r_enc_001 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let b = Char.code s.[!i] in
      if b <= 0x7F then incr i (* ASCII *)
      else if b land 0xE0 = 0xC0 then
        if
          (* 2-byte: 110xxxxx 10xxxxxx *)
          !i + 1 < n && Char.code s.[!i + 1] land 0xC0 = 0x80
        then i := !i + 2
        else (
          incr cnt;
          incr i)
      else if b land 0xF0 = 0xE0 then
        if
          (* 3-byte: 1110xxxx 10xxxxxx 10xxxxxx *)
          !i + 2 < n
          && Char.code s.[!i + 1] land 0xC0 = 0x80
          && Char.code s.[!i + 2] land 0xC0 = 0x80
        then i := !i + 3
        else (
          incr cnt;
          incr i)
      else if b land 0xF8 = 0xF0 then
        if
          (* 4-byte: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx *)
          !i + 3 < n
          && Char.code s.[!i + 1] land 0xC0 = 0x80
          && Char.code s.[!i + 2] land 0xC0 = 0x80
          && Char.code s.[!i + 3] land 0xC0 = 0x80
        then i := !i + 4
        else (
          incr cnt;
          incr i)
      else (
        (* Invalid leading byte *)
        incr cnt;
        incr i)
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-001";
          severity = Error;
          message = "Non‑UTF‑8 byte sequence detected";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-001"; run }

(* ENC-002: BOM U+FEFF present in middle of file *)
let r_enc_002 : rule =
  let run s =
    let bom = "\xef\xbb\xbf" in
    let total = count_substring s bom in
    let at_start = String.length s >= 3 && String.sub s 0 3 = bom in
    let interior = if at_start then total - 1 else total in
    if interior > 0 then
      Some
        {
          id = "ENC-002";
          severity = Error;
          message = "Byte‑order mark U+FEFF present in middle of file";
          count = interior;
        }
    else None
  in
  { id = "ENC-002"; run }

(* ENC-003: LATIN-1 smart quotes detected (bare high bytes 0x91-0x94) *)
let r_enc_003 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let b = Char.code s.[!i] in
      if b = 0x91 || b = 0x92 || b = 0x93 || b = 0x94 then (
        (* These bare bytes are LATIN-1/Windows-1252 smart quotes *)
        incr cnt;
        incr i)
      else if b >= 0xC0 && !i + 1 < n then
        (* Skip valid UTF-8 multi-byte sequences *)
        if b land 0xE0 = 0xC0 then i := !i + 2
        else if b land 0xF0 = 0xE0 then i := !i + 3
        else if b land 0xF8 = 0xF0 then i := !i + 4
        else incr i
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-003";
          severity = Warning;
          message = "LATIN‑1 smart quotes detected";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-003"; run }

(* ENC-004: Windows-1252 characters outside UTF-8 *)
let r_enc_004 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let b = Char.code s.[!i] in
      if b >= 0x80 && b <= 0x9F then (
        (* Bare C1 range bytes that are Windows-1252 characters *)
        incr cnt;
        incr i)
      else if b >= 0xC0 && !i + 1 < n then
        if b land 0xE0 = 0xC0 then i := !i + 2
        else if b land 0xF0 = 0xE0 then i := !i + 3
        else if b land 0xF8 = 0xF0 then i := !i + 4
        else incr i
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-004";
          severity = Warning;
          message = "Windows‑1252 characters (– — …) outside UTF‑8";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-004"; run }

(* ENC-013: Mixed CRLF and LF line endings *)
let r_enc_013 : rule =
  let run s =
    let n = String.length s in
    let has_crlf = ref false in
    let has_bare_lf = ref false in
    let i = ref 0 in
    while !i < n do
      if s.[!i] = '\r' && !i + 1 < n && s.[!i + 1] = '\n' then (
        has_crlf := true;
        i := !i + 2)
      else if s.[!i] = '\n' then (
        has_bare_lf := true;
        incr i)
      else incr i
    done;
    if !has_crlf && !has_bare_lf then
      Some
        {
          id = "ENC-013";
          severity = Info;
          message = "Mixed CRLF and LF line endings";
          count = 1;
        }
    else None
  in
  { id = "ENC-013"; run }

(* ENC-014: UTF-16 byte-order mark present *)
let r_enc_014 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    if n >= 2 then (
      (* UTF-16 LE BOM: FF FE *)
      if Char.code s.[0] = 0xFF && Char.code s.[1] = 0xFE then incr cnt;
      (* UTF-16 BE BOM: FE FF *)
      if Char.code s.[0] = 0xFE && Char.code s.[1] = 0xFF then incr cnt);
    if !cnt > 0 then
      Some
        {
          id = "ENC-014";
          severity = Error;
          message = "UTF‑16 byte‑order mark present";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-014"; run }

(* ENC-008: Private-use codepoint U+E000-F8FF detected *)
let r_enc_008 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let b0 = Char.code s.[!i] in
      if b0 = 0xEE && !i + 2 < n then (
        (* U+E000-EFFF: EE 80 80 — EE BF BF *)
        incr cnt;
        i := !i + 3)
      else if b0 = 0xEF && !i + 2 < n then
        let b1 = Char.code s.[!i + 1] in
        if b1 <= 0xA3 then (
          (* U+F000-F8FF: EF 80 80 — EF A3 BF *)
          incr cnt;
          i := !i + 3)
        else i := !i + 1
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-008";
          severity = Warning;
          message = "Private‑use codepoint detected";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-008"; run }

(* ENC-009: Unpaired surrogate code unit U+D800-DFFF in UTF-8 *)
let r_enc_009 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      let b0 = Char.code s.[!i] in
      if b0 = 0xED then
        let b1 = Char.code s.[!i + 1] in
        if b1 >= 0xA0 && b1 <= 0xBF then (
          (* ED A0 80 — ED BF BF = U+D800-DFFF *)
          incr cnt;
          i := !i + 3)
        else i := !i + 1
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-009";
          severity = Error;
          message = "Unpaired surrogate code unit";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-009"; run }

(* ENC-010: Non-canonical NFC form — detect multi-codepoint sequences that
   should be NFC-normalised. We check for the most common cases: combining acute
   (CC 81), combining grave (CC 80), combining diaeresis (CC 88), combining
   tilde (CC 83), combining circumflex (CC 82), combining cedilla (CC A7)
   immediately following an ASCII letter. These sequences have precomposed NFC
   equivalents and should not appear in well-formed LaTeX. *)
let r_enc_010 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 1 do
      let b0 = Char.code s.[!i] in
      let b1 = Char.code s.[!i + 1] in
      (* ASCII letter followed by CC xx (combining diacritical marks
         U+0300-U+036F encoded as CC 80 .. CD AF) *)
      if
        ((b0 >= 0x41 && b0 <= 0x5A) || (b0 >= 0x61 && b0 <= 0x7A))
        && b1 = 0xCC
        && !i + 2 < n
      then
        let b2 = Char.code s.[!i + 2] in
        if b2 >= 0x80 && b2 <= 0xAF then (
          incr cnt;
          i := !i + 3)
        else i := !i + 1
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-010";
          severity = Info;
          message = "Non‑canonical NFC form";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-010"; run }

(* ENC-011: Byte sequence resembles MacRoman encoding — detect byte sequences
   that are valid MacRoman but invalid or unusual UTF-8. Common MacRoman
   artifacts: 0x8E (e-acute), 0x8A (a-umlaut), 0x9C (u-umlaut), 0x85
   (c-cedilla), 0x92 (right-quote in Windows), 0xD2/0xD3 (smart quotes). We
   detect isolated high bytes (0x80-0x9F) that are NOT valid UTF-8 lead bytes —
   in valid UTF-8, 0x80-0xBF are only continuation bytes and 0xC0-0xC1 are
   overlong. Isolated bytes in 0x80-0x9F preceded and followed by ASCII suggest
   MacRoman or CP1252 encoding. *)
let r_enc_011 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    for i = 0 to n - 1 do
      let c = Char.code s.[i] in
      if c >= 0x80 && c <= 0x9F then
        (* Check if this byte is part of a valid UTF-8 multi-byte sequence by
           looking back up to 3 positions for a UTF-8 lead byte that would
           encompass this position. In valid UTF-8, bytes 0x80-0x9F only appear
           as continuation bytes following a lead byte. *)
        let is_valid_utf8 =
          let rec check_back offset =
            if offset > 3 || i - offset < 0 then false
            else
              let p = Char.code s.[i - offset] in
              if p >= 0xC2 && p <= 0xDF then offset = 1
              else if p >= 0xE0 && p <= 0xEF then offset >= 1 && offset <= 2
              else if p >= 0xF0 && p <= 0xF4 then offset >= 1 && offset <= 3
              else if p >= 0x80 && p <= 0xBF then check_back (offset + 1)
              else false
          in
          check_back 1
        in
        if not is_valid_utf8 then incr cnt
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-011";
          severity = Warning;
          message = "Byte sequence resembles MacRoman encoding";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-011"; run }

(* ENC-015: Non-NFKC homoglyph character — detect characters that have
   NFKC-equivalent ASCII/Latin forms but appear in their compatibility variant.
   Most common cases: - U+00B5 MICRO SIGN (C2 B5) vs U+03BC GREEK SMALL MU (CE
   BC) - U+2126 OHM SIGN (E2 84 A6) vs U+03A9 GREEK CAPITAL OMEGA (CE A9) -
   U+212B ANGSTROM SIGN (E2 84 AB) vs U+00C5 LATIN CAPITAL A WITH RING (C3 85) -
   U+017F LATIN SMALL LONG S (C5 BF) vs 's' We flag the compatibility variants
   that should be normalised. *)
let r_enc_015 : rule =
  let run s =
    (* U+00B5 MICRO SIGN = C2 B5 *)
    let cnt_micro = count_substring s "\xc2\xb5" in
    (* U+2126 OHM SIGN = E2 84 A6 *)
    let cnt_ohm = count_substring s "\xe2\x84\xa6" in
    (* U+212B ANGSTROM SIGN = E2 84 AB *)
    let cnt_angstrom = count_substring s "\xe2\x84\xab" in
    (* U+017F LATIN SMALL LONG S = C5 BF *)
    let cnt_long_s = count_substring s "\xc5\xbf" in
    let cnt = cnt_micro + cnt_ohm + cnt_angstrom + cnt_long_s in
    if cnt > 0 then
      Some
        {
          id = "ENC-015";
          severity = Warning;
          message = "Non‑NFKC homoglyph character (Greek μ vs µ)";
          count = cnt;
        }
    else None
  in
  { id = "ENC-015"; run }

(* ENC-016: Fullwidth digits U+FF10-FF19 (Arabic numeral look-alikes) *)
let r_enc_016 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      let b0 = Char.code s.[!i] in
      let b1 = Char.code s.[!i + 1] in
      let b2 = Char.code s.[!i + 2] in
      if b0 = 0xEF && b1 = 0xBC && b2 >= 0x90 && b2 <= 0x99 then (
        (* EF BC 90 — EF BC 99 = U+FF10-FF19 *)
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-016";
          severity = Warning;
          message = "Arabic numerals replaced by Unicode look‑alikes";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-016"; run }

(* ENC-005: Invalid UTF-8 continuation byte *)
let r_enc_005 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let b0 = Char.code s.[!i] in
      if b0 < 0x80 then incr i
      else if b0 < 0xC0 then (
        (* Unexpected continuation byte *)
        incr cnt;
        incr i)
      else if b0 < 0xE0 then
        if (* 2-byte: need 1 continuation *)
           !i + 1 < n then (
          let b1 = Char.code s.[!i + 1] in
          if b1 < 0x80 || b1 > 0xBF then incr cnt;
          i := !i + 2)
        else (
          incr cnt;
          incr i)
      else if b0 < 0xF0 then
        if (* 3-byte: need 2 continuations *)
           !i + 2 < n then (
          let b1 = Char.code s.[!i + 1] in
          let b2 = Char.code s.[!i + 2] in
          if b1 < 0x80 || b1 > 0xBF || b2 < 0x80 || b2 > 0xBF then incr cnt;
          i := !i + 3)
        else (
          incr cnt;
          incr i)
      else if b0 < 0xF8 then
        if (* 4-byte: need 3 continuations *)
           !i + 3 < n then (
          let b1 = Char.code s.[!i + 1] in
          let b2 = Char.code s.[!i + 2] in
          let b3 = Char.code s.[!i + 3] in
          if
            b1 < 0x80
            || b1 > 0xBF
            || b2 < 0x80
            || b2 > 0xBF
            || b3 < 0x80
            || b3 > 0xBF
          then incr cnt;
          i := !i + 4)
        else (
          incr cnt;
          incr i)
      else (
        incr cnt;
        incr i)
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-005";
          severity = Error;
          message = "Invalid UTF‑8 continuation byte";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-005"; run }

(* ENC-006: Overlong UTF-8 encoding sequence *)
let r_enc_006 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let b0 = Char.code s.[!i] in
      if b0 < 0x80 then incr i
      else if b0 < 0xC0 then incr i (* continuation byte, skip *)
      else if b0 < 0xE0 then (
        (* 2-byte: overlong if b0 = C0 or C1 (encodes U+0000–007F) *)
        if b0 = 0xC0 || b0 = 0xC1 then incr cnt;
        i := !i + 2)
      else if b0 < 0xF0 then (
        (* 3-byte: overlong if b0=E0 and b1 < A0 *)
        (if !i + 2 < n then
           let b1 = Char.code s.[!i + 1] in
           if b0 = 0xE0 && b1 < 0xA0 then incr cnt);
        i := !i + 3)
      else if b0 < 0xF8 then (
        (* 4-byte: overlong if b0=F0 and b1 < 90 *)
        (if !i + 3 < n then
           let b1 = Char.code s.[!i + 1] in
           if b0 = 0xF0 && b1 < 0x90 then incr cnt);
        i := !i + 4)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-006";
          severity = Error;
          message = "Overlong UTF‑8 encoding sequence";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-006"; run }

(* ENC-018: Non-breaking hyphen U+2011 present outside URLs *)
let r_enc_018 : rule =
  let run s =
    (* U+2011 = E2 80 91 *)
    let s_text = strip_math_segments s in
    let n = String.length s_text in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      if
        Char.code s_text.[!i] = 0xE2
        && Char.code s_text.[!i + 1] = 0x80
        && Char.code s_text.[!i + 2] = 0x91
      then (
        (* Check if inside \url{} — look back for \url{ *)
        let in_url = ref false in
        let j = ref (!i - 1) in
        while !j >= 0 && not !in_url do
          if !j + 4 < n && String.sub s_text !j 5 = "\\url{" then in_url := true;
          if s_text.[!j] = '}' then j := -1 (* stop searching *) else decr j
        done;
        if not !in_url then incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-018";
          severity = Info;
          message = "Non‑breaking hyphen U+2011 present outside URLs";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-018"; run }

(* ENC-019: Duplicate combining accents on same base glyph *)
let r_enc_019 : rule =
  let is_combining b0 b1 =
    (* Combining diacritical marks: U+0300–036F = CC 80 – CD AF *)
    (b0 = 0xCC && b1 >= 0x80) || (b0 = 0xCD && b1 <= 0xAF)
  in
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let b0 = Char.code s.[!i] in
      if b0 < 0x80 then (
        (* ASCII base char; check for combining after *)
        let j = ref (!i + 1) in
        let prev_combining = ref (-1, -1) in
        while !j + 1 < n do
          let c0 = Char.code s.[!j] in
          let c1 = Char.code s.[!j + 1] in
          if is_combining c0 c1 then (
            let pc0, pc1 = !prev_combining in
            if pc0 = c0 && pc1 = c1 then incr cnt;
            prev_combining := (c0, c1);
            j := !j + 2)
          else j := n (* exit inner loop *)
        done;
        incr i)
      else if b0 >= 0xC0 && b0 < 0xE0 then (
        (* 2-byte char; check for combining after *)
        let base_end = !i + 2 in
        let j = ref base_end in
        let prev_combining = ref (-1, -1) in
        while !j + 1 < n do
          let c0 = Char.code s.[!j] in
          let c1 = Char.code s.[!j + 1] in
          if is_combining c0 c1 then (
            let pc0, pc1 = !prev_combining in
            if pc0 = c0 && pc1 = c1 then incr cnt;
            prev_combining := (c0, c1);
            j := !j + 2)
          else j := n
        done;
        i := base_end)
      else if b0 >= 0xE0 && b0 < 0xF0 then i := !i + 3
      else if b0 >= 0xF0 then i := !i + 4
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "ENC-019";
          severity = Warning;
          message = "Duplicate combining accents on same base glyph";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-019"; run }

let rules_enc : rule list =
  [
    r_enc_001;
    r_enc_002;
    r_enc_003;
    r_enc_004;
    r_enc_005;
    r_enc_006;
    r_enc_007;
    r_enc_008;
    r_enc_009;
    r_enc_010;
    r_enc_011;
    r_enc_012;
    r_enc_013;
    r_enc_014;
    r_enc_015;
    r_enc_016;
    r_enc_017;
    r_enc_018;
    r_enc_019;
    r_enc_020;
    r_enc_021;
    r_enc_022;
    r_enc_023;
    r_enc_024;
  ]

(* ── CHAR rules: control character detection ───────────────────────── *)

(* CHAR-005: Control characters U+0000-001F present (excluding TAB 0x09, LF
   0x0A, CR 0x0D which are handled by other rules) *)
let r_char_005 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    for i = 0 to n - 1 do
      let c = Char.code s.[i] in
      if
        c <= 0x1F
        && c <> 0x09
        && c <> 0x0A
        && c <> 0x0D
        (* Also exclude 0x07/0x08/0x0C/0x7F — these have their own rules *)
        && c <> 0x07
        && c <> 0x08
        && c <> 0x0C
      then incr cnt
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-005";
          severity = Error;
          message = "Control characters U+0000–001F present";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-005"; run }

(* CHAR-006: Backspace U+0008 *)
let r_char_006 : rule =
  let run s =
    let cnt = count_char s '\x08' in
    if cnt > 0 then
      Some
        {
          id = "CHAR-006";
          severity = Error;
          message = "Backspace U+0008 present";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-006"; run }

(* CHAR-007: Bell/alert U+0007 *)
let r_char_007 : rule =
  let run s =
    let cnt = count_char s '\x07' in
    if cnt > 0 then
      Some
        {
          id = "CHAR-007";
          severity = Error;
          message = "Bell/alert U+0007 present";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-007"; run }

(* CHAR-008: Form feed U+000C *)
let r_char_008 : rule =
  let run s =
    let cnt = count_char s '\x0c' in
    if cnt > 0 then
      Some
        {
          id = "CHAR-008";
          severity = Warning;
          message = "Form feed U+000C present";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-008"; run }

(* CHAR-009: Delete U+007F *)
let r_char_009 : rule =
  let run s =
    let cnt = count_char s '\x7f' in
    if cnt > 0 then
      Some
        {
          id = "CHAR-009";
          severity = Warning;
          message = "Delete U+007F present";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-009"; run }

(* CHAR-013: Bidirectional isolate chars U+2066-U+2069 *)
let r_char_013 : rule =
  let run s =
    let cnt =
      count_substring s "\xe2\x81\xa6"
      + count_substring s "\xe2\x81\xa7"
      + count_substring s "\xe2\x81\xa8"
      + count_substring s "\xe2\x81\xa9"
    in
    if cnt > 0 then
      Some
        {
          id = "CHAR-013";
          severity = Warning;
          message = "Bidirectional isolate chars U+2066–U+2069 present";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-013"; run }

(* CHAR-014: Unicode replacement character U+FFFD *)
let r_char_014 : rule =
  let run s =
    let cnt = count_substring s "\xef\xbf\xbd" in
    if cnt > 0 then
      Some
        {
          id = "CHAR-014";
          severity = Warning;
          message = "Unicode replacement � found – decoding error";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-014"; run }

(* CHAR-021: Zero-width no-break space U+FEFF inside paragraph (BOM) *)
let r_char_021 : rule =
  let run s =
    (* Count U+FEFF occurrences, skip the one at file start (legitimate BOM) *)
    let bom = "\xef\xbb\xbf" in
    let total = count_substring s bom in
    let starts_with_bom = String.length s >= 3 && String.sub s 0 3 = bom in
    let cnt = if starts_with_bom then total - 1 else total in
    if cnt > 0 then
      Some
        {
          id = "CHAR-021";
          severity = Error;
          message = "Zero‑width no‑break space U+FEFF inside paragraph";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-021"; run }

(* CHAR-015: Emoji detected in source *)
let r_char_015 : rule =
  let run s =
    (* Scan for common emoji ranges encoded in UTF-8: U+1F300-1F9FF = F0 9F 8C
       80 .. F0 9F A7 BF (4-byte seqs) *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 3 do
      if Char.code s.[!i] = 0xF0 && Char.code s.[!i + 1] = 0x9F then
        let b2 = Char.code s.[!i + 2] in
        (* U+1F300 = F0 9F 8C 80 through U+1F9FF = F0 9F A7 BF *)
        if b2 >= 0x8C && b2 <= 0xA7 then (
          incr cnt;
          i := !i + 4)
        else i := !i + 4
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-015";
          severity = Info;
          message = "Emoji detected in source";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-015"; run }

(* CHAR-017: Full-width Latin letters detected *)
let r_char_017 : rule =
  let run s =
    (* U+FF21-FF3A (A-Z) = EF BC A1 .. EF BC BA U+FF41-FF5A (a-z) = EF BD 81 ..
       EF BD 9A *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      let b0 = Char.code s.[!i] in
      let b1 = Char.code s.[!i + 1] in
      let b2 = Char.code s.[!i + 2] in
      if
        b0 = 0xEF
        && ((b1 = 0xBC && b2 >= 0xA1 && b2 <= 0xBA)
           || (b1 = 0xBD && b2 >= 0x81 && b2 <= 0x9A))
      then (
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-017";
          severity = Warning;
          message = "Full‑width Latin letters detected";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-017"; run }

(* CHAR-018: Deprecated ligature characters present *)
let r_char_018 : rule =
  let run s =
    (* U+FB00 ﬀ, U+FB01 ﬁ, U+FB02 ﬂ, U+FB03 ﬃ, U+FB04 ﬄ UTF-8: EF AC 80..84 *)
    let cnt =
      count_substring s "\xef\xac\x80"
      + count_substring s "\xef\xac\x81"
      + count_substring s "\xef\xac\x82"
      + count_substring s "\xef\xac\x83"
      + count_substring s "\xef\xac\x84"
    in
    if cnt > 0 then
      Some
        {
          id = "CHAR-018";
          severity = Info;
          message = "Deprecated ligature ﬀ/ﬁ/ﬂ characters present";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-018"; run }

(* CHAR-022: Deprecated tag characters U+E0000-E007F *)
let r_char_022 : rule =
  let run s =
    (* U+E0000-E007F = F3 A0 80 80 .. F3 A0 81 BF in UTF-8 *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 3 do
      if
        Char.code s.[!i] = 0xF3
        && Char.code s.[!i + 1] = 0xA0
        && (Char.code s.[!i + 2] = 0x80 || Char.code s.[!i + 2] = 0x81)
      then (
        incr cnt;
        i := !i + 4)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-022";
          severity = Warning;
          message = "Deprecated tag characters U+E0000–E007F present";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-022"; run }

(* CHAR-016: Double-width CJK punctuation in ASCII context *)
let r_char_016 : rule =
  let run s =
    (* CJK fullwidth punctuation: U+3001 (E3 80 81), U+3002 (E3 80 82), U+FF0C
       (EF BC 8C), U+FF0E (EF BC 8E), U+FF1A (EF BC 9A), U+FF1B (EF BC 9B),
       U+FF01 (EF BC 81), U+FF1F (EF BC 9F) *)
    let cnt =
      count_substring s "\xe3\x80\x81"
      + count_substring s "\xe3\x80\x82"
      + count_substring s "\xef\xbc\x8c"
      + count_substring s "\xef\xbc\x8e"
      + count_substring s "\xef\xbc\x9a"
      + count_substring s "\xef\xbc\x9b"
      + count_substring s "\xef\xbc\x81"
      + count_substring s "\xef\xbc\x9f"
    in
    if cnt > 0 then
      Some
        {
          id = "CHAR-016";
          severity = Warning;
          message = "Double‑width CJK punctuation in ASCII context";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-016"; run }

(* CHAR-019: Unicode minus U+2212 in text mode *)
let r_char_019 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s "\xe2\x88\x92" in
    if cnt > 0 then
      Some
        {
          id = "CHAR-019";
          severity = Info;
          message = "Unicode minus U+2212 in text mode";
          count = cnt;
        }
    else None
  in
  { id = "CHAR-019"; run }

(* CHAR-020: Sharp S in uppercase context — suggest SS *)
let r_char_020 : rule =
  let run s =
    (* U+00DF = C3 9F (lowercase sharp s) *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 1 do
      if Char.code s.[!i] = 0xC3 && Char.code s.[!i + 1] = 0x9F then (
        (* Check if surrounded by uppercase context *)
        let prev_upper =
          !i >= 1
          &&
          let c = Char.code s.[!i - 1] in
          c >= 0x41 && c <= 0x5A
        in
        let next_upper =
          !i + 2 < n
          &&
          let c = Char.code s.[!i + 2] in
          c >= 0x41 && c <= 0x5A
        in
        if prev_upper || next_upper then incr cnt;
        i := !i + 2)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-020";
          severity = Info;
          message = "Sharp S ß in uppercase context – suggest SS";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-020"; run }

(* CHAR-010: Right-to-left mark U+200F outside RTL context *)
let r_char_010 : rule =
  let run s =
    (* U+200F = E2 80 8F *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      if
        Char.code s.[!i] = 0xE2
        && Char.code s.[!i + 1] = 0x80
        && Char.code s.[!i + 2] = 0x8F
      then (
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-010";
          severity = Info;
          message = "Right‑to‑left mark U+200F outside RTL context";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-010"; run }

(* CHAR-011: Left-to-right mark U+200E unnecessary *)
let r_char_011 : rule =
  let run s =
    (* U+200E = E2 80 8E *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      if
        Char.code s.[!i] = 0xE2
        && Char.code s.[!i + 1] = 0x80
        && Char.code s.[!i + 2] = 0x8E
      then (
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-011";
          severity = Info;
          message = "Left‑to‑right mark U+200E unnecessary";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-011"; run }

(* CHAR-012: Zero-width joiner U+200D outside ligature context *)
let r_char_012 : rule =
  let run s =
    (* U+200D = E2 80 8D *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      if
        Char.code s.[!i] = 0xE2
        && Char.code s.[!i + 1] = 0x80
        && Char.code s.[!i + 2] = 0x8D
      then (
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-012";
          severity = Info;
          message = "Zero‑width joiner U+200D outside ligature context";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-012"; run }

let rules_char : rule list =
  [
    r_char_005;
    r_char_006;
    r_char_007;
    r_char_008;
    r_char_009;
    r_char_010;
    r_char_011;
    r_char_012;
    r_char_013;
    r_char_014;
    r_char_015;
    r_char_016;
    r_char_017;
    r_char_018;
    r_char_019;
    r_char_020;
    r_char_021;
    r_char_022;
  ]

(* ── SPC rules: spacing and whitespace ─────────────────────────────── *)

(* SPC-001: Line longer than 120 characters *)
let r_spc_001 : rule =
  let run s =
    let _, matched = any_line_pred s (fun line -> String.length line > 120) in
    if matched > 0 then
      Some
        {
          id = "SPC-001";
          severity = Info;
          message = "Line longer than 120 characters";
          count = matched;
        }
    else None
  in
  { id = "SPC-001"; run }

(* SPC-002: Line containing only whitespace *)
let r_spc_002 : rule =
  let run s =
    let is_ws_only line =
      let len = String.length line in
      len > 0
      &&
      let ok = ref true in
      for i = 0 to len - 1 do
        let c = line.[i] in
        if c <> ' ' && c <> '\t' && c <> '\r' then ok := false
      done;
      !ok
    in
    let _, matched = any_line_pred s is_ws_only in
    if matched > 0 then
      Some
        {
          id = "SPC-002";
          severity = Info;
          message = "Line containing only whitespace";
          count = matched;
        }
    else None
  in
  { id = "SPC-002"; run }

(* SPC-003: Hard tab precedes non-tab text (mixed indent) *)
let r_spc_003 : rule =
  let run s =
    let is_mixed_indent line =
      let len = String.length line in
      let i = ref 0 in
      let has_tab = ref false in
      let has_space = ref false in
      while !i < len && (line.[!i] = ' ' || line.[!i] = '\t') do
        if line.[!i] = '\t' then has_tab := true else has_space := true;
        incr i
      done;
      !has_tab && !has_space && !i < len
    in
    let _, matched = any_line_pred s is_mixed_indent in
    if matched > 0 then
      Some
        {
          id = "SPC-003";
          severity = Warning;
          message = "Hard tab precedes non‑tab text (mixed indent)";
          count = matched;
        }
    else None
  in
  { id = "SPC-003"; run }

(* SPC-004: Carriage return U+000D without LF *)
let r_spc_004 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    for i = 0 to n - 1 do
      if s.[i] = '\r' then
        if i + 1 < n && s.[i + 1] = '\n' then () else incr cnt
    done;
    if !cnt > 0 then
      Some
        {
          id = "SPC-004";
          severity = Warning;
          message = "Carriage return U+000D without LF";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-004"; run }

(* SPC-005: Trailing tab at end of line *)
let r_spc_005 : rule =
  let run s =
    let ends_with_tab line =
      let len = String.length line in
      len > 0 && line.[len - 1] = '\t'
    in
    let _, matched = any_line_pred s ends_with_tab in
    if matched > 0 then
      Some
        {
          id = "SPC-005";
          severity = Info;
          message = "Trailing tab at end of line";
          count = matched;
        }
    else None
  in
  { id = "SPC-005"; run }

(* SPC-006: Indentation mixes spaces and tabs *)
let r_spc_006 : rule =
  let run s =
    let has_mixed_indent line =
      let len = String.length line in
      if len = 0 then false
      else
        let seen_tab = ref false in
        let seen_space_after_tab = ref false in
        let i = ref 0 in
        while !i < len && (line.[!i] = ' ' || line.[!i] = '\t') do
          if line.[!i] = '\t' then seen_tab := true
          else if !seen_tab then seen_space_after_tab := true;
          incr i
        done;
        !seen_space_after_tab
    in
    let _, matched = any_line_pred s has_mixed_indent in
    if matched > 0 then
      Some
        {
          id = "SPC-006";
          severity = Info;
          message = "Indentation mixes spaces and tabs";
          count = matched;
        }
    else None
  in
  { id = "SPC-006"; run }

(* SPC-012: BOM not at file start *)
let r_spc_012 : rule =
  let run s =
    let bom = "\xef\xbb\xbf" in
    let total = count_substring s bom in
    let at_start = String.length s >= 3 && String.sub s 0 3 = bom in
    let interior = if at_start then total - 1 else total in
    if interior > 0 then
      Some
        {
          id = "SPC-012";
          severity = Error;
          message = "BOM not at file start";
          count = interior;
        }
    else None
  in
  { id = "SPC-012"; run }

(* SPC-024: Leading spaces on blank line *)
let r_spc_024 : rule =
  let run s =
    let is_spaces_only_blank line =
      let len = String.length line in
      len > 0
      &&
      let all_space = ref true in
      for i = 0 to len - 1 do
        if line.[i] <> ' ' && line.[i] <> '\t' then all_space := false
      done;
      !all_space
    in
    let _, matched = any_line_pred s is_spaces_only_blank in
    if matched > 0 then
      Some
        {
          id = "SPC-024";
          severity = Info;
          message = "Leading spaces on blank line";
          count = matched;
        }
    else None
  in
  { id = "SPC-024"; run }

(* SPC-028: Multiple consecutive ~ (non-breaking spaces) *)
let r_spc_028 : rule =
  let run s =
    let cnt = count_substring s "~~" in
    if cnt > 0 then
      Some
        {
          id = "SPC-028";
          severity = Warning;
          message = "Multiple consecutive ~ NBSPs";
          count = cnt;
        }
    else None
  in
  { id = "SPC-028"; run }

(* SPC-007: Three or more consecutive blank lines *)
let r_spc_007 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let consecutive_newlines = ref 0 in
    for i = 0 to n - 1 do
      if s.[i] = '\n' then (
        incr consecutive_newlines;
        (* 3 consecutive newlines = 2+ blank lines between content; 4 = 3+ blank
           lines which is what we flag *)
        if !consecutive_newlines = 4 then incr cnt
        else if !consecutive_newlines > 4 then () (* already counted *))
      else if s.[i] <> '\r' && s.[i] <> ' ' && s.[i] <> '\t' then
        consecutive_newlines := 0
    done;
    if !cnt > 0 then
      Some
        {
          id = "SPC-007";
          severity = Info;
          message = "Three or more consecutive blank lines";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-007"; run }

(* SPC-008: Paragraph starts with whitespace (indented first line after
   blank) *)
let r_spc_008 : rule =
  let run s =
    let has_indented_para line prev_blank =
      prev_blank
      && String.length line > 0
      && (line.[0] = ' ' || line.[0] = '\t')
      && (* skip \item lines *)
      not
        (let trimmed = String.trim line in
         String.length trimmed >= 5 && String.sub trimmed 0 5 = "\\item")
    in
    let lines = String.split_on_char '\n' s in
    let cnt = ref 0 in
    let prev_blank = ref true in
    (* start of file counts as after blank *)
    List.iter
      (fun line ->
        let trimmed = String.trim line in
        if has_indented_para line !prev_blank then incr cnt;
        prev_blank := String.length trimmed = 0)
      lines;
    if !cnt > 0 then
      Some
        {
          id = "SPC-008";
          severity = Info;
          message = "Paragraph starts with whitespace";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-008"; run }

(* SPC-009: Non-breaking space ~ at line start *)
let r_spc_009 : rule =
  let run s =
    let _, matched =
      any_line_pred s (fun line ->
          String.length line > 0
          && (line.[0] = '~'
             || String.length line >= 2
                && Char.code line.[0] = 0xC2
                && Char.code line.[1] = 0xA0))
    in
    if matched > 0 then
      Some
        {
          id = "SPC-009";
          severity = Warning;
          message = "Non‑breaking space ~ at line start";
          count = matched;
        }
    else None
  in
  { id = "SPC-009"; run }

(* SPC-013: Whitespace-only paragraph *)
let r_spc_013 : rule =
  let run s =
    (* A paragraph that contains only whitespace chars but is non-empty. Blank
       line = truly empty (length 0). Whitespace-only = length > 0, all chars
       are spaces/tabs. *)
    let lines = String.split_on_char '\n' s in
    let cnt = ref 0 in
    let para_started = ref false in
    let para_has_content = ref false in
    let para_has_ws = ref false in
    let flush () =
      if !para_started && !para_has_ws && not !para_has_content then incr cnt;
      para_started := false;
      para_has_content := false;
      para_has_ws := false
    in
    List.iter
      (fun line ->
        if String.length line = 0 then flush ()
        else
          let all_ws = ref true in
          String.iter
            (fun c ->
              if c <> ' ' && c <> '\t' && c <> '\r' then all_ws := false)
            line;
          if !all_ws then (
            para_started := true;
            para_has_ws := true)
          else (
            para_started := true;
            para_has_content := true))
      lines;
    flush ();
    if !cnt > 0 then
      Some
        {
          id = "SPC-013";
          severity = Info;
          message = "Whitespace‑only paragraph";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-013"; run }

(* SPC-014: Mixed LF and CRLF within same file *)
let r_spc_014 : rule =
  let run s =
    let n = String.length s in
    let has_crlf = ref false in
    let has_bare_lf = ref false in
    let i = ref 0 in
    while !i < n do
      if s.[!i] = '\r' && !i + 1 < n && s.[!i + 1] = '\n' then (
        has_crlf := true;
        i := !i + 2)
      else if s.[!i] = '\n' then (
        has_bare_lf := true;
        incr i)
      else incr i
    done;
    if !has_crlf && !has_bare_lf then
      Some
        {
          id = "SPC-014";
          severity = Info;
          message = "Mixed LF and CRLF within paragraph";
          count = 1;
        }
    else None
  in
  { id = "SPC-014"; run }

(* SPC-015: Indentation exceeds 8 spaces *)
let r_spc_015 : rule =
  let run s =
    let deep_indent line =
      let len = String.length line in
      let i = ref 0 in
      while !i < len && line.[!i] = ' ' do
        incr i
      done;
      !i > 8 && !i < len
    in
    let _, matched = any_line_pred s deep_indent in
    if matched > 0 then
      Some
        {
          id = "SPC-015";
          severity = Info;
          message = "Indentation exceeds 8 spaces";
          count = matched;
        }
    else None
  in
  { id = "SPC-015"; run }

(* SPC-016: Space before semicolon *)
let r_spc_016 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s " ;" in
    if cnt > 0 then
      Some
        {
          id = "SPC-016";
          severity = Warning;
          message = "Space before semicolon";
          count = cnt;
        }
    else None
  in
  { id = "SPC-016"; run }

(* SPC-017: Missing thin space before units — detect patterns like "5cm",
   "100kg", "3.5 GHz" where a number directly adjoins a unit abbreviation
   without a thin space (\,). We check for digit-letter transitions in text mode
   where the letter sequence matches a known SI/common unit. *)
let r_spc_017 : rule =
  let re =
    Str.regexp
      {|[0-9]\(mm\|cm\|km\|m\|kg\|g\|mg\|lb\|oz\|ml\|kl\|dB\|Hz\|kHz\|MHz\|GHz\|THz\|eV\|keV\|MeV\|GeV\|TeV\|K\|Pa\|kPa\|MPa\|bar\|atm\|mol\|cd\|lm\|lx\|Bq\|Gy\|Sv\|kat\|rad\|sr\|V\|kV\|mV\|W\|kW\|MW\|GW\|J\|kJ\|MJ\|cal\|kcal\|A\|mA\|N\|kN\|s\|ms\|ns\|min\|h\)\b|}
  in
  let run s =
    let s_text = strip_math_segments s in
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s_text !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "SPC-017";
          severity = Info;
          message = "Missing thin space before units (e.g. 5 cm)";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-017"; run }

(* SPC-019: Trailing full-width space U+3000 at line end *)
let r_spc_019 : rule =
  let run s =
    let trailing_fw_space line =
      let len = String.length line in
      len >= 3
      && Char.code line.[len - 3] = 0xE3
      && Char.code line.[len - 2] = 0x80
      && Char.code line.[len - 1] = 0x80
    in
    let _, matched = any_line_pred s trailing_fw_space in
    if matched > 0 then
      Some
        {
          id = "SPC-019";
          severity = Warning;
          message = "Trailing full‑width space U+3000 at line end";
          count = matched;
        }
    else None
  in
  { id = "SPC-019"; run }

(* SPC-021: Space before colon *)
let r_spc_021 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s " :" in
    if cnt > 0 then
      Some
        {
          id = "SPC-021";
          severity = Warning;
          message = "Space before colon";
          count = cnt;
        }
    else None
  in
  { id = "SPC-021"; run }

(* SPC-025: Space before ellipsis \dots *)
let r_spc_025 : rule =
  let run s =
    let cnt = count_substring s " \\dots" + count_substring s " \xe2\x80\xa6" in
    if cnt > 0 then
      Some
        {
          id = "SPC-025";
          severity = Info;
          message = {|Space before ellipsis \dots|};
          count = cnt;
        }
    else None
  in
  { id = "SPC-025"; run }

(* SPC-026: Mixed indentation width at same list depth — detect inconsistent
   indentation levels inside list environments (itemize/enumerate/description).
   If \item lines within the same environment use different leading whitespace
   widths, this rule fires. *)
let r_spc_026 : rule =
  let run s =
    let envs = [ "itemize"; "enumerate"; "description" ] in
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            let lines = String.split_on_char '\n' blk in
            (* Measure leading whitespace of \item lines *)
            let widths = ref [] in
            List.iter
              (fun line ->
                let len = String.length line in
                let j = ref 0 in
                while !j < len && (line.[!j] = ' ' || line.[!j] = '\t') do
                  incr j
                done;
                (* Check if the non-whitespace part starts with \item *)
                if
                  !j < len
                  && !j + 5 <= len
                  && String.sub line !j (min 5 (len - !j)) = "\\item"
                then widths := !j :: !widths)
              lines;
            (* If we found at least 2 \item lines with different indentation *)
            match !widths with
            | [] | [ _ ] -> ()
            | first :: rest ->
                if List.exists (fun w -> w <> first) rest then incr cnt)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "SPC-026";
          severity = Info;
          message = "Mixed indentation width at same list depth";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-026"; run }

(* SPC-029: Indentation uses NBSP U+00A0 characters *)
let r_spc_029 : rule =
  let run s =
    let nbsp_indent line =
      String.length line >= 2
      && Char.code line.[0] = 0xC2
      && Char.code line.[1] = 0xA0
    in
    let _, matched = any_line_pred s nbsp_indent in
    if matched > 0 then
      Some
        {
          id = "SPC-029";
          severity = Warning;
          message = "Indentation uses NBSP characters";
          count = matched;
        }
    else None
  in
  { id = "SPC-029"; run }

(* SPC-030: Line starts with full-width space U+3000 *)
let r_spc_030 : rule =
  let run s =
    let fw_space_start line =
      String.length line >= 3
      && Char.code line.[0] = 0xE3
      && Char.code line.[1] = 0x80
      && Char.code line.[2] = 0x80
    in
    let _, matched = any_line_pred s fw_space_start in
    if matched > 0 then
      Some
        {
          id = "SPC-030";
          severity = Warning;
          message = "Line starts with full‑width space U+3000";
          count = matched;
        }
    else None
  in
  { id = "SPC-030"; run }

(* SPC-031: Three spaces after period *)
let r_spc_031 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s ".   " in
    if cnt > 0 then
      Some
        {
          id = "SPC-031";
          severity = Info;
          message = "Three spaces after period";
          count = cnt;
        }
    else None
  in
  { id = "SPC-031"; run }

(* SPC-032: Indentation with mix of NBSP and regular space *)
let r_spc_032 : rule =
  let run s =
    let mixed_nbsp_indent line =
      let len = String.length line in
      let i = ref 0 in
      let has_nbsp = ref false in
      let has_space = ref false in
      while !i < len do
        if
          !i + 1 < len
          && Char.code line.[!i] = 0xC2
          && Char.code line.[!i + 1] = 0xA0
        then (
          has_nbsp := true;
          i := !i + 2)
        else if line.[!i] = ' ' then (
          has_space := true;
          incr i)
        else if line.[!i] = '\t' then incr i
        else i := len (* exit *)
      done;
      !has_nbsp && !has_space
    in
    let _, matched = any_line_pred s mixed_nbsp_indent in
    if matched > 0 then
      Some
        {
          id = "SPC-032";
          severity = Info;
          message = "Paragraph indented with mix of NBSP and space";
          count = matched;
        }
    else None
  in
  { id = "SPC-032"; run }

(* SPC-033: No-break space before em-dash in English text *)
let r_spc_033 : rule =
  let run s =
    (* U+00A0 = C2 A0 before em-dash U+2014 = E2 80 94 or --- *)
    let cnt =
      count_substring s "\xc2\xa0\xe2\x80\x94" + count_substring s "\xc2\xa0---"
    in
    if cnt > 0 then
      Some
        {
          id = "SPC-033";
          severity = Info;
          message = "No‑break space before em‑dash in English text forbidden";
          count = cnt;
        }
    else None
  in
  { id = "SPC-033"; run }

(* SPC-034: Thin-space U+2009 before en-dash *)
let r_spc_034 : rule =
  let run s =
    (* U+2009 = E2 80 89 before en-dash U+2013 = E2 80 93 or -- *)
    let cnt =
      count_substring s "\xe2\x80\x89\xe2\x80\x93"
      + count_substring s "\xe2\x80\x89--"
    in
    if cnt > 0 then
      Some
        {
          id = "SPC-034";
          severity = Info;
          message = "Thin‑space before en‑dash in command‑line flags removed";
          count = cnt;
        }
    else None
  in
  { id = "SPC-034"; run }

(* SPC-035: Leading thin-space U+2009 at start of line *)
let r_spc_035 : rule =
  let run s =
    let thin_space_start line =
      String.length line >= 3
      && Char.code line.[0] = 0xE2
      && Char.code line.[1] = 0x80
      && Char.code line.[2] = 0x89
    in
    let _, matched = any_line_pred s thin_space_start in
    if matched > 0 then
      Some
        {
          id = "SPC-035";
          severity = Info;
          message = "Leading thin‑space U+2009 at start of line";
          count = matched;
        }
    else None
  in
  { id = "SPC-035"; run }

(* SPC-010: Two spaces after sentence-ending period *)
let r_spc_010 : rule =
  let re = Str.regexp "\\. +[A-Z]" in
  let run s =
    let s = strip_math_segments s in
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        let m = Str.matched_string s in
        let nspaces = String.length m - 2 in
        (* Only count exactly 2 spaces — 3+ is SPC-031 *)
        let acc' = if nspaces = 2 then acc + 1 else acc in
        loop (Str.match_end ()) acc'
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "SPC-010";
          severity = Info;
          message = "Sentence spacing uses two spaces after period";
          count = cnt;
        }
    else None
  in
  { id = "SPC-010"; run }

(* SPC-018: No space after sentence-ending period (period+uppercase) *)
let r_spc_018 : rule =
  let re = Str.regexp "\\.[A-Z]" in
  let run s =
    let s = strip_math_segments s in
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        loop (Str.match_end ()) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "SPC-018";
          severity = Info;
          message = "No space after sentence‑ending period";
          count = cnt;
        }
    else None
  in
  { id = "SPC-018"; run }

(* SPC-022: Tab after bullet in \itemize *)
let r_spc_022 : rule =
  let run s =
    let cnt = count_substring s "\\item\t" in
    if cnt > 0 then
      Some
        {
          id = "SPC-022";
          severity = Info;
          message = "Tab after bullet in \\itemize";
          count = cnt;
        }
    else None
  in
  { id = "SPC-022"; run }

(* SPC-027: Trailing whitespace inside \url{} *)
let r_spc_027 : rule =
  let re = Str.regexp "\\\\url{\\([^}]*\\)}" in
  let run s =
    let rec loop i acc =
      try
        ignore (Str.search_forward re s i);
        let inner = Str.matched_group 1 s in
        let len = String.length inner in
        let has_leading = len > 0 && (inner.[0] = ' ' || inner.[0] = '\t') in
        let has_trailing =
          len > 0 && (inner.[len - 1] = ' ' || inner.[len - 1] = '\t')
        in
        let acc' = if has_leading || has_trailing then acc + 1 else acc in
        loop (Str.match_end ()) acc'
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "SPC-027";
          severity = Warning;
          message = "Trailing whitespace inside \\url{}";
          count = cnt;
        }
    else None
  in
  { id = "SPC-027"; run }

(* SPC-011: Space before newline inside $$…$$ display *)
let r_spc_011 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let in_display = ref false in
    let i = ref 0 in
    while !i < n - 1 do
      if s.[!i] = '$' && !i + 1 < n && s.[!i + 1] = '$' then (
        in_display := not !in_display;
        i := !i + 2)
      else if
        !in_display && (s.[!i] = ' ' || s.[!i] = '\t') && s.[!i + 1] = '\n'
      then (
        incr cnt;
        i := !i + 2)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "SPC-011";
          severity = Warning;
          message = "Space before newline inside $$…$$ display";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-011"; run }

(* SPC-020: Tab character inside math mode *)
let r_spc_020 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let in_math = ref false in
    let in_display = ref false in
    let i = ref 0 in
    while !i < n do
      if s.[!i] = '$' then
        if !i + 1 < n && s.[!i + 1] = '$' then (
          in_display := not !in_display;
          i := !i + 2)
        else (
          in_math := not !in_math;
          incr i)
      else (
        if (!in_math || !in_display) && s.[!i] = '\t' then incr cnt;
        incr i)
    done;
    if !cnt > 0 then
      Some
        {
          id = "SPC-020";
          severity = Warning;
          message = "Tab character inside math mode";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-020"; run }

(* SPC-023: Hard space U+00A0 outside French punctuation context *)
let r_spc_023 : rule =
  let run s =
    (* U+00A0 = C2 A0 *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 1 do
      if Char.code s.[!i] = 0xC2 && Char.code s.[!i + 1] = 0xA0 then (
        (* Check if adjacent to French punctuation: ; : ! ? « » *)
        let before_french =
          !i >= 1
          && (s.[!i - 1] = ';'
             || s.[!i - 1] = ':'
             || s.[!i - 1] = '!'
             || s.[!i - 1] = '?')
        in
        let after_french =
          !i + 2 < n
          && (s.[!i + 2] = ';'
             || s.[!i + 2] = ':'
             || s.[!i + 2] = '!'
             || s.[!i + 2] = '?')
        in
        (* Also check for guillemets « = C2 AB, » = C2 BB *)
        let before_guill =
          !i >= 2
          && Char.code s.[!i - 2] = 0xC2
          && (Char.code s.[!i - 1] = 0xAB || Char.code s.[!i - 1] = 0xBB)
        in
        let after_guill =
          !i + 3 < n
          && Char.code s.[!i + 2] = 0xC2
          && (Char.code s.[!i + 3] = 0xAB || Char.code s.[!i + 3] = 0xBB)
        in
        if not (before_french || after_french || before_guill || after_guill)
        then incr cnt;
        i := !i + 2)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "SPC-023";
          severity = Info;
          message = "Hard space U+00A0 outside French punctuation context";
          count = !cnt;
        }
    else None
  in
  { id = "SPC-023"; run }

let rules_spc : rule list =
  [
    r_spc_001;
    r_spc_002;
    r_spc_003;
    r_spc_004;
    r_spc_005;
    r_spc_006;
    r_spc_007;
    r_spc_008;
    r_spc_009;
    r_spc_010;
    r_spc_011;
    r_spc_012;
    r_spc_013;
    r_spc_014;
    r_spc_015;
    r_spc_016;
    r_spc_017;
    r_spc_018;
    r_spc_019;
    r_spc_020;
    r_spc_021;
    r_spc_022;
    r_spc_023;
    r_spc_024;
    r_spc_025;
    r_spc_026;
    r_spc_027;
    r_spc_028;
    r_spc_029;
    r_spc_030;
    r_spc_031;
    r_spc_032;
    r_spc_033;
    r_spc_034;
    r_spc_035;
  ]

(* ── VERB rules: verbatim / code environment checks ────────────────── *)

(* VERB-001: \verb delimiter reused inside same \verb block *)
let r_verb_001 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 5 do
      if
        !i + 5 < n
        && s.[!i] = '\\'
        && s.[!i + 1] = 'v'
        && s.[!i + 2] = 'e'
        && s.[!i + 3] = 'r'
        && s.[!i + 4] = 'b'
        && (!i + 5 >= n
           || s.[!i + 5] <> '*'
              && not
                   (Char.lowercase_ascii s.[!i + 5] >= 'a'
                   && Char.lowercase_ascii s.[!i + 5] <= 'z'))
      then
        let delim_pos =
          if !i + 5 < n && s.[!i + 5] = '*' then !i + 6 else !i + 5
        in
        if delim_pos < n then (
          let delim = s.[delim_pos] in
          let j = ref (delim_pos + 1) in
          let found_end = ref false in
          let has_reuse = ref false in
          while !j < n && not !found_end do
            if s.[!j] = delim then found_end := true
            else if
              s.[!j] = '\\'
              && !j + 4 < n
              && s.[!j + 1] = 'v'
              && s.[!j + 2] = 'e'
              && s.[!j + 3] = 'r'
              && s.[!j + 4] = 'b'
            then has_reuse := true;
            incr j
          done;
          if !has_reuse then incr cnt;
          i := !j)
        else i := n
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "VERB-001";
          severity = Error;
          message = "\\verb delimiter reused inside same \\verb block";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-001"; run }

(* VERB-002: Tab inside verbatim *)
let r_verb_002 : rule =
  let run s =
    let envs = [ "verbatim"; "lstlisting"; "minted" ] in
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk -> String.iter (fun c -> if c = '\t' then incr cnt) blk)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "VERB-002";
          severity = Info;
          message = "Tab inside verbatim – discouraged";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-002"; run }

(* VERB-003: Trailing spaces inside verbatim *)
let r_verb_003 : rule =
  let run s =
    let envs = [ "verbatim"; "lstlisting"; "minted" ] in
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            let lines = String.split_on_char '\n' blk in
            List.iter
              (fun line ->
                let len = String.length line in
                if len > 0 && (line.[len - 1] = ' ' || line.[len - 1] = '\t')
                then incr cnt)
              lines)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "VERB-003";
          severity = Info;
          message = "Trailing spaces inside verbatim";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-003"; run }

(* VERB-004: Non-ASCII quotes inside verbatim *)
let r_verb_004 : rule =
  let run s =
    let envs = [ "verbatim"; "lstlisting"; "minted" ] in
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            let n = String.length blk in
            let i = ref 0 in
            while !i < n - 2 do
              let b0 = Char.code blk.[!i] in
              if b0 = 0xE2 && !i + 2 < n then (
                let b1 = Char.code blk.[!i + 1] in
                let b2 = Char.code blk.[!i + 2] in
                if
                  b1 = 0x80 && (b2 = 0x9C || b2 = 0x9D || b2 = 0x98 || b2 = 0x99)
                then incr cnt;
                i := !i + 3)
              else incr i
            done)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "VERB-004";
          severity = Warning;
          message = "Non‑ASCII quotes inside verbatim";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-004"; run }

(* VERB-005: Verbatim line > 120 characters *)
let r_verb_005 : rule =
  let run s =
    let envs = [ "verbatim"; "lstlisting"; "minted" ] in
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            let lines = String.split_on_char '\n' blk in
            List.iter
              (fun line -> if String.length line > 120 then incr cnt)
              lines)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "VERB-005";
          severity = Info;
          message = "Verbatim line > 120 characters";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-005"; run }

(* VERB-006: Inline \verb used for multiline content *)
let r_verb_006 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 5 do
      if
        s.[!i] = '\\'
        && s.[!i + 1] = 'v'
        && s.[!i + 2] = 'e'
        && s.[!i + 3] = 'r'
        && s.[!i + 4] = 'b'
        && (!i + 5 >= n
           || s.[!i + 5] <> '*'
              && not
                   (Char.lowercase_ascii s.[!i + 5] >= 'a'
                   && Char.lowercase_ascii s.[!i + 5] <= 'z'))
      then
        let delim_pos =
          if !i + 5 < n && s.[!i + 5] = '*' then !i + 6 else !i + 5
        in
        if delim_pos < n then (
          let delim = s.[delim_pos] in
          let j = ref (delim_pos + 1) in
          let found_end = ref false in
          let has_newline = ref false in
          while !j < n && not !found_end do
            if s.[!j] = delim then found_end := true
            else if s.[!j] = '\n' then has_newline := true;
            incr j
          done;
          if !has_newline then incr cnt;
          i := !j)
        else i := n
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "VERB-006";
          severity = Error;
          message = "Inline \\verb used for multiline content";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-006"; run }

(* VERB-007: Nested verbatim environment *)
let r_verb_007 : rule =
  let run s =
    let envs = [ "verbatim"; "lstlisting"; "minted" ] in
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            List.iter
              (fun inner_env ->
                let tag = "\\begin{" ^ inner_env ^ "}" in
                let tlen = String.length tag in
                let n = String.length blk in
                let i = ref 0 in
                while !i <= n - tlen do
                  if String.sub blk !i tlen = tag then (
                    incr cnt;
                    i := !i + tlen)
                  else incr i
                done)
              envs)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "VERB-007";
          severity = Error;
          message = "Nested verbatim environment";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-007"; run }

(* VERB-008: lstlisting uses language=none *)
let r_verb_008 : rule =
  let re = Str.regexp {|\\begin{lstlisting}\[.*language *= *none.*\]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "VERB-008";
          severity = Info;
          message = "`lstlisting` uses language=none";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-008"; run }

(* VERB-009: Missing caption in minted code block *)
let r_verb_009 : rule =
  let run s =
    let _blocks = extract_env_blocks "minted" s in
    let cnt = ref 0 in
    (* For each \begin{minted}, check if wrapped in listing/figure env *)
    let n = String.length s in
    let tag = "\\begin{minted}" in
    let tlen = String.length tag in
    let i = ref 0 in
    while !i <= n - tlen do
      if String.sub s !i tlen = tag then (
        let context_start = max 0 (!i - 200) in
        let before = String.sub s context_start (!i - context_start) in
        if
          not
            (try
               let _ =
                 Str.search_forward
                   (Str.regexp_string "\\begin{listing}")
                   before 0
               in
               true
             with Not_found -> false)
        then incr cnt;
        i := !i + tlen)
      else incr i
    done;
    let cnt = !cnt in
    if cnt > 0 then
      Some
        {
          id = "VERB-009";
          severity = Warning;
          message = "Missing caption in `minted` code block";
          count = cnt;
        }
    else None
  in
  { id = "VERB-009"; run }

(* VERB-010: Inline code uses back-ticks instead of \verb *)
let r_verb_010 : rule =
  let re = Str.regexp "`[^`\n]+`" in
  let run s =
    let s_text = strip_math_segments s in
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s_text !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "VERB-010";
          severity = Info;
          message = {|Inline code uses back‑ticks instead of \verb|};
          count = !cnt;
        }
    else None
  in
  { id = "VERB-010"; run }

(* VERB-011: Unknown lstlisting language — detect \begin{lstlisting}[language=X]
   where X is not in the standard set of languages supported by the listings
   package. We extract the language= option value and check against a known
   set. *)
let r_verb_011 : rule =
  let known_languages =
    [
      "abap";
      "acm";
      "acmscript";
      "ada";
      "algol";
      "ant";
      "assembler";
      "awk";
      "bash";
      "basic";
      "c";
      "caml";
      "cil";
      "clean";
      "cobol";
      "comal";
      "command";
      "comsol";
      "csh";
      "delphi";
      "eiffel";
      "elan";
      "elisp";
      "erlang";
      "euphoria";
      "forth";
      "fortran";
      "gcl";
      "gnuplot";
      "go";
      "hansl";
      "haskell";
      "html";
      "idl";
      "inform";
      "java";
      "jvmis";
      "ksh";
      "lingo";
      "lisp";
      "llvm";
      "logo";
      "lua";
      "make";
      "mathematica";
      "matlab";
      "mercury";
      "metapost";
      "miranda";
      "mizar";
      "ml";
      "modula";
      "mupad";
      "nastran";
      "oberon";
      "objective";
      "ocaml";
      "octave";
      "oorexx";
      "oz";
      "pascal";
      "perl";
      "php";
      "pli";
      "plasm";
      "postscript";
      "pov";
      "prolog";
      "promela";
      "pstricks";
      "python";
      "r";
      "reduce";
      "rexx";
      "rsl";
      "ruby";
      "rust";
      "s";
      "sas";
      "scala";
      "scilab";
      "sh";
      "shelxl";
      "simula";
      "sparql";
      "sql";
      "swift";
      "tcl";
      "tex";
      "vbscript";
      "verilog";
      "vhdl";
      "vrml";
      "xml";
      "xslt";
    ]
  in
  let re =
    Str.regexp
      {|\\begin{lstlisting}[ \t\n]*\[[^]]*language[ \t]*=[ \t]*\([A-Za-z+#]*\)|}
  in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         let lang = String.lowercase_ascii (Str.matched_group 1 s) in
         (* Strip trailing +/# for languages like C++, C#, Objective-C *)
         let lang_base =
           let len = String.length lang in
           let j = ref (len - 1) in
           while !j >= 0 && (lang.[!j] = '+' || lang.[!j] = '#') do
             decr j
           done;
           if !j < len - 1 then String.sub lang 0 (!j + 1) else lang
         in
         if
           not
             (List.exists (fun k -> k = lang || k = lang_base) known_languages)
         then incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "VERB-011";
          severity = Warning;
          message = "Unknown `lstlisting` language";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-011"; run }

(* VERB-012: minted block missing autogobble *)
let r_verb_012 : rule =
  let re = Str.regexp "\\\\begin{minted}[ \t\n]*\\(\\[[^]]*\\]\\)?[ \t\n]*{" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re s !i in
         let matched = Str.matched_string s in
         if
           not
             (try
                let _ =
                  Str.search_forward (Str.regexp_string "autogobble") matched 0
                in
                true
              with Not_found -> false)
         then incr cnt;
         i := pos + String.length matched
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "VERB-012";
          severity = Info;
          message = "`minted` block missing autogobble";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-012"; run }

(* VERB-013: Code line > 120 glyphs — same as VERB-005 but for minted
   specifically *)
let r_verb_013 : rule =
  let run s =
    let blocks = extract_env_blocks "minted" s in
    let cnt = ref 0 in
    List.iter
      (fun blk ->
        let lines = String.split_on_char '\n' blk in
        List.iter (fun line -> if String.length line > 120 then incr cnt) lines)
      blocks;
    if !cnt > 0 then
      Some
        {
          id = "VERB-013";
          severity = Info;
          message = "Code line > 120 glyphs";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-013"; run }

(* VERB-015: Verbatim uses catcode changes instead of \verb *)
let r_verb_015 : rule =
  let re = Str.regexp "\\\\catcode[ \t\n]*`" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "VERB-015";
          severity = Warning;
          message = "Verbatim uses catcode changes instead of \\verb";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-015"; run }

(* VERB-016: minted without escapeinside while containing back-ticks *)
let r_verb_016 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let tag = "\\begin{minted}" in
    let tlen = String.length tag in
    let i = ref 0 in
    while !i <= n - tlen do
      if String.sub s !i tlen = tag then (
        (* Find the options and body *)
        let opts_end = ref (!i + tlen) in
        (* Skip optional [...] *)
        if !opts_end < n && s.[!opts_end] = '[' then (
          while !opts_end < n && s.[!opts_end] <> ']' do
            incr opts_end
          done;
          if !opts_end < n then incr opts_end);
        let opts = String.sub s (!i + tlen) (!opts_end - !i - tlen) in
        let has_escape =
          try
            let _ =
              Str.search_forward (Str.regexp_string "escapeinside") opts 0
            in
            true
          with Not_found -> false
        in
        if not has_escape then
          (* Check body for back-ticks *)
          let blocks = extract_env_blocks "minted" (String.sub s !i (n - !i)) in
          match blocks with
          | blk :: _ ->
              if String.contains blk '`' then incr cnt;
              i := !opts_end
          | [] -> i := !opts_end
        else i := !opts_end)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "VERB-016";
          severity = Info;
          message =
            "`minted` without `escapeinside` while containing back‑ticks";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-016"; run }

(* VERB-017: minted lacks linenos in code block > 20 lines *)
let r_verb_017 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let tag = "\\begin{minted}" in
    let tlen = String.length tag in
    let i = ref 0 in
    while !i <= n - tlen do
      if String.sub s !i tlen = tag then (
        let opts_end = ref (!i + tlen) in
        if !opts_end < n && s.[!opts_end] = '[' then (
          while !opts_end < n && s.[!opts_end] <> ']' do
            incr opts_end
          done;
          if !opts_end < n then incr opts_end);
        let opts = String.sub s (!i + tlen) (!opts_end - !i - tlen) in
        let has_linenos =
          try
            let _ = Str.search_forward (Str.regexp_string "linenos") opts 0 in
            true
          with Not_found -> false
        in
        if not has_linenos then
          let blocks = extract_env_blocks "minted" (String.sub s !i (n - !i)) in
          match blocks with
          | blk :: _ ->
              let lines = String.split_on_char '\n' blk in
              if List.length lines > 20 then incr cnt;
              i := !opts_end
          | [] -> i := !opts_end
        else i := !opts_end)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "VERB-017";
          severity = Info;
          message = "`minted` lacks `linenos` in code block > 20 lines";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-017"; run }

let rules_verb : rule list =
  [
    r_verb_001;
    r_verb_002;
    r_verb_003;
    r_verb_004;
    r_verb_005;
    r_verb_006;
    r_verb_007;
    r_verb_008;
    r_verb_009;
    r_verb_010;
    r_verb_011;
    r_verb_012;
    r_verb_013;
    r_verb_015;
    r_verb_016;
    r_verb_017;
  ]

(* ── CJK rules: CJK character and punctuation checks ────────────────── *)

(* CJK-001: Full-width comma U+FF0C in ASCII context *)
let r_cjk_001 : rule =
  let run s =
    (* U+FF0C = EF BC 8C *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      if
        Char.code s.[!i] = 0xEF
        && Char.code s.[!i + 1] = 0xBC
        && Char.code s.[!i + 2] = 0x8C
      then (
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CJK-001";
          severity = Warning;
          message = "Full‑width comma U+FF0C in ASCII context";
          count = !cnt;
        }
    else None
  in
  { id = "CJK-001"; run }

(* CJK-002: Full-width period U+FF0E in ASCII context *)
let r_cjk_002 : rule =
  let run s =
    (* U+FF0E = EF BC 8E *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      if
        Char.code s.[!i] = 0xEF
        && Char.code s.[!i + 1] = 0xBC
        && Char.code s.[!i + 2] = 0x8E
      then (
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CJK-002";
          severity = Warning;
          message = "Full‑width period U+FF0E in ASCII context";
          count = !cnt;
        }
    else None
  in
  { id = "CJK-002"; run }

(* CJK-010: Half-width CJK punctuation in full-width context *)
(* Detect ASCII comma/period/colon/semicolon adjacent to CJK characters *)
let r_cjk_010 : rule =
  let is_cjk_byte0 b = b >= 0xE4 && b <= 0xE9 in
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    for i = 0 to n - 1 do
      let c = s.[i] in
      if c = ',' || c = '.' || c = ':' || c = ';' then
        if
          (* Check if preceded by a CJK character (3-byte UTF-8 starting
             E4-E9) *)
          i >= 3 && is_cjk_byte0 (Char.code s.[i - 3])
        then incr cnt (* or followed by CJK *)
        else if i + 3 < n && is_cjk_byte0 (Char.code s.[i + 1]) then incr cnt
    done;
    if !cnt > 0 then
      Some
        {
          id = "CJK-010";
          severity = Warning;
          message = "Half‑width CJK punctuation in full‑width context";
          count = !cnt;
        }
    else None
  in
  { id = "CJK-010"; run }

(* CJK-014: Inter-punct U+30FB outside CJK run *)
let r_cjk_014 : rule =
  let run s =
    (* U+30FB = E3 83 BB *)
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 2 do
      if
        Char.code s.[!i] = 0xE3
        && Char.code s.[!i + 1] = 0x83
        && Char.code s.[!i + 2] = 0xBB
      then (
        incr cnt;
        i := !i + 3)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "CJK-014";
          severity = Info;
          message = "Inter‑punct U+30FB outside CJK run";
          count = !cnt;
        }
    else None
  in
  { id = "CJK-014"; run }

let rules_cjk : rule list = [ r_cjk_001; r_cjk_002; r_cjk_010; r_cjk_014 ]

(* ── Locale rules: language-specific checks ─────────────────────────── *)

(* FR-007: FR-BE thin NB-space before/after € sign *)
let r_fr_007 : rule =
  (* Detect € preceded/followed by normal space instead of NBSP/thin space *)
  let re = Str.regexp "[ ]\xe2\x82\xac\\|\xe2\x82\xac[ ]" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !i);
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "FR-007";
          severity = Info;
          message = {|FR‑BE: thin NB‑space before/after € sign required|};
          count = !cnt;
        }
    else None
  in
  { id = "FR-007"; run }

(* FR-008: French ligature œ/Œ mandatory *)
let r_fr_008 : rule =
  (* Detect "oe" where œ is required: coeur, oeuvre, oeuf, oeil, noeud, voeu,
     etc. *)
  let words =
    [
      "coeur";
      "oeuvre";
      "oeuf";
      "oeil";
      "noeud";
      "voeu";
      "soeur";
      "moeurs";
      "foetus";
      "manoeuvre";
    ]
  in
  let run s =
    let s_low = String.lowercase_ascii s in
    let cnt =
      List.fold_left (fun acc w -> acc + count_substring s_low w) 0 words
    in
    if cnt > 0 then
      Some
        {
          id = "FR-008";
          severity = Warning;
          message = {|French: ligature œ/Œ mandatory in “cœur”, “œuvre”…|};
          count = cnt;
        }
    else None
  in
  { id = "FR-008"; run }

(* PT-003: pt-PT ordinal must use º/ª *)
let r_pt_003 : rule =
  (* Detect patterns like 1\textsuperscript{o} or 1\textsuperscript{a} *)
  let re = Str.regexp "[0-9]\\\\textsuperscript{[oa]}" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !i);
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "PT-003";
          severity = Info;
          message = {|pt‑PT: ordinal 1.º/1.ª must use º/ª, not superscript|};
          count = !cnt;
        }
    else None
  in
  { id = "PT-003"; run }

(* RU-001: NB-space required before em-dash *)
let r_ru_001 : rule =
  (* Detect regular space before em-dash (U+2014 = \xe2\x80\x94) *)
  let run s =
    let cnt = count_substring s " \xe2\x80\x94" in
    if cnt > 0 then
      Some
        {
          id = "RU-001";
          severity = Info;
          message = {|RU: NB‑space required before em‑dash|};
          count = cnt;
        }
    else None
  in
  { id = "RU-001"; run }

(* PL-001: NB-space before abbreviations *)
let r_pl_001 : rule =
  (* Detect regular space before Polish abbreviations r., nr, s. *)
  let re = Str.regexp " \\(r\\.\\|nr \\|s\\.\\)" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !i);
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "PL-001";
          severity = Info;
          message = {|PL: NB‑space before abbreviations “r.”, “nr”, “s.”|};
          count = !cnt;
        }
    else None
  in
  { id = "PL-001"; run }

(* CS-001: thin NB-space before °C forbidden *)
let r_cs_001 : rule =
  (* Detect thin space (\,) or NBSP before °C — CS/SK forbids it *)
  let re = Str.regexp "\\\\,\xc2\xb0C\\|\xc2\xa0\xc2\xb0C" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !i);
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "CS-001";
          severity = Info;
          message = {|CS/SK: thin NB‑space before °C forbidden|};
          count = !cnt;
        }
    else None
  in
  { id = "CS-001"; run }

(* CS-002: date format must be 30.\,1.\,2026 *)
let r_cs_002 : rule =
  (* Detect date patterns like 30.1.2026 without \, *)
  let re = Str.regexp "[0-9]+\\.[0-9]+\\.[0-9][0-9][0-9][0-9]" in
  let re_correct =
    Str.regexp "[0-9]+\\.\\\\,[0-9]+\\.\\\\,[0-9][0-9][0-9][0-9]"
  in
  let run s =
    let has_bare =
      try
        ignore (Str.search_forward re s 0);
        true
      with Not_found -> false
    in
    let has_correct =
      try
        ignore (Str.search_forward re_correct s 0);
        true
      with Not_found -> false
    in
    if has_bare && not has_correct then
      Some
        {
          id = "CS-002";
          severity = Info;
          message = "CS/SK: date format must be 30.\\,1.\\,2026";
          count = 1;
        }
    else None
  in
  { id = "CS-002"; run }

(* EL-001: Greek oxia vs tonos normalisation *)
let r_el_001 : rule =
  (* Detect Greek oxia accents (U+1F00-1FFF range) that should be tonos
     (U+0384/0385) *)
  (* Check for polytonic accents in 0x1F00-0x1FFF range *)
  let run s =
    let cnt = ref 0 in
    let len = String.length s in
    let i = ref 0 in
    while !i < len - 2 do
      let b0 = Char.code (String.unsafe_get s !i) in
      if b0 = 0xe1 then (
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        (if b1 >= 0xbc && b1 <= 0xbf then
           let b2 = Char.code (String.unsafe_get s (!i + 2)) in
           if b2 >= 0x80 && b2 <= 0xbf then incr cnt);
        i := !i + 3)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "EL-001";
          severity = Warning;
          message = {|Greek: oxia vs tonos normalisation|};
          count = !cnt;
        }
    else None
  in
  { id = "EL-001"; run }

(* RO-001: use Ș/ș (S-comma) not Ş/ş (S-cedilla) *)
let r_ro_001 : rule =
  (* Ş = U+015E = \xc5\x9e, ş = U+015F = \xc5\x9f *)
  (* Also Ţ = U+0162 = \xc5\xa2, ţ = U+0163 = \xc5\xa3 (T-cedilla vs T-comma) *)
  let run s =
    let cnt =
      count_substring s "\xc5\x9e"
      + count_substring s "\xc5\x9f"
      + count_substring s "\xc5\xa2"
      + count_substring s "\xc5\xa3"
    in
    if cnt > 0 then
      Some
        {
          id = "RO-001";
          severity = Warning;
          message = {|RO: use Ș/ș (S‑comma) not Ş/ş (S‑cedilla)|};
          count = cnt;
        }
    else None
  in
  { id = "RO-001"; run }

(* AR-002: ASCII hyphen in phone numbers — use \arabicdash *)
let r_ar_002 : rule =
  (* Detect ASCII hyphen-minus between digits in Arabic text context *)
  (* Arabic digits: U+0660-0669 = \xd9\xa0-\xd9\xa9 *)
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len do
      if
        !i + 4 < len
        && Char.code (String.unsafe_get s !i) = 0xd9
        && Char.code (String.unsafe_get s (!i + 1)) >= 0xa0
        && Char.code (String.unsafe_get s (!i + 1)) <= 0xa9
        && String.unsafe_get s (!i + 2) = '-'
        && Char.code (String.unsafe_get s (!i + 3)) = 0xd9
        && Char.code (String.unsafe_get s (!i + 4)) >= 0xa0
        && Char.code (String.unsafe_get s (!i + 4)) <= 0xa9
      then (
        incr cnt;
        i := !i + 5)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "AR-002";
          severity = Info;
          message = {|AR: ASCII hyphen in phone numbers—use \arabicdash|};
          count = !cnt;
        }
    else None
  in
  { id = "AR-002"; run }

(* HE-001: apostrophe used instead of geresh U+05F3 *)
let r_he_001 : rule =
  (* Detect ASCII apostrophe ' adjacent to Hebrew letters (U+05D0-05EA =
     \xd7\x90-\xd7\xaa) *)
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len do
      if
        String.unsafe_get s !i = '\''
        && !i >= 2
        && Char.code (String.unsafe_get s (!i - 2)) = 0xd7
        &&
        let b = Char.code (String.unsafe_get s (!i - 1)) in
        b >= 0x90 && b <= 0xaa
      then (
        incr cnt;
        i := !i + 1)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "HE-001";
          severity = Warning;
          message = {|HE: apostrophe used instead of geresh U+05F3|};
          count = !cnt;
        }
    else None
  in
  { id = "HE-001"; run }

(* ZH-001: western '.' — use Chinese '。' *)
let r_zh_001 : rule =
  (* Detect ASCII period after CJK character *)
  (* CJK Unified Ideographs: U+4E00-9FFF, 3-byte UTF-8: \xe4\xb8\x80 -
     \xe9\xbf\xbf *)
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len do
      if
        !i + 3 < len
        && (let b0 = Char.code (String.unsafe_get s !i) in
            b0 >= 0xe4 && b0 <= 0xe9)
        && (let b1 = Char.code (String.unsafe_get s (!i + 1)) in
            b1 >= 0x80 && b1 <= 0xbf)
        && (let b2 = Char.code (String.unsafe_get s (!i + 2)) in
            b2 >= 0x80 && b2 <= 0xbf)
        && String.unsafe_get s (!i + 3) = '.'
      then (
        incr cnt;
        i := !i + 4)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "ZH-001";
          severity = Info;
          message = {|ZH‑Hans: western '.' – use Chinese ‘。’|};
          count = !cnt;
        }
    else None
  in
  { id = "ZH-001"; run }

(* JA-001: half-width katakana present — use full-width *)
let r_ja_001 : rule =
  (* Half-width katakana: U+FF65-FF9F = \xef\xbd\xa5-\xef\xbe\x9f *)
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len - 2 do
      let b0 = Char.code (String.unsafe_get s !i) in
      if b0 = 0xef then (
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        (* U+FF65-FF9F: EF BD A5 - EF BE 9F *)
        if (b1 = 0xbd && b2 >= 0xa5) || (b1 = 0xbe && b2 <= 0x9f) then incr cnt;
        i := !i + 3)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "JA-001";
          severity = Warning;
          message = {|JA: half‑width katakana present—use full‑width|};
          count = !cnt;
        }
    else None
  in
  { id = "JA-001"; run }

(* JA-002: U+FF5E tilde normalise to wave-dash U+301C *)
let r_ja_002 : rule =
  (* U+FF5E fullwidth tilde = \xef\xbd\x9e *)
  let run s =
    let cnt = count_substring s "\xef\xbd\x9e" in
    if cnt > 0 then
      Some
        {
          id = "JA-002";
          severity = Info;
          message = {|JA: U+FF5E tilde normalise to wave‑dash U+301C|};
          count = cnt;
        }
    else None
  in
  { id = "JA-002"; run }

(* KO-001: Old-Hangul jamo outside scholarly context *)
let r_ko_001 : rule =
  (* Old Hangul Jamo: archaic ranges *)
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len - 2 do
      let b0 = Char.code (String.unsafe_get s !i) in
      if b0 = 0xe1 then (
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        (* U+1113-115F: E1 84 93 - E1 85 9F *)
        if
          (b1 = 0x84 && b2 >= 0x93)
          || (b1 = 0x85 && b2 <= 0x9f)
          (* U+1176-11A7: E1 85 B6 - E1 86 A7 *)
          || (b1 = 0x85 && b2 >= 0xb6)
          || (b1 = 0x86 && b2 <= 0xa7)
          (* U+11C3-11FF: E1 87 83 - E1 87 BF *)
          || (b1 = 0x87 && b2 >= 0x83 && b2 <= 0xbf)
        then incr cnt;
        i := !i + 3)
      else if b0 = 0xea then (
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        (* U+A960-A97C: EA A5 A0 - EA A5 BC *)
        if b1 = 0xa5 && b2 >= 0xa0 && b2 <= 0xbc then incr cnt;
        i := !i + 3)
      else if b0 = 0xed then (
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        (* U+D7B0-D7FF: ED 9E B0 - ED 9F BF *)
        if (b1 = 0x9e && b2 >= 0xb0) || (b1 = 0x9f && b2 >= 0x80 && b2 <= 0xbf)
        then incr cnt;
        i := !i + 3)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "KO-001";
          severity = Warning;
          message = {|KO: Old‑Hangul jamo outside scholarly context|};
          count = !cnt;
        }
    else None
  in
  { id = "KO-001"; run }

(* HI-001: ZWJ/ZWNJ misuse next to ख् *)
let r_hi_001 : rule =
  (* ZWJ = U+200D = \xe2\x80\x8d, ZWNJ = U+200C = \xe2\x80\x8c *)
  (* Halant/virama: U+094D = \xe0\xa5\x8d *)
  (* Detect ZWJ/ZWNJ adjacent to halant *)
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len - 5 do
      let b0 = Char.code (String.unsafe_get s !i) in
      if b0 = 0xe0 then
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        (* Check for halant U+094D = E0 A5 8D *)
        if b1 = 0xa5 && b2 = 0x8d && !i + 5 < len then
          let c0 = Char.code (String.unsafe_get s (!i + 3)) in
          let c1 = Char.code (String.unsafe_get s (!i + 4)) in
          let c2 = Char.code (String.unsafe_get s (!i + 5)) in
          (* ZWJ E2 80 8D or ZWNJ E2 80 8C *)
          if c0 = 0xe2 && c1 = 0x80 && (c2 = 0x8d || c2 = 0x8c) then (
            incr cnt;
            i := !i + 6)
          else i := !i + 3
        else i := !i + 3
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "HI-001";
          severity = Info;
          message = {|HI: ZWJ/ZWNJ misuse next to ख्|};
          count = !cnt;
        }
    else None
  in
  { id = "HI-001"; run }

let rules_locale : rule list =
  [
    r_fr_007;
    r_fr_008;
    r_pt_003;
    r_ru_001;
    r_pl_001;
    r_cs_001;
    r_cs_002;
    r_el_001;
    r_ro_001;
    r_ar_002;
    r_he_001;
    r_zh_001;
    r_ja_001;
    r_ja_002;
    r_ko_001;
    r_hi_001;
  ]

(* ── Straggler rules ─────────────────────────────────────────────────── *)

(* CY-001: Cyrillic initials require NB-space "И.\,И." *)
let r_cy_001 : rule =
  (* Detect Cyrillic letter followed by period and regular space before another
     Cyrillic letter — should use NB-space / \, *)
  (* Cyrillic capital letters: U+0410-042F = D0 90-D0 AF *)
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len - 4 do
      let b0 = Char.code (String.unsafe_get s !i) in
      if b0 = 0xd0 then
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        (* Cyrillic capital: D0 90-AF *)
        if b1 >= 0x90 && b1 <= 0xaf && !i + 4 < len then
          if
            String.unsafe_get s (!i + 2) = '.'
            && String.unsafe_get s (!i + 3) = ' '
          then (
            (* Check if next is Cyrillic capital *)
            let n0 = Char.code (String.unsafe_get s (!i + 4)) in
            if n0 = 0xd0 && !i + 5 < len then (
              let n1 = Char.code (String.unsafe_get s (!i + 5)) in
              if n1 >= 0x90 && n1 <= 0xaf then incr cnt;
              i := !i + 4))
          else i := !i + 2
        else i := !i + 2
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "CY-001";
          severity = Info;
          message = {esc|Cyrillic initials require NB‑space "И.\,И."|esc};
          count = !cnt;
        }
    else None
  in
  { id = "CY-001"; run }

(* DE-006: Swiss DE ß prohibited — use "ss" *)
let r_de_006 : rule =
  let run s =
    (* Count ß (U+00DF = C3 9F) and ẞ (U+1E9E = E1 BA 9E) *)
    let cnt = count_substring s "\xc3\x9f" + count_substring s "\xe1\xba\x9e" in
    if cnt > 0 then
      Some
        {
          id = "DE-006";
          severity = Info;
          message = {|Swiss DE: glyph ß is prohibited—use “ss”|};
          count = cnt;
        }
    else None
  in
  { id = "DE-006"; run }

(* NL-001: NL digraph IJ/ij — capitalise both at sentence start *)
let r_nl_001 : rule =
  (* Detect 'Ij' at start of sentence (after '. ' or at start) *)
  let run s =
    let cnt = ref 0 in
    let len = String.length s in
    (* Check at start of string *)
    if len >= 2 && s.[0] = 'I' && s.[1] = 'j' then incr cnt;
    let i = ref 0 in
    while !i < len - 3 do
      if
        (s.[!i] = '.' || s.[!i] = '!' || s.[!i] = '?')
        && s.[!i + 1] = ' '
        && s.[!i + 2] = 'I'
        && s.[!i + 3] = 'j'
      then (
        incr cnt;
        i := !i + 4)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "NL-001";
          severity = Info;
          message =
            {|NL: digraph IJ/ij—capitalise both letters at sentence start|};
          count = !cnt;
        }
    else None
  in
  { id = "NL-001"; run }

(* NL-002: NL quotes must be uniform *)
let r_nl_002 : rule =
  let run s =
    (* Detect mixing of single-style quotes and German-style quotes *)
    (* Single opening ' U+2018 = E2 80 98 *)
    (* German opening „ U+201E = E2 80 9E *)
    let has_single =
      count_substring s "\xe2\x80\x98" > 0
      || count_substring s "\xe2\x80\x99" > 0
    in
    let has_german =
      count_substring s "\xe2\x80\x9e" > 0
      || count_substring s "\xe2\x80\x9f" > 0
    in
    if has_single && has_german then
      Some
        {
          id = "NL-002";
          severity = Info;
          message = {|NL: quotes must be uniform (‘…’ or „…‟)|};
          count = 1;
        }
    else None
  in
  { id = "NL-002"; run }

(* PL-002: PL primary quotes, nested guillemets only *)
let r_pl_002 : rule =
  let run s =
    (* Detect use of « » (French guillemets) at top level *)
    (* « = C2 AB, » = C2 BB, „ = E2 80 9E *)
    let has_guill =
      count_substring s "\xc2\xab" > 0 || count_substring s "\xc2\xbb" > 0
    in
    let has_german = count_substring s "\xe2\x80\x9e" > 0 in
    (* If guillemets present but no German quotes, it's wrong *)
    if has_guill && not has_german then
      Some
        {
          id = "PL-002";
          severity = Info;
          message = {|PL: primary quotes „…”, nested »…« only|};
          count = 1;
        }
    else None
  in
  { id = "PL-002"; run }

(* PT-001: pt-BR pre-2009 spellings forbidden *)
let r_pt_001 : rule =
  let words =
    [
      "ac\xc3\xa7\xc3\xa3o";
      "\xc3\xb3ptimo";
      "direc\xc3\xa7\xc3\xa3o";
      "objec\xc3\xa7\xc3\xa3o";
      "projec\xc3\xa7\xc3\xa3o";
      "colec\xc3\xa7\xc3\xa3o";
      "selec\xc3\xa7\xc3\xa3o";
      "correc\xc3\xa7\xc3\xa3o";
      "protec\xc3\xa7\xc3\xa3o";
    ]
  in
  let run s =
    let s_low = String.lowercase_ascii s in
    let cnt =
      List.fold_left (fun acc w -> acc + count_substring s_low w) 0 words
    in
    if cnt > 0 then
      Some
        {
          id = "PT-001";
          severity = Warning;
          message = {|pt‑BR: pre‑2009 spellings “acção”, “óptimo” forbidden|};
          count = cnt;
        }
    else None
  in
  { id = "PT-001"; run }

(* RU-002: RU letter ё must be preserved where needed *)
let r_ru_002 : rule =
  (* Common words where ё (D1 91) is often incorrectly replaced by е (D0 B5) *)
  (* We check for known words with е where ё is mandatory *)
  let run s =
    (* Check for ё present — if present the author is ё-aware *)
    let has_yo = count_substring s "\xd1\x91" > 0 in
    if not has_yo then None
    else
      (* Author uses ё somewhere but may have missed some *)
      (* Common mandatory-ё words written with е: всё, ещё, её *)
      let cnt =
        count_substring s "\xd0\xb5\xd1\x89\xd0\xb5"
        (* еще instead of ещё *)
        + count_substring s "\xd0\xb2\xd1\x81\xd0\xb5 "
        (* все instead of всё *)
      in
      if cnt > 0 then
        Some
          {
            id = "RU-002";
            severity = Info;
            message = {|RU: letter ё must be preserved where needed|};
            count = cnt;
          }
      else None
  in
  { id = "RU-002"; run }

(* TR-001: TR dotless/dotted I mapping error *)
let r_tr_001 : rule =
  (* Detect mixing of Turkish İ/ı with ASCII I/i in Turkish context *)
  (* Turkish İ U+0130 = C4 B0, Turkish ı U+0131 = C4 B1 *)
  let run s =
    let has_turkish_i = count_substring s "\xc4\xb0" > 0 in
    let has_turkish_dotless = count_substring s "\xc4\xb1" > 0 in
    if has_turkish_i || has_turkish_dotless then (
      (* Check for ASCII I where İ expected or i where ı expected *)
      (* Simple heuristic: if Turkish chars present, flag ASCII I/i near them *)
      let cnt = ref 0 in
      let len = String.length s in
      let i = ref 0 in
      while !i < len - 1 do
        let b0 = Char.code (String.unsafe_get s !i) in
        if b0 = 0xc4 then (
          let b1 = Char.code (String.unsafe_get s (!i + 1)) in
          if b1 = 0xb0 || b1 = 0xb1 then (
            (* Turkish İ/ı found, check adjacent ASCII *)
            (if !i >= 1 then
               let prev = String.unsafe_get s (!i - 1) in
               if prev = 'I' || prev = 'i' then incr cnt);
            if !i + 2 < len then
              let next = String.unsafe_get s (!i + 2) in
              if next = 'I' || next = 'i' then incr cnt);
          i := !i + 2)
        else i := !i + 1
      done;
      if !cnt > 0 then
        Some
          {
            id = "TR-001";
            severity = Warning;
            message = {|TR: dotless/dotted I mapping error|};
            count = !cnt;
          }
      else None)
    else None
  in
  { id = "TR-001"; run }

(* ZH-002: ZH-Hant quotes must be 「…」 or 『…』 consistently *)
let r_zh_002 : rule =
  let run s =
    (* 「 = E3 80 8C, 」 = E3 80 8D, 『 = E3 80 8E, 』 = E3 80 8F *)
    let has_cjk_corner =
      count_substring s "\xe3\x80\x8c" > 0
      || count_substring s "\xe3\x80\x8d" > 0
    in
    let has_cjk_white =
      count_substring s "\xe3\x80\x8e" > 0
      || count_substring s "\xe3\x80\x8f" > 0
    in
    (* Also check for western curly quotes mixed in with CJK quotes *)
    let has_western =
      count_substring s "\xe2\x80\x9c" > 0
      || count_substring s "\xe2\x80\x9d" > 0
    in
    if (has_cjk_corner || has_cjk_white) && has_western then
      Some
        {
          id = "ZH-002";
          severity = Info;
          message = {|ZH‑Hant: quotes must be 「…」 or 『…』 consistently|};
          count = 1;
        }
    else None
  in
  { id = "ZH-002"; run }

(* VERB-014: Code block inside caption *)
let r_verb_014 : rule =
  let run s =
    (* Detect \begin{lstlisting} or \begin{verbatim} or \verb inside \caption *)
    let cnt = ref 0 in
    let len = String.length s in
    (* Find \caption{ and check for code blocks within *)
    let cap = "\\caption{" in
    let cap_len = String.length cap in
    let i = ref 0 in
    while !i < len - cap_len do
      if try String.sub s !i cap_len = cap with Invalid_argument _ -> false
      then (
        (* Find matching close brace, accounting for nesting *)
        let depth = ref 1 in
        let j = ref (!i + cap_len) in
        let found_code = ref false in
        while !j < len && !depth > 0 do
          if s.[!j] = '{' then incr depth else if s.[!j] = '}' then decr depth;
          (* Check for code block markers *)
          if
            !j + 17 < len
            &&
            try String.sub s !j 17 = "\\begin{lstlisting"
            with Invalid_argument _ -> false
          then found_code := true;
          if
            !j + 16 < len
            &&
            try String.sub s !j 16 = "\\begin{verbatim}"
            with Invalid_argument _ -> false
          then found_code := true;
          if
            !j + 5 < len
            &&
            try String.sub s !j 5 = "\\verb" with Invalid_argument _ -> false
          then found_code := true;
          incr j
        done;
        if !found_code then incr cnt;
        i := !j)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "VERB-014";
          severity = Warning;
          message = {|Code block inside caption|};
          count = !cnt;
        }
    else None
  in
  { id = "VERB-014"; run }

(* MATH-064: Use of \eqalign — obsolete *)
let r_math_064 : rule =
  let run s =
    let cnt = count_substring s "\\eqalign" in
    if cnt > 0 then
      Some
        {
          id = "MATH-064";
          severity = Warning;
          message = {esc|Use of \eqalign – obsolete|esc};
          count = cnt;
        }
    else None
  in
  { id = "MATH-064"; run }

(* MATH-102: Legacy eqnarray (un-starred) environment present *)
let r_math_102 : rule =
  let run s =
    let cnt = count_substring s "\\begin{eqnarray}" in
    if cnt > 0 then
      Some
        {
          id = "MATH-102";
          severity = Warning;
          message = {|Legacy eqnarray (un‑starred) environment present|};
          count = cnt;
        }
    else None
  in
  { id = "MATH-102"; run }

(* MATH-107: Mix of \le and \leqslant within same document *)
let r_math_107 : rule =
  let run s =
    let has_le =
      count_substring s "\\le " > 0 || count_substring s "\\le\\" > 0
    in
    let has_leqslant = count_substring s "\\leqslant" > 0 in
    if has_le && has_leqslant then
      Some
        {
          id = "MATH-107";
          severity = Info;
          message = {|Mix of \le and \leqslant within same document|};
          count = 1;
        }
    else None
  in
  { id = "MATH-107"; run }

(* L3-008: Expl3 module lacks \ProvidesExplPackage *)
let r_l3_008 : rule =
  let run s =
    let has_expl3 = count_substring s "\\ExplSyntaxOn" > 0 in
    let has_provides = count_substring s "\\ProvidesExplPackage" > 0 in
    if has_expl3 && not has_provides then
      Some
        {
          id = "L3-008";
          severity = Warning;
          message = {|Expl3 module lacks \ProvidesExplPackage|};
          count = 1;
        }
    else None
  in
  { id = "L3-008"; run }

(* L3-010: \ExplSyntaxOff missing at end of file *)
let r_l3_010 : rule =
  let run s =
    let has_on = count_substring s "\\ExplSyntaxOn" > 0 in
    let has_off = count_substring s "\\ExplSyntaxOff" > 0 in
    if has_on && not has_off then
      Some
        {
          id = "L3-010";
          severity = Info;
          message = {|\ExplSyntaxOff missing at end of file|};
          count = 1;
        }
    else None
  in
  { id = "L3-010"; run }

(* REF-011: \autoref used without hyperref/cleveref loaded *)
let r_ref_011 : rule =
  let run s =
    let has_autoref = count_substring s "\\autoref" > 0 in
    let has_hyperref =
      count_substring s "\\usepackage{hyperref}" > 0
      || count_substring s "\\usepackage[" > 0
         && count_substring s "hyperref" > 0
    in
    let has_cleveref =
      count_substring s "\\usepackage{cleveref}" > 0
      || count_substring s "cleveref" > 0
    in
    if has_autoref && (not has_hyperref) && not has_cleveref then
      Some
        {
          id = "REF-011";
          severity = Error;
          message = {|\autoref used without hyperref/cleveref loaded|};
          count = count_substring s "\\autoref";
        }
    else None
  in
  { id = "REF-011"; run }

(* TYPO-050: Inconsistent title-case capitalisation *)
let r_typo_050 : rule =
  (* Detect \section{} and \subsection{} with inconsistent capitalisation *)
  let re_sec =
    Str.regexp
      {|\\section\*?\{[^}]+\}\|\\subsection\*?\{[^}]+\}\|\\chapter\*?\{[^}]+\}|}
  in
  let run s =
    let titles = ref [] in
    let start = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re_sec s !start in
         let m = Str.matched_string s in
         titles := m :: !titles;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if List.length !titles < 2 then None
    else
      (* Check if some are title-case and some are sentence-case *)
      let is_title_case t =
        (* Extract content between { and } *)
        let i = try String.index t '{' + 1 with Not_found -> 0 in
        let j = try String.rindex t '}' with Not_found -> String.length t in
        if j <= i then false
        else
          let content = String.sub t i (j - i) in
          let words = String.split_on_char ' ' content in
          let sig_words =
            List.filter
              (fun w ->
                String.length w > 3
                && w.[0] <> '\\'
                && w <> "and"
                && w <> "the"
                && w <> "for"
                && w <> "with")
              words
          in
          List.length sig_words > 0
          && List.for_all
               (fun w ->
                 let c = Char.code w.[0] in
                 c >= 65 && c <= 90)
               sig_words
      in
      let tc_count = List.length (List.filter is_title_case !titles) in
      let total = List.length !titles in
      let sc_count = total - tc_count in
      if tc_count > 0 && sc_count > 0 then
        Some
          {
            id = "TYPO-050";
            severity = Info;
            message = {|Inconsistent title‑case capitalisation|};
            count = 1;
          }
      else None
  in
  { id = "TYPO-050"; run }

let rules_stragglers : rule list =
  [
    r_cy_001;
    r_de_006;
    r_nl_001;
    r_nl_002;
    r_pl_002;
    r_pt_001;
    r_ru_002;
    r_tr_001;
    r_zh_002;
    r_verb_014;
    r_math_064;
    r_math_102;
    r_math_107;
    r_l3_008;
    r_l3_010;
    r_ref_011;
    r_typo_050;
  ]
