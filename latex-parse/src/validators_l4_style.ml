(* ══════════════════════════════════════════════════════════════════════
   Validators_l4_style — L4 style rules (text-scannable approximations)

   Phase 1 batch: 25 rules (STYLE-004..049), all Info severity.
   These rules operate on strip_math_segments output so they ignore
   math-mode content.
   ══════════════════════════════════════════════════════════════════════ *)

open Validators_common

(* ── Helpers ────────────────────────────────────────────────────────── *)

(** Strip LaTeX comments (lines starting with % or inline % not preceded
    by \\). *)
let strip_comments (s : string) : string =
  let lines = String.split_on_char '\n' s in
  let strip_line l =
    let len = String.length l in
    let rec find i =
      if i >= len then l
      else if l.[i] = '%' then
        if i = 0 then ""
        else if l.[i - 1] <> '\\' then String.sub l 0 i
        else find (i + 1)
      else find (i + 1)
    in
    find 0
  in
  String.concat "\n" (List.map strip_line lines)

(** Rough sentence split: split on ". " followed by uppercase or end.
    Returns list of sentence strings. *)
let sentence_split (s : string) : string list =
  let len = String.length s in
  let buf = Buffer.create 256 in
  let acc = ref [] in
  let rec loop i =
    if i >= len then (
      let cur = Buffer.contents buf in
      if String.length (String.trim cur) > 0 then acc := cur :: !acc)
    else if
      s.[i] = '.'
      && i + 2 < len
      && s.[i + 1] = ' '
      && let c = s.[i + 2] in
         c >= 'A' && c <= 'Z'
    then (
      Buffer.add_char buf '.';
      let cur = Buffer.contents buf in
      if String.length (String.trim cur) > 0 then acc := cur :: !acc;
      Buffer.clear buf;
      loop (i + 2))
    else (
      Buffer.add_char buf s.[i];
      loop (i + 1))
  in
  loop 0;
  List.rev !acc

(** Count words in a string (split on whitespace). *)
let word_count (s : string) : int =
  let s = String.trim s in
  if String.length s = 0 then 0
  else
    let cnt = ref 1 in
    let in_ws = ref false in
    String.iter
      (fun c ->
        if c = ' ' || c = '\t' || c = '\n' || c = '\r' then (
          if not !in_ws then incr cnt;
          in_ws := true)
        else in_ws := false)
      s;
    !cnt

(** Extract the body content of \\section{...}, \\subsection{...} etc. *)
let extract_heading_titles (s : string) : string list =
  let re =
    Str.regexp
      {|\\[sub]*section\*?[ \t\n]*\(\[[^]]*\][ \t\n]*\)?\{|}
  in
  let acc = ref [] in
  let len = String.length s in
  let rec find start =
    match
      (try Some (Str.search_forward re s start) with Not_found -> None)
    with
    | None -> ()
    | Some _pos ->
        let mend = Str.match_end () in
        (* find the matching closing brace *)
        let depth = ref 1 in
        let j = ref mend in
        while !j < len && !depth > 0 do
          (match s.[!j] with
          | '{' -> incr depth
          | '}' -> decr depth
          | _ -> ());
          if !depth > 0 then incr j
        done;
        if !depth = 0 then
          acc := String.sub s mend (!j - mend) :: !acc;
        find (!j + 1)
  in
  find 0;
  List.rev !acc

(** Split text into paragraphs (separated by blank lines). *)
let split_paragraphs (s : string) : string list =
  let re = Str.regexp "\n[ \t]*\n" in
  let parts = Str.split re s in
  List.filter (fun p -> String.length (String.trim p) > 0) parts

(** First word of a sentence after trimming. *)
let first_word (s : string) : string =
  let s = String.trim s in
  match String.index_opt s ' ' with
  | Some i -> String.sub s 0 i
  | None -> s

(* ── Rules ──────────────────────────────────────────────────────────── *)

(* STYLE-004: Paragraph exceeds 300 words *)
let r_style_004 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let paras = split_paragraphs text in
    let cnt =
      List.fold_left
        (fun acc p -> if word_count p > 300 then acc + 1 else acc)
        0 paras
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-004";
          severity = Info;
          message = "Paragraph exceeds 300 words";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-004"; run }

(* STYLE-006: Consecutive sentences start with same word *)
let r_style_006 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let sents = sentence_split text in
    let rec check cnt = function
      | [] | [ _ ] -> cnt
      | a :: ((b :: _) as rest) ->
          let wa = String.lowercase_ascii (first_word a) in
          let wb = String.lowercase_ascii (first_word b) in
          let cnt =
            if String.length wa > 0 && wa = wb then cnt + 1 else cnt
          in
          check cnt rest
    in
    let cnt = check 0 sents in
    if cnt > 0 then
      Some
        {
          id = "STYLE-006";
          severity = Info;
          message = "Consecutive sentences start with same word";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-006"; run }

(* STYLE-008: Sentence starts with mathematical symbol *)
let r_style_008 : rule =
  let re = Str.regexp {|\. \$\|^\$|} in
  let run s =
    let text = strip_comments s in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-008";
          severity = Info;
          message = "Sentence starts with mathematical symbol";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-008"; run }

(* STYLE-013: Sentence starts with numeric figure *)
let r_style_013 : rule =
  let re = Str.regexp {|\. +[0-9]|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-013";
          severity = Info;
          message = "Sentence starts with numeric figure";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-013"; run }

(* STYLE-014: Contraction (don't, isn't) in formal text *)
let r_style_014 : rule =
  let contractions =
    [
      "don't"; "doesn't"; "didn't"; "isn't"; "aren't"; "wasn't"; "weren't";
      "won't"; "wouldn't"; "couldn't"; "shouldn't"; "can't"; "haven't";
      "hasn't"; "hadn't"; "it's"; "that's"; "there's"; "they're"; "we're";
      "you're"; "let's"; "who's"; "what's";
    ]
  in
  let run s =
    let text =
      String.lowercase_ascii (strip_comments (strip_math_segments s))
    in
    let cnt =
      List.fold_left
        (fun acc c ->
          let n = count_substring text c in
          acc + n)
        0 contractions
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-014";
          severity = Info;
          message = "Contraction in formal text";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-014"; run }

(* STYLE-015: Double space after period *)
let r_style_015 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let cnt = count_substring text ".  " in
    if cnt > 0 then
      Some
        {
          id = "STYLE-015";
          severity = Info;
          message = "Double space after period";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-015"; run }

(* STYLE-016: Latin abbreviation (e.g., i.e.) missing comma *)
let r_style_016 : rule =
  let re = Str.regexp {|[ei]\.g\.\([^,]\)\|i\.e\.\([^,]\)|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-016";
          severity = Info;
          message =
            "Latin abbreviation (e.g., i.e.) missing comma after abbreviation";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-016"; run }

(* STYLE-017: Sentence exceeds 40 words *)
let r_style_017 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let sents = sentence_split text in
    let cnt =
      List.fold_left
        (fun acc sent -> if word_count sent > 40 then acc + 1 else acc)
        0 sents
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-017";
          severity = Info;
          message = "Sentence exceeds 40 words";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-017"; run }

(* STYLE-019: Multiple consecutive headings without intervening text *)
let r_style_019 : rule =
  let heading_re =
    Str.regexp {|\\[sub]*section\*?[ \t\n]*\({[^}]*}\)|}
  in
  let run s =
    let text = strip_comments s in
    (* Find all heading positions *)
    let positions = ref [] in
    let start = ref 0 in
    (try
       while true do
         let pos = Str.search_forward heading_re text !start in
         positions := pos :: !positions;
         start := Str.match_end ()
       done
     with Not_found -> ());
    let positions = List.rev !positions in
    (* Check consecutive pairs for intervening non-whitespace text *)
    let rec check cnt = function
      | [] | [ _ ] -> cnt
      | a :: ((b :: _) as rest) ->
          (* Find end of first heading *)
          ignore (Str.search_forward heading_re text a);
          let a_end = Str.match_end () in
          (* Check if text between a_end and b is only whitespace *)
          let between = String.sub text a_end (b - a_end) in
          let trimmed = String.trim between in
          let cnt =
            if String.length trimmed = 0 then cnt + 1 else cnt
          in
          check cnt rest
    in
    let cnt = check 0 positions in
    if cnt > 0 then
      Some
        {
          id = "STYLE-019";
          severity = Info;
          message = "Multiple consecutive headings without intervening text";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-019"; run }

(* STYLE-023: Percent sign in text not escaped *)
let r_style_023 : rule =
  let run s =
    let text = strip_math_segments s in
    let len = String.length text in
    let cnt = ref 0 in
    for i = 0 to len - 1 do
      if text.[i] = '%' then
        if i = 0 || text.[i - 1] <> '\\' then incr cnt
    done;
    if !cnt > 0 then
      Some
        {
          id = "STYLE-023";
          severity = Info;
          message = "Percent sign in text not escaped";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-023"; run }

(* STYLE-024: Ampersand in text not escaped *)
let r_style_024 : rule =
  let run s =
    let text = strip_math_segments s in
    (* skip tabular / align environments *)
    let in_tabular = contains_substring s "\\begin{tabular}" in
    let in_align = contains_substring s "\\begin{align" in
    if in_tabular || in_align then None
    else
      let len = String.length text in
      let cnt = ref 0 in
      for i = 0 to len - 1 do
        if text.[i] = '&' then
          if i = 0 || text.[i - 1] <> '\\' then incr cnt
      done;
      if !cnt > 0 then
        Some
          {
            id = "STYLE-024";
            severity = Info;
            message = "Ampersand in text not escaped";
            count = !cnt;
          }
      else None
  in
  { id = "STYLE-024"; run }

(* STYLE-026: Repeated word (the the) *)
let r_style_026 : rule =
  let run s =
    let text =
      String.lowercase_ascii (strip_comments (strip_math_segments s))
    in
    let words =
      Str.split (Str.regexp "[ \t\n\r]+") text
    in
    let rec check cnt = function
      | [] | [ _ ] -> cnt
      | a :: ((b :: _) as rest) ->
          let cnt =
            if String.length a > 1 && a = b then cnt + 1 else cnt
          in
          check cnt rest
    in
    let cnt = check 0 words in
    if cnt > 0 then
      Some
        {
          id = "STYLE-026";
          severity = Info;
          message = "Repeated word detected";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-026"; run }

(* STYLE-030: Sub-heading capitalisation inconsistent *)
let r_style_030 : rule =
  let is_titlecase s =
    let words =
      List.filter
        (fun w -> String.length w > 3)
        (String.split_on_char ' ' s)
    in
    List.for_all
      (fun w ->
        let c = w.[0] in
        c >= 'A' && c <= 'Z')
      words
  in
  let is_sentencecase s =
    let s = String.trim s in
    if String.length s = 0 then true
    else
      let c = s.[0] in
      c >= 'A' && c <= 'Z'
  in
  let run s =
    let titles = extract_heading_titles s in
    if List.length titles < 2 then None
    else
      let tc_count =
        List.fold_left
          (fun acc t -> if is_titlecase t then acc + 1 else acc)
          0 titles
      in
      let sc_count =
        List.fold_left
          (fun acc t ->
            if (not (is_titlecase t)) && is_sentencecase t then acc + 1
            else acc)
          0 titles
      in
      if tc_count > 0 && sc_count > 0 then
        Some
          {
            id = "STYLE-030";
            severity = Info;
            message = "Sub-heading capitalisation inconsistent";
            count = min tc_count sc_count;
          }
      else None
  in
  { id = "STYLE-030"; run }

(* STYLE-031: Heading number without title *)
let r_style_031 : rule =
  let re = Str.regexp {|\\[sub]*section\*?\s*{[0-9. ]*}|} in
  let run s =
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-031";
          severity = Info;
          message = "Heading contains only numbers without title text";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-031"; run }

(* STYLE-033: Space before citation bracket *)
let r_style_033 : rule =
  let re = Str.regexp {| \\cite[^a-zA-Z]|} in
  let run s =
    let text = strip_comments s in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         (* check it's not a tilde ~ before \cite *)
         let pos = Str.match_beginning () in
         if pos = 0 || text.[pos - 1] <> '~' then incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-033";
          severity = Info;
          message = "Space before \\cite — use ~ (non-breaking space)";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-033"; run }

(* STYLE-034: Orphan word (1-2 letters) at paragraph end *)
let r_style_034 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let paras = split_paragraphs text in
    let cnt =
      List.fold_left
        (fun acc p ->
          let trimmed = String.trim p in
          let words = String.split_on_char ' ' trimmed in
          match List.rev words with
          | last :: _ ->
              if String.length last > 0 && String.length last <= 2 then
                acc + 1
              else acc
          | [] -> acc)
        0 paras
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-034";
          severity = Info;
          message = "Orphan word (1-2 letters) at paragraph end";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-034"; run }

(* STYLE-035: Slash used for 'and/or' *)
let r_style_035 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let cnt = count_substring text "and/or" in
    if cnt > 0 then
      Some
        {
          id = "STYLE-035";
          severity = Info;
          message = "Slash used for 'and/or'";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-035"; run }

(* STYLE-036: Latin phrase (cf., ibid.) not italicised *)
let r_style_036 : rule =
  let phrases = [ "cf."; "ibid."; "et al."; "viz."; "e.g."; "i.e." ] in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let cnt =
      List.fold_left
        (fun acc phrase ->
          (* count occurrences not inside \emph or \textit *)
          let n = count_substring text phrase in
          let n_emph =
            count_substring text ("\\emph{" ^ phrase)
            + count_substring text ("\\textit{" ^ phrase)
          in
          acc + max 0 (n - n_emph))
        0 phrases
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-036";
          severity = Info;
          message = "Latin phrase not italicised";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-036"; run }

(* STYLE-037: Sentence starts with conjunction 'And' or 'But' *)
let r_style_037 : rule =
  let re = Str.regexp {|\. +\(And\|But\) +|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-037";
          severity = Info;
          message = "Sentence starts with conjunction 'And' or 'But'";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-037"; run }

(* STYLE-040: Exclamation mark in academic prose *)
let r_style_040 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let cnt = count_char text '!' in
    if cnt > 0 then
      Some
        {
          id = "STYLE-040";
          severity = Info;
          message = "Exclamation mark in academic prose";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-040"; run }

(* STYLE-042: Consecutive short paragraphs (< 15 words) *)
let r_style_042 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let paras = split_paragraphs text in
    let rec check cnt = function
      | [] | [ _ ] -> cnt
      | a :: ((b :: _) as rest) ->
          let cnt =
            if word_count a < 15 && word_count b < 15 then cnt + 1 else cnt
          in
          check cnt rest
    in
    let cnt = check 0 paras in
    if cnt > 0 then
      Some
        {
          id = "STYLE-042";
          severity = Info;
          message = "Consecutive short paragraphs (< 15 words each)";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-042"; run }

(* STYLE-045: Excess parentheses in single sentence (> 3) *)
let r_style_045 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let sents = sentence_split text in
    let cnt =
      List.fold_left
        (fun acc sent ->
          let n = count_char sent '(' in
          if n > 3 then acc + 1 else acc)
        0 sents
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-045";
          severity = Info;
          message = "Excess parentheses in single sentence (> 3)";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-045"; run }

(* STYLE-046: Mixed en-dash and em-dash in same sentence *)
let r_style_046 : rule =
  let en_dash = "\xe2\x80\x93" in
  (* U+2013 *)
  let em_dash = "\xe2\x80\x94" in
  (* U+2014 *)
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let sents = sentence_split text in
    let cnt =
      List.fold_left
        (fun acc sent ->
          if contains_substring sent en_dash && contains_substring sent em_dash
          then acc + 1
          else acc)
        0 sents
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-046";
          severity = Info;
          message = "Mixed en-dash and em-dash in same sentence";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-046"; run }

(* STYLE-048: Word-pair variant 'among/amongst', 'while/whilst' mixed *)
let r_style_048 : rule =
  let pairs = [ ("among", "amongst"); ("while", "whilst") ] in
  let run s =
    let text =
      String.lowercase_ascii (strip_comments (strip_math_segments s))
    in
    let cnt =
      List.fold_left
        (fun acc (a, b) ->
          if contains_substring text a && contains_substring text b then
            acc + 1
          else acc)
        0 pairs
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-048";
          severity = Info;
          message = "Word-pair variant mixed (e.g. among/amongst)";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-048"; run }

(* STYLE-049: Section heading ends with colon *)
let r_style_049 : rule =
  let run s =
    let titles = extract_heading_titles s in
    let cnt =
      List.fold_left
        (fun acc t ->
          let t = String.trim t in
          if String.length t > 0 && t.[String.length t - 1] = ':' then
            acc + 1
          else acc)
        0 titles
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-049";
          severity = Info;
          message = "Section heading ends with colon";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-049"; run }

(* ── Exported rules list ────────────────────────────────────────────── *)

let rules_style : rule list =
  [
    r_style_004;
    r_style_006;
    r_style_008;
    r_style_013;
    r_style_014;
    r_style_015;
    r_style_016;
    r_style_017;
    r_style_019;
    r_style_023;
    r_style_024;
    r_style_026;
    r_style_030;
    r_style_031;
    r_style_033;
    r_style_034;
    r_style_035;
    r_style_036;
    r_style_037;
    r_style_040;
    r_style_042;
    r_style_045;
    r_style_046;
    r_style_048;
    r_style_049;
  ]
