(* ══════════════════════════════════════════════════════════════════════
   Validators_l4_style — L4 style rules (text-scannable approximations)

   Phase 1 batch: 25 rules (STYLE-004..049), all Info severity. These rules
   operate on strip_math_segments output so they ignore math-mode content.
   ══════════════════════════════════════════════════════════════════════ *)

open Validators_common

(* ── Helpers ────────────────────────────────────────────────────────── *)

(** Strip LaTeX comments (lines starting with % or inline % not preceded by \\). *)
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

(** Rough sentence split: split on ". " followed by uppercase or end. Returns
    list of sentence strings. *)
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
      &&
      let c = s.[i + 2] in
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
  let re = Str.regexp {|\\[sub]*section\*?[ \t\n]*\(\[[^]]*\][ \t\n]*\)?\{|} in
  let acc = ref [] in
  let len = String.length s in
  let rec find start =
    match try Some (Str.search_forward re s start) with Not_found -> None with
    | None -> ()
    | Some _pos ->
        let mend = Str.match_end () in
        (* find the matching closing brace *)
        let depth = ref 1 in
        let j = ref mend in
        while !j < len && !depth > 0 do
          (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
          if !depth > 0 then incr j
        done;
        if !depth = 0 then acc := String.sub s mend (!j - mend) :: !acc;
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
  match String.index_opt s ' ' with Some i -> String.sub s 0 i | None -> s

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
      | a :: (b :: _ as rest) ->
          let wa = String.lowercase_ascii (first_word a) in
          let wb = String.lowercase_ascii (first_word b) in
          let cnt = if String.length wa > 0 && wa = wb then cnt + 1 else cnt in
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
      "don't";
      "doesn't";
      "didn't";
      "isn't";
      "aren't";
      "wasn't";
      "weren't";
      "won't";
      "wouldn't";
      "couldn't";
      "shouldn't";
      "can't";
      "haven't";
      "hasn't";
      "hadn't";
      "it's";
      "that's";
      "there's";
      "they're";
      "we're";
      "you're";
      "let's";
      "who's";
      "what's";
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
  let heading_re = Str.regexp {|\\[sub]*section\*?[ \t\n]*\({[^}]*}\)|} in
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
      | a :: (b :: _ as rest) ->
          (* Find end of first heading *)
          ignore (Str.search_forward heading_re text a);
          let a_end = Str.match_end () in
          (* Check if text between a_end and b is only whitespace *)
          let between = String.sub text a_end (b - a_end) in
          let trimmed = String.trim between in
          let cnt = if String.length trimmed = 0 then cnt + 1 else cnt in
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
      if text.[i] = '%' then if i = 0 || text.[i - 1] <> '\\' then incr cnt
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
        if text.[i] = '&' then if i = 0 || text.[i - 1] <> '\\' then incr cnt
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
    let words = Str.split (Str.regexp "[ \t\n\r]+") text in
    let rec check cnt = function
      | [] | [ _ ] -> cnt
      | a :: (b :: _ as rest) ->
          let cnt = if String.length a > 1 && a = b then cnt + 1 else cnt in
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
      List.filter (fun w -> String.length w > 3) (String.split_on_char ' ' s)
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
            if (not (is_titlecase t)) && is_sentencecase t then acc + 1 else acc)
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
              if String.length last > 0 && String.length last <= 2 then acc + 1
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
      | a :: (b :: _ as rest) ->
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
          if contains_substring text a && contains_substring text b then acc + 1
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
          if String.length t > 0 && t.[String.length t - 1] = ':' then acc + 1
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

(* ══════════════════════════════════════════════════════════════════════ Phase
   2 batch: 14 more STYLE rules + 10 locale/LANG rules
   ══════════════════════════════════════════════════════════════════════ *)

(* STYLE-001: Inconsistent Oxford-comma usage *)
let r_style_001 : rule =
  let re_oxford = Str.regexp {|, [a-zA-Z]+, and |} in
  let re_no_oxford = Str.regexp {|, [a-zA-Z]+ and |} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let has_oxford =
      try
        ignore (Str.search_forward re_oxford text 0);
        true
      with Not_found -> false
    in
    let has_no_oxford =
      try
        ignore (Str.search_forward re_no_oxford text 0);
        true
      with Not_found -> false
    in
    if has_oxford && has_no_oxford then
      Some
        {
          id = "STYLE-001";
          severity = Info;
          message = "Inconsistent Oxford-comma usage";
          count = 1;
        }
    else None
  in
  { id = "STYLE-001"; run }

(* STYLE-002: Mixed UK and US spelling *)
let r_style_002 : rule =
  let pairs =
    [
      ("colour", "color");
      ("favour", "favor");
      ("honour", "honor");
      ("labour", "labor");
      ("analyse", "analyze");
      ("organise", "organize");
      ("realise", "realize");
      ("defence", "defense");
      ("licence", "license");
      ("centre", "center");
      ("metre", "meter");
      ("programme", "program");
    ]
  in
  let run s =
    let text =
      String.lowercase_ascii (strip_comments (strip_math_segments s))
    in
    let cnt =
      List.fold_left
        (fun acc (uk, us) ->
          if contains_substring text uk && contains_substring text us then
            acc + 1
          else acc)
        0 pairs
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-002";
          severity = Info;
          message = "Mixed UK and US spelling detected";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-002"; run }

(* STYLE-005: First-person 'we' inconsistent with 'I' *)
let r_style_005 : rule =
  let re_we = Str.regexp {|\bwe \|We |} in
  let re_i = Str.regexp {| I \| I,\| I\.|^I |} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let has_we =
      try
        ignore (Str.search_forward re_we text 0);
        true
      with Not_found -> false
    in
    let has_i =
      try
        ignore (Str.search_forward re_i text 0);
        true
      with Not_found -> false
    in
    if has_we && has_i then
      Some
        {
          id = "STYLE-005";
          severity = Info;
          message = "First-person pronoun inconsistent (mixed 'we' and 'I')";
          count = 1;
        }
    else None
  in
  { id = "STYLE-005"; run }

(* STYLE-007: Bullet-list items inconsistent punctuation *)
let r_style_007 : rule =
  let re_item = Str.regexp {|\\item\([^\\]*\)|} in
  let run s =
    let text = strip_comments s in
    let items = ref [] in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re_item text !start);
         let body = String.trim (Str.matched_group 1 text) in
         if String.length body > 0 then items := body :: !items;
         start := Str.match_end ()
       done
     with Not_found -> ());
    let items = !items in
    if List.length items < 2 then None
    else
      let ends_with_punct s =
        let c = s.[String.length s - 1] in
        c = '.' || c = ';' || c = ','
      in
      let with_p =
        List.fold_left
          (fun acc it -> if ends_with_punct it then acc + 1 else acc)
          0 items
      in
      let without_p = List.length items - with_p in
      if with_p > 0 && without_p > 0 then
        Some
          {
            id = "STYLE-007";
            severity = Info;
            message = "Bullet-list items have inconsistent punctuation";
            count = min with_p without_p;
          }
      else None
  in
  { id = "STYLE-007"; run }

(* STYLE-009: Citation style mixes parenthetical and narrative *)
let r_style_009 : rule =
  let run s =
    let text = strip_comments s in
    let has_cite = contains_substring text "\\cite{" in
    let has_citep =
      contains_substring text "\\citep{"
      || contains_substring text "\\parencite{"
    in
    let has_citet =
      contains_substring text "\\citet{"
      || contains_substring text "\\textcite{"
    in
    if has_cite && (has_citep || has_citet) then
      Some
        {
          id = "STYLE-009";
          severity = Info;
          message = "Mixed citation styles (\\cite with \\citep/\\citet)";
          count = 1;
        }
    else None
  in
  { id = "STYLE-009"; run }

(* STYLE-010: First-person singular 'I' in multi-author paper *)
let r_style_010 : rule =
  let re_i = Str.regexp {| I \| I,\| I\.|^I |} in
  let re_multi = Str.regexp {|\\author{[^}]*and[^}]*}|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let multi =
      try
        ignore (Str.search_forward re_multi s 0);
        true
      with Not_found -> false
    in
    let has_i =
      try
        ignore (Str.search_forward re_i text 0);
        true
      with Not_found -> false
    in
    if multi && has_i then
      Some
        {
          id = "STYLE-010";
          severity = Info;
          message = "First-person 'I' in multi-author paper";
          count = 1;
        }
    else None
  in
  { id = "STYLE-010"; run }

(* STYLE-011: Hyphen vs en-dash inconsistency in ranges *)
let r_style_011 : rule =
  let re_hyphen_range = Str.regexp {|[0-9]-[0-9]|} in
  let re_endash_range = Str.regexp {|[0-9]--[0-9]|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let has_hyphen =
      try
        ignore (Str.search_forward re_hyphen_range text 0);
        true
      with Not_found -> false
    in
    let has_endash =
      try
        ignore (Str.search_forward re_endash_range text 0);
        true
      with Not_found -> false
    in
    if has_hyphen && has_endash then
      Some
        {
          id = "STYLE-011";
          severity = Info;
          message = "Hyphen vs en-dash inconsistency in number ranges";
          count = 1;
        }
    else None
  in
  { id = "STYLE-011"; run }

(* STYLE-018: Dangling reference word 'this' *)
let r_style_018 : rule =
  let re =
    Str.regexp {|[Tt]his \(is\|was\|has\|shows\|suggests\|means\|implies\) |}
  in
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
          id = "STYLE-018";
          severity = Info;
          message = "Dangling 'this' without noun";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-018"; run }

(* STYLE-020: Acronym defined but never used *)
let r_style_020 : rule =
  let re_def = Str.regexp {|(\([A-Z][A-Z]+\))|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let defs = ref [] in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re_def text !start);
         let acr = Str.matched_group 1 text in
         defs := acr :: !defs;
         start := Str.match_end ()
       done
     with Not_found -> ());
    let cnt =
      List.fold_left
        (fun acc acr ->
          (* Count uses outside the definition *)
          let n = count_substring text acr in
          (* Subtract 1 for the definition itself *)
          if n <= 1 then acc + 1 else acc)
        0 !defs
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-020";
          severity = Info;
          message = "Acronym defined but never used";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-020"; run }

(* STYLE-021: Acronym used before definition *)
let r_style_021 : rule =
  let re_def = Str.regexp {|(\([A-Z][A-Z]+\))|} in
  let re_acr = Str.regexp {|[^a-zA-Z]\([A-Z][A-Z][A-Z]+\)[^a-zA-Z]|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    (* Find first definition *)
    let first_def_pos = ref max_int in
    let acr_name = ref "" in
    (try
       ignore (Str.search_forward re_def text 0);
       first_def_pos := Str.match_beginning ();
       acr_name := Str.matched_group 1 text
     with Not_found -> ());
    if !first_def_pos = max_int then None
    else
      (* Check if the acronym appears before definition *)
      let used_before =
        try
          let pos = Str.search_forward re_acr text 0 in
          let found = Str.matched_group 1 text in
          pos < !first_def_pos && found = !acr_name
        with Not_found -> false
      in
      if used_before then
        Some
          {
            id = "STYLE-021";
            severity = Info;
            message = "Acronym used before definition";
            count = 1;
          }
      else None
  in
  { id = "STYLE-021"; run }

(* STYLE-022: Serial comma missing in three-item list *)
let r_style_022 : rule =
  let re = Str.regexp {|[a-zA-Z]+, [a-zA-Z]+ and [a-zA-Z]|} in
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
          id = "STYLE-022";
          severity = Info;
          message = "Serial comma missing in three-item list";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-022"; run }

(* STYLE-025: Run-on sentence detected *)
let r_style_025 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let sents = sentence_split text in
    let cnt =
      List.fold_left
        (fun acc sent -> if word_count sent > 60 then acc + 1 else acc)
        0 sents
    in
    if cnt > 0 then
      Some
        {
          id = "STYLE-025";
          severity = Info;
          message = "Run-on sentence detected (> 60 words)";
          count = cnt;
        }
    else None
  in
  { id = "STYLE-025"; run }

(* STYLE-027: Overuse of adverbs (-ly > 5% of words) *)
let r_style_027 : rule =
  let re_ly = Str.regexp {|[a-zA-Z]+ly |} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let total = word_count text in
    if total < 50 then None
    else
      let cnt = ref 0 in
      let start = ref 0 in
      (try
         while true do
           ignore (Str.search_forward re_ly text !start);
           incr cnt;
           start := Str.match_end ()
         done
       with Not_found -> ());
      let ratio = float_of_int !cnt /. float_of_int total in
      if ratio > 0.05 then
        Some
          {
            id = "STYLE-027";
            severity = Info;
            message =
              Printf.sprintf "Overuse of adverbs (%.1f%% -ly words)"
                (ratio *. 100.0);
            count = !cnt;
          }
      else None
  in
  { id = "STYLE-027"; run }

(* STYLE-028: Equation referenced without adjoining punctuation *)
let r_style_028 : rule =
  let re = Str.regexp {|\\eqref{[^}]*} [A-Za-z]|} in
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
          id = "STYLE-028";
          severity = Info;
          message = "Equation reference without adjoining punctuation";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-028"; run }

(* ── Locale / LANG rules ───────────────────────────────────────────── *)

(* CE-001: Canadian EN mixes BrE colour with AmE color *)
let r_ce_001 : rule =
  let pairs =
    [ ("colour", "color"); ("favour", "favor"); ("centre", "center") ]
  in
  let run s =
    let text =
      String.lowercase_ascii (strip_comments (strip_math_segments s))
    in
    let cnt =
      List.fold_left
        (fun acc (uk, us) ->
          if contains_substring text uk && contains_substring text us then
            acc + 1
          else acc)
        0 pairs
    in
    if cnt > 0 then
      Some
        {
          id = "CE-001";
          severity = Info;
          message = "Canadian EN: mixes BrE and AmE spelling";
          count = cnt;
        }
    else None
  in
  { id = "CE-001"; run }

(* CE-002: Canadian EN requires Oxford comma *)
let r_ce_002 : rule =
  let re = Str.regexp {|[a-zA-Z]+, [a-zA-Z]+ and [a-zA-Z]|} in
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
          id = "CE-002";
          severity = Info;
          message = "Canadian EN: Oxford comma must always be used";
          count = !cnt;
        }
    else None
  in
  { id = "CE-002"; run }

(* TH-001: Thai leading vowels at line break need non-breaking space *)
let r_th_001 : rule =
  let run s =
    let lines = String.split_on_char '\n' s in
    let cnt =
      List.fold_left
        (fun acc line ->
          let line = String.trim line in
          if String.length line >= 3 then
            (* Thai leading vowels: U+0E40-0E44 = E0 B9 80..84 *)
            let b0 = Char.code line.[0] in
            let b1 = Char.code line.[1] in
            let b2 = Char.code line.[2] in
            if b0 = 0xe0 && b1 = 0xb9 && b2 >= 0x80 && b2 <= 0x84 then acc + 1
            else acc
          else acc)
        0 lines
    in
    if cnt > 0 then
      Some
        {
          id = "TH-001";
          severity = Info;
          message = "Thai leading vowel at line start needs \\nobreakspace";
          count = cnt;
        }
    else None
  in
  { id = "TH-001"; run }

(* IB-001: Brochure mixes pt-BR 'voce' with es-ES 'tu' *)
let r_ib_001 : rule =
  let voce = "voc\xc3\xaa" in
  (* U+00EA = ê *)
  let run s =
    let text = String.lowercase_ascii (strip_comments s) in
    let has_voce = contains_substring text voce in
    let has_tu =
      contains_substring text " tu " || contains_substring text " t\xc3\xba "
    in
    if has_voce && has_tu then
      Some
        {
          id = "IB-001";
          severity = Info;
          message = {|Brochure mixes pt-BR 'você' with es-ES 'tú'|};
          count = 1;
        }
    else None
  in
  { id = "IB-001"; run }

(* LANG-003: Mixed French/English punctuation spacing *)
let r_lang_003 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    (* French: space before ; : ! ? *)
    let fr_style =
      contains_substring text " ;" || contains_substring text " :"
    in
    (* English: no space before ; : *)
    let en_style =
      contains_substring text ";\n" || contains_substring text ": "
    in
    let has_both = fr_style && en_style in
    if has_both then
      Some
        {
          id = "LANG-003";
          severity = Info;
          message = "Mixed French/English punctuation spacing";
          count = 1;
        }
    else None
  in
  { id = "LANG-003"; run }

(* LANG-011: French quotes absent — should use \og ... \fg{} *)
let r_lang_011 : rule =
  let run s =
    let has_french_babel =
      contains_substring s "\\usepackage[french]{babel}"
      || contains_substring s "\\usepackage[francais]{babel}"
      || contains_substring s "{french}" (* polyglossia *)
    in
    if not has_french_babel then None
    else
      let text = strip_comments (strip_math_segments s) in
      let has_ascii_quotes =
        contains_substring text {|"|} || contains_substring text {|``|}
      in
      if has_ascii_quotes then
        Some
          {
            id = "LANG-011";
            severity = Info;
            message = "French document uses ASCII quotes — use \\og ... \\fg{}";
            count = 1;
          }
      else None
  in
  { id = "LANG-011"; run }

(* LANG-012: babel language option mismatches \selectlanguage *)
let r_lang_012 : rule =
  let re_babel = Str.regexp {|\\usepackage\[\([a-z]+\)\]{babel}|} in
  let re_select = Str.regexp {|\\selectlanguage{\([a-z]+\)}|} in
  let run s =
    let babel_lang =
      try
        ignore (Str.search_forward re_babel s 0);
        Some (Str.matched_group 1 s)
      with Not_found -> None
    in
    let select_lang =
      try
        ignore (Str.search_forward re_select s 0);
        Some (Str.matched_group 1 s)
      with Not_found -> None
    in
    match (babel_lang, select_lang) with
    | Some b, Some sl when b <> sl ->
        Some
          {
            id = "LANG-012";
            severity = Info;
            message =
              Printf.sprintf
                "babel language '%s' mismatches \\selectlanguage{'%s'}" b sl;
            count = 1;
          }
    | _ -> None
  in
  { id = "LANG-012"; run }

(* LANG-014: BrE -ize/-ise inconsistency *)
let r_lang_014 : rule =
  let re_ize = Str.regexp {|[a-z]ize[ds .,\n]|} in
  let re_ise = Str.regexp {|[a-z]ise[ds .,\n]|} in
  let run s =
    let text =
      String.lowercase_ascii (strip_comments (strip_math_segments s))
    in
    let has_ize =
      try
        ignore (Str.search_forward re_ize text 0);
        true
      with Not_found -> false
    in
    let has_ise =
      try
        ignore (Str.search_forward re_ise text 0);
        true
      with Not_found -> false
    in
    if has_ize && has_ise then
      Some
        {
          id = "LANG-014";
          severity = Info;
          message = "BrE -ize/-ise ending inconsistency";
          count = 1;
        }
    else None
  in
  { id = "LANG-014"; run }

(* LANG-015: Serial-comma rule violated *)
let r_lang_015 : rule =
  (* Reuses STYLE-022 logic but as LANG-level rule *)
  let re = Str.regexp {|[a-zA-Z]+, [a-zA-Z]+ and [a-zA-Z]|} in
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
          id = "LANG-015";
          severity = Info;
          message = "Serial-comma rule violated (per style)";
          count = !cnt;
        }
    else None
  in
  { id = "LANG-015"; run }

(* LANG-016: 'programme'/'program' inconsistency in BrE text *)
let r_lang_016 : rule =
  let run s =
    let text =
      String.lowercase_ascii (strip_comments (strip_math_segments s))
    in
    let has_programme = contains_substring text "programme" in
    let has_program =
      contains_substring text "program "
      || contains_substring text "program,"
      || contains_substring text "program."
    in
    if has_programme && has_program then
      Some
        {
          id = "LANG-016";
          severity = Info;
          message = "'programme'/'program' inconsistency in text";
          count = 1;
        }
    else None
  in
  { id = "LANG-016"; run }

(* ══════════════════════════════════════════════════════════════════════ Phase
   4 batch: 10 remaining STYLE rules
   ══════════════════════════════════════════════════════════════════════ *)

(* STYLE-003: Passive voice in > 20% of sentences *)
let r_style_003 : rule =
  let re_passive =
    Str.regexp {|\(was\|were\|been\|being\|is\|are\) +[a-z]+ed |}
  in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let sents = sentence_split text in
    let total = List.length sents in
    if total < 5 then None
    else
      let passive_cnt =
        List.fold_left
          (fun acc sent ->
            if
              try
                ignore (Str.search_forward re_passive sent 0);
                true
              with Not_found -> false
            then acc + 1
            else acc)
          0 sents
      in
      let ratio = float_of_int passive_cnt /. float_of_int total in
      if ratio > 0.20 then
        Some
          {
            id = "STYLE-003";
            severity = Info;
            message =
              Printf.sprintf "Passive voice in %.0f%% of sentences"
                (ratio *. 100.0);
            count = passive_cnt;
          }
      else None
  in
  { id = "STYLE-003"; run }

(* STYLE-012: That/which relative-clause misuse *)
let r_style_012 : rule =
  let re = Str.regexp {|, which [a-z]|} in
  let re_that = Str.regexp {|that [a-z]|} in
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let has_which =
      try
        ignore (Str.search_forward re text 0);
        true
      with Not_found -> false
    in
    let has_that =
      try
        ignore (Str.search_forward re_that text 0);
        true
      with Not_found -> false
    in
    (* Only fire if both patterns present — indicates potential misuse *)
    if has_which && has_that then
      Some
        {
          id = "STYLE-012";
          severity = Info;
          message = "That/which relative-clause usage may be inconsistent";
          count = 1;
        }
    else None
  in
  { id = "STYLE-012"; run }

(* STYLE-029: Undefined 'we' (author vs generic) *)
let r_style_029 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    let has_author_we =
      contains_substring text "we present"
      || contains_substring text "we propose"
      || contains_substring text "we show"
      || contains_substring text "We present"
      || contains_substring text "We propose"
    in
    let has_generic_we =
      contains_substring text "we can see"
      || contains_substring text "we note"
      || contains_substring text "we observe"
      || contains_substring text "We can see"
      || contains_substring text "We note"
    in
    if has_author_we && has_generic_we then
      Some
        {
          id = "STYLE-029";
          severity = Info;
          message = "Undefined 'we' — mixes author-we and generic-we";
          count = 1;
        }
    else None
  in
  { id = "STYLE-029"; run }

(* STYLE-032: Bullet list mixes sentence-case and title-case *)
let r_style_032 : rule =
  let re_item = Str.regexp {|\\item +\([A-Za-z]\)|} in
  let run s =
    let text = strip_comments s in
    let uppers = ref 0 in
    let lowers = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re_item text !start);
         let c = (Str.matched_group 1 text).[0] in
         if c >= 'A' && c <= 'Z' then incr uppers else incr lowers;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !uppers > 0 && !lowers > 0 then
      Some
        {
          id = "STYLE-032";
          severity = Info;
          message = "Bullet list mixes sentence-case and title-case";
          count = min !uppers !lowers;
        }
    else None
  in
  { id = "STYLE-032"; run }

(* STYLE-038: Footnote paragraph exceeds 80 words *)
let r_style_038 : rule =
  let re = Str.regexp {|\\footnote{|} in
  let run s =
    let text = strip_comments s in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         let brace_start = Str.match_end () in
         let len = String.length text in
         let depth = ref 1 in
         let j = ref brace_start in
         while !j < len && !depth > 0 do
           (match text.[!j] with
           | '{' -> incr depth
           | '}' -> decr depth
           | _ -> ());
           if !depth > 0 then incr j
         done;
         (if !depth = 0 then
            let body = String.sub text brace_start (!j - brace_start) in
            if word_count body > 80 then incr cnt);
         start := !j + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-038";
          severity = Info;
          message = "Footnote paragraph exceeds 80 words";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-038"; run }

(* STYLE-039: Figure-caption ending punctuation inconsistent *)
let r_style_039 : rule =
  let re = Str.regexp {|\\caption{|} in
  let run s =
    let text = strip_comments s in
    let endings = ref [] in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         let brace_start = Str.match_end () in
         let len = String.length text in
         let depth = ref 1 in
         let j = ref brace_start in
         while !j < len && !depth > 0 do
           (match text.[!j] with
           | '{' -> incr depth
           | '}' -> decr depth
           | _ -> ());
           if !depth > 0 then incr j
         done;
         (if !depth = 0 && !j > brace_start then
            let body =
              String.trim (String.sub text brace_start (!j - brace_start))
            in
            if String.length body > 0 then
              endings := body.[String.length body - 1] :: !endings);
         start := !j + 1
       done
     with Not_found -> ());
    let endings = !endings in
    if List.length endings < 2 then None
    else
      let with_period = List.filter (fun c -> c = '.') endings in
      let without_period = List.filter (fun c -> c <> '.') endings in
      if List.length with_period > 0 && List.length without_period > 0 then
        Some
          {
            id = "STYLE-039";
            severity = Info;
            message = "Figure-caption ending punctuation inconsistent";
            count = min (List.length with_period) (List.length without_period);
          }
      else None
  in
  { id = "STYLE-039"; run }

(* STYLE-041: Footnote lacks terminal period *)
let r_style_041 : rule =
  let re = Str.regexp {|\\footnote{|} in
  let run s =
    let text = strip_comments s in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         let brace_start = Str.match_end () in
         let len = String.length text in
         let depth = ref 1 in
         let j = ref brace_start in
         while !j < len && !depth > 0 do
           (match text.[!j] with
           | '{' -> incr depth
           | '}' -> decr depth
           | _ -> ());
           if !depth > 0 then incr j
         done;
         (if !depth = 0 && !j > brace_start then
            let body =
              String.trim (String.sub text brace_start (!j - brace_start))
            in
            if String.length body > 0 && body.[String.length body - 1] <> '.'
            then incr cnt);
         start := !j + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "STYLE-041";
          severity = Info;
          message = "Footnote lacks terminal period";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-041"; run }

(* STYLE-043: Section-heading punctuation inconsistent *)
let r_style_043 : rule =
  let run s =
    let titles = extract_heading_titles s in
    if List.length titles < 2 then None
    else
      let with_punct =
        List.fold_left
          (fun acc t ->
            let t = String.trim t in
            if String.length t > 0 then
              let c = t.[String.length t - 1] in
              if c = '.' || c = ':' || c = '!' || c = '?' then acc + 1 else acc
            else acc)
          0 titles
      in
      let without_punct = List.length titles - with_punct in
      if with_punct > 0 && without_punct > 0 then
        Some
          {
            id = "STYLE-043";
            severity = Info;
            message = "Section-heading punctuation inconsistent";
            count = min with_punct without_punct;
          }
      else None
  in
  { id = "STYLE-043"; run }

(* STYLE-044: Ambiguous demonstrative 'this' without noun *)
let r_style_044 : rule =
  let re =
    Str.regexp
      {|[Tt]his \(is\|was\|has\|shows\|suggests\|means\|implies\|can\|will\|may\|might\|could\|should\) |}
  in
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
          id = "STYLE-044";
          severity = Info;
          message = "Ambiguous demonstrative 'this' without noun";
          count = !cnt;
        }
    else None
  in
  { id = "STYLE-044"; run }

(* STYLE-047: Quote-punctuation placement AmE vs BrE inconsistent *)
let r_style_047 : rule =
  let run s =
    let text = strip_comments (strip_math_segments s) in
    (* AmE: period inside quotes; BrE: period outside quotes *)
    let ame =
      contains_substring text {|."|} || contains_substring text {|,"|}
    in
    let bre =
      contains_substring text {|".|} || contains_substring text {|",|}
    in
    if ame && bre then
      Some
        {
          id = "STYLE-047";
          severity = Info;
          message = "Quote-punctuation placement AmE vs BrE inconsistent";
          count = 1;
        }
    else None
  in
  { id = "STYLE-047"; run }

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
    (* Phase 2 *)
    r_style_001;
    r_style_002;
    r_style_005;
    r_style_007;
    r_style_009;
    r_style_010;
    r_style_011;
    r_style_018;
    r_style_020;
    r_style_021;
    r_style_022;
    r_style_025;
    r_style_027;
    r_style_028;
    (* Locale / LANG *)
    r_ce_001;
    r_ce_002;
    r_th_001;
    r_ib_001;
    r_lang_003;
    r_lang_011;
    r_lang_012;
    r_lang_014;
    r_lang_015;
    r_lang_016;
    (* Phase 4 *)
    r_style_003;
    r_style_012;
    r_style_029;
    r_style_032;
    r_style_038;
    r_style_039;
    r_style_041;
    r_style_043;
    r_style_044;
    r_style_047;
  ]
