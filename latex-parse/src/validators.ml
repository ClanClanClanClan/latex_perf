type severity = Error | Warning | Info

type result = {
  id : string;
  severity : severity;
  message : string;
  count : int;
}

type rule = { id : string; run : string -> result option }

(* Helpers *)
let count_char (s : string) (c : char) : int =
  let n = String.length s in
  let rec loop i acc =
    if i >= n then acc
    else loop (i + 1) (acc + if String.unsafe_get s i = c then 1 else 0)
  in
  loop 0 0

let count_substring (s : string) (sub : string) : int =
  let n = String.length s and m = String.length sub in
  if m = 0 || n < m then 0
  else
    let rec loop i acc =
      if i > n - m then acc
      else if String.sub s i m = sub then loop (i + 1) (acc + 1)
        (* allow overlaps *)
      else loop (i + 1) acc
    in
    loop 0 0

let any_line_pred (s : string) (pred : string -> bool) : int * int =
  (* returns (lines_checked, lines_matched) *)
  let len = String.length s in
  let rec loop i cur acc total =
    if i >= len then
      let total = total + if cur >= 0 then 1 else 0 in
      let matched =
        if cur >= 0 then if pred (String.sub s cur (i - cur)) then 1 else 0
        else 0
      in
      (total, acc + matched)
    else if String.unsafe_get s i = '\n' then
      let line = if cur >= 0 then String.sub s cur (i - cur) else "" in
      let acc = acc + if cur >= 0 && pred line then 1 else 0 in
      loop (i + 1) (i + 1) acc (total + 1)
    else if cur < 0 then loop (i + 1) 0 acc total
    else loop (i + 1) cur acc total
  in
  loop 0 0 0 0

(* Split text into paragraphs separated by two or more newlines *)
let split_into_paragraphs (s : string) : (int * int) list =
  (* returns list of (start, len) spans for each paragraph *)
  let n = String.length s in
  let rec collect acc i cur newlines =
    if i >= n then
      let acc = if cur < n then (cur, n - cur) :: acc else acc in
      List.rev acc
    else
      let c = String.unsafe_get s i in
      if c = '\n' then
        let newlines' = newlines + 1 in
        if newlines' >= 2 then
          let acc =
            if i - newlines' > cur then (cur, i - cur - newlines') :: acc
            else acc
          in
          collect acc (i + 1) (i + 1) 0
        else collect acc (i + 1) cur newlines'
      else collect acc (i + 1) cur 0
  in
  collect [] 0 0 0

(* Math-aware stripper: remove $...$, \( ... \), \[ ... \], and common math
   environments *)
let strip_math_segments (s : string) : string =
  let len = String.length s in
  let buf = Buffer.create len in
  let math_envs =
    [
      "equation";
      "equation*";
      "align";
      "align*";
      "gather";
      "gather*";
      "multline";
      "multline*";
      "eqnarray";
      "math";
      "displaymath";
    ]
  in
  let is_math_env name = List.exists (String.equal name) math_envs in
  let starts_with prefix idx =
    let plen = String.length prefix in
    idx + plen <= len && String.sub s idx plen = prefix
  in
  let is_escaped idx =
    let rec count back acc =
      if back < 0 then acc
      else if String.unsafe_get s back = '\\' then count (back - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let parse_begin idx =
    let prefix = "\\begin{" in
    if not (starts_with prefix idx) then None
    else
      let name_start = idx + String.length prefix in
      let j = ref name_start in
      while !j < len && String.unsafe_get s !j <> '}' do
        incr j
      done;
      if !j >= len then None
      else
        let name = String.sub s name_start (!j - name_start) in
        Some (name, !j + 1)
  in
  let rec skip_env name idx depth =
    let end_prefix = "\\end{" ^ name ^ "}" in
    let end_len = String.length end_prefix in
    if idx >= len then len
    else if (not (is_escaped idx)) && starts_with end_prefix idx then
      if depth = 0 then idx + end_len
      else skip_env name (idx + end_len) (depth - 1)
    else if (not (is_escaped idx)) && starts_with "\\begin{" idx then
      match parse_begin idx with
      | Some (inner, next_idx) when is_math_env inner ->
          let after_inner = skip_env inner next_idx 0 in
          skip_env name after_inner depth
      | Some (_, next_idx) -> skip_env name next_idx depth
      | None -> skip_env name (idx + 1) depth
    else skip_env name (idx + 1) depth
  in
  let in_dollar = ref false in
  let in_paren = ref false in
  let in_brack = ref false in
  let rec loop i =
    if i >= len then ()
    else if !in_dollar then
      if (not (is_escaped i)) && s.[i] = '$' then (
        in_dollar := false;
        loop (i + 1))
      else loop (i + 1)
    else if !in_paren then
      if (not (is_escaped i)) && starts_with "\\)" i then (
        in_paren := false;
        loop (i + 2))
      else loop (i + 1)
    else if !in_brack then
      if (not (is_escaped i)) && starts_with "\\]" i then (
        in_brack := false;
        loop (i + 2))
      else loop (i + 1)
    else if (not (is_escaped i)) && s.[i] = '$' then (
      in_dollar := true;
      loop (i + 1))
    else if (not (is_escaped i)) && starts_with "\\(" i then (
      in_paren := true;
      loop (i + 2))
    else if (not (is_escaped i)) && starts_with "\\[" i then (
      in_brack := true;
      loop (i + 2))
    else if (not (is_escaped i)) && starts_with "\\begin{" i then (
      match parse_begin i with
      | Some (name, after_begin) when is_math_env name ->
          let next_i = skip_env name after_begin 0 in
          loop next_i
      | _ ->
          Buffer.add_char buf s.[i];
          loop (i + 1))
    else (
      Buffer.add_char buf s.[i];
      loop (i + 1))
  in
  loop 0;
  Buffer.contents buf

(* Extract LaTeX command names from source using Tokenizer_lite *)
let extract_command_names (s : string) : string list =
  (* Prefer per-request post_commands context if available (thread-local), else
     fallback to token scan *)
  let ctx = Validators_context.get_post_commands () in
  if ctx <> [] then
    List.map (fun (pc : Validators_context.post_command) -> pc.name) ctx
  else
    let module T = Tokenizer_lite in
    let toks = T.tokenize s in
    let n = String.length s in
    List.rev
    @@ List.fold_left
         (fun acc (t : T.tok) ->
           match t.kind with
           | T.Command ->
               let i = t.s + 1 in
               let k = ref i in
               while
                 !k < n
                 &&
                 let ch = String.unsafe_get s !k in
                 (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
               do
                 incr k
               done;
               if !k > i then String.sub s i (!k - i) :: acc else acc
           | _ -> acc)
         [] toks

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
          message = "ASCII straight quotes must be curly quotes";
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
              message = "Double hyphen -- should be en-dash –";
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
              message = "Double hyphen -- should be en-dash –";
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
              message = "Triple hyphen --- should be em-dash —";
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
              message = "Triple hyphen --- should be em-dash —";
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
          message = "TeX double back-tick ``…'' not allowed; use curly quotes";
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
              message = "Multiple consecutive blank lines (>2) in source";
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
              message = "Multiple consecutive blank lines (>2) in source";
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
          message = "Non-breaking space ~ used incorrectly at line start";
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

(* Additional pilot rules to reach 15+ *)

let r_typo_011 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: rest -> (
                match a.kind with
                | Space when a.e - a.s > 1 -> loop (c + 1) rest
                | _ -> loop c rest)
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-011";
              severity = Info;
              message = "Multiple consecutive spaces in text";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s "  " in
        if cnt > 0 then
          Some
            {
              id = "TYPO-011";
              severity = Info;
              message = "Multiple consecutive spaces in text";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-011"; run }

let r_typo_012 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind, b.ch) with
                | Space, Bracket_close, Some _ -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-012";
              severity = Warning;
              message = "Space before closing bracket ) ] }";
              count = cnt;
            }
        else None
    | _ ->
        let combos = [ " )"; " ]"; " }" ] in
        let cnt =
          List.fold_left (fun acc sub -> acc + count_substring s sub) 0 combos
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-012";
              severity = Warning;
              message = "Space before closing bracket ) ] }";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-012"; run }

let r_typo_013 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        (* Look for single-letter Word tokens followed by Space then Word *)
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: c' :: rest -> (
                match (a.kind, b.kind, c'.kind) with
                | Word, Space, Word when a.e - a.s = 1 ->
                    loop (c + 1) (b :: c' :: rest)
                | _ -> loop c (b :: c' :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-013";
              severity = Info;
              message = "Consider non-breaking space after single-letter words";
              count = cnt;
            }
        else None
    | _ ->
        let patterns = [ " a "; " I "; " a\n"; " I\n" ] in
        let cnt =
          List.fold_left (fun acc sub -> acc + count_substring s sub) 0 patterns
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-013";
              severity = Info;
              message = "Consider non-breaking space after single-letter words";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-013"; run }

let r_typo_014 : rule =
  let run s =
    (* Paragraph-aware mixed quote styles: straight and curly in same
       paragraph *)
    let paras = split_into_paragraphs s in
    let mixed =
      let check seg0 =
        let seg = strip_math_segments seg0 in
        let has_straight = count_char seg '"' > 0 || count_char seg '\'' > 0 in
        let has_curly =
          Unicode.has_curly_quote seg
          || count_substring seg "``" + count_substring seg "''" > 0
        in
        has_straight && has_curly
      in
      if paras = [] then check s
      else List.exists (fun (off, len) -> check (String.sub s off len)) paras
    in
    if mixed then
      Some
        {
          id = "TYPO-014";
          severity = Warning;
          message = "Inconsistent quotation mark style within text";
          count = 1;
        }
    else None
  in
  { id = "TYPO-014"; run }

let r_typo_015 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind) with
                | Command, Space -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-015";
              severity = Info;
              message = "LaTeX command spacing may need adjustment";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s "\\ " in
        if cnt > 0 then
          Some
            {
              id = "TYPO-015";
              severity = Info;
              message = "LaTeX command spacing may need adjustment";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-015"; run }

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
  ]

(* Extended pilot additions *)

let r_typo_016 : rule =
  let run s =
    let cnt = count_substring s "!!" + count_substring s "!!!" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-016";
          severity = Info;
          message = "Excessive exclamation marks, consider moderation";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-016"; run }

let r_typo_017 : rule =
  let run s =
    let cnt = count_substring s "??" + count_substring s "???" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-017";
          severity = Info;
          message = "Excessive question marks, consider moderation";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-017"; run }

let r_typo_018 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let is_end = function Some ('.' | '?' | '!') -> true | _ -> false in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, a.ch, b.kind) with
                | Symbol, ch, Space when is_end ch && b.e - b.s > 1 ->
                    loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-018";
              severity = Warning;
              message = "Double space after sentence punctuation";
              count = cnt;
            }
        else None
    | _ ->
        let cnt =
          count_substring s ".  "
          + count_substring s "?  "
          + count_substring s "!  "
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-018";
              severity = Warning;
              message = "Double space after sentence punctuation";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-018"; run }

let r_typo_019 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c prev = function
            | [] -> c
            | t :: rest -> (
                match (prev, t.kind) with
                | None, Space -> loop (c + 1) (Some t.kind) rest
                | Some Newline, Space -> loop (c + 1) (Some t.kind) rest
                | _ -> loop c (Some t.kind) rest)
          in
          loop 0 None toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-019";
              severity = Info;
              message = "Leading spaces at start of line";
              count = cnt;
            }
        else None
    | _ ->
        let starts =
          if String.length s > 0 && String.unsafe_get s 0 = ' ' then 1 else 0
        in
        let cnt = starts + count_substring s "\n " in
        if cnt > 0 then
          Some
            {
              id = "TYPO-019";
              severity = Info;
              message = "Leading spaces at start of line";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-019"; run }

let r_typo_020 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, a.ch, b.kind, b.ch) with
                | Symbol, Some ',', Symbol, Some ',' -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-020";
              severity = Warning;
              message = "Consecutive commas ,, found";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s ",," in
        if cnt > 0 then
          Some
            {
              id = "TYPO-020";
              severity = Warning;
              message = "Consecutive commas ,, found";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-020"; run }

let rules_pilot : rule list =
  rules_pilot @ [ r_typo_016; r_typo_017; r_typo_018; r_typo_019; r_typo_020 ]

(* Next 5 high-signal lexical rules *)

let r_typo_021 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind, a.ch) with
                | Bracket_open, Space, Some _ -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-021";
              severity = Warning;
              message = "Space after opening bracket ( [ {";
              count = cnt;
            }
        else None
    | _ ->
        let cnt =
          count_substring s "( "
          + count_substring s "[ "
          + count_substring s "{ "
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-021";
              severity = Warning;
              message = "Space after opening bracket ( [ {";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-021"; run }

let r_typo_022 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let is_punct c =
          match c with ',' | '.' | ';' | ':' | '?' | '!' -> true | _ -> false
        in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, a.ch, b.kind) with
                | Symbol, Some ch, (Word | Command | Bracket_open | Quote)
                  when is_punct ch ->
                    loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-022";
              severity = Warning;
              message = "Missing space after punctuation";
              count = cnt;
            }
        else None
    | _ ->
        (* byte-level fallback *)
        let n = String.length s in
        let is_punct c =
          match c with ',' | '.' | ';' | ':' | '?' | '!' -> true | _ -> false
        in
        let is_space c = c = ' ' || c = '\n' || c = '\t' in
        let is_word c =
          ('a' <= c && c <= 'z')
          || ('A' <= c && c <= 'Z')
          || ('0' <= c && c <= '9')
        in
        let rec loop i acc =
          if i + 1 >= n then acc
          else
            let c = String.unsafe_get s i in
            let d = String.unsafe_get s (i + 1) in
            if is_punct c && (not (is_space d)) && is_word d then
              loop (i + 1) (acc + 1)
            else loop (i + 1) acc
        in
        let cnt = loop 0 0 in
        if cnt > 0 then
          Some
            {
              id = "TYPO-022";
              severity = Warning;
              message = "Missing space after punctuation";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-022"; run }

let r_typo_023 : rule =
  let run s =
    let cnt = count_char s '\r' in
    if cnt > 0 then
      Some
        {
          id = "TYPO-023";
          severity = Warning;
          message = "Windows CR (\r) line endings found";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-023"; run }

let r_typo_024 : rule =
  let run s =
    let n = String.length s in
    let rec loop i acc =
      if i >= n then acc
      else
        let c = String.unsafe_get s i in
        let code = Char.code c in
        if code < 32 && code <> 9 && code <> 10 then loop (i + 1) (acc + 1)
        else loop (i + 1) acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        {
          id = "TYPO-024";
          severity = Error;
          message = "Control characters (U+0000–U+001F) present";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-024"; run }

let r_typo_025 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind) with
                | Space, Quote -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-025";
              severity = Warning;
              message = "Space before closing quote";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s " \"" + count_substring s " '" in
        if cnt > 0 then
          Some
            {
              id = "TYPO-025";
              severity = Warning;
              message = "Space before closing quote";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-025"; run }

let rules_pilot : rule list =
  rules_pilot @ [ r_typo_021; r_typo_022; r_typo_023; r_typo_024; r_typo_025 ]

(* Next 5 lexical rules (026–030) *)

let r_typo_026 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        (* Count pairs of consecutive '.' symbols not part of '...' *)
        let cnt =
          let rec loop c = function
            | [] -> c
            | [ _ ] -> c
            | a :: b :: c' :: rest -> (
                match (a.ch, b.ch, c'.ch) with
                | Some '.', Some '.', Some '.' -> loop c (b :: c' :: rest)
                | Some '.', Some '.', _ -> loop (c + 1) (b :: c' :: rest)
                | _ -> loop c (b :: c' :: rest))
            | a :: b :: rest -> (
                match (a.ch, b.ch) with
                | Some '.', Some '.' -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-026";
              severity = Warning;
              message = "Double period .. should be … or \\\\dots";
              count = cnt;
            }
        else None
    | _ ->
        let dd = count_substring s ".." in
        let ell = count_substring s "..." in
        let cnt = dd - (2 * ell) in
        if cnt > 0 then
          Some
            {
              id = "TYPO-026";
              severity = Warning;
              message = "Double period .. should be … or \\\\dots";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-026"; run }

let r_typo_027 : rule =
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
                | Space, Symbol, ch when b.e - b.s > 1 && is_punct ch ->
                    loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-027";
              severity = Warning;
              message = "Multiple spaces before punctuation";
              count = cnt;
            }
        else None
    | _ ->
        let combos = [ "  ,"; "  ."; "  ;"; "  :"; "  ?"; "  !" ] in
        let cnt =
          List.fold_left (fun acc sub -> acc + count_substring s sub) 0 combos
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-027";
              severity = Warning;
              message = "Multiple spaces before punctuation";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-027"; run }

let r_typo_028 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind, b.ch) with
                | Space, Symbol, Some '%' -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-028";
              severity = Warning;
              message = "Space before percent sign %";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s " %" in
        if cnt > 0 then
          Some
            {
              id = "TYPO-028";
              severity = Warning;
              message = "Space before percent sign %";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-028"; run }

let r_typo_029 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind) with
                | Quote, Space -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            {
              id = "TYPO-029";
              severity = Warning;
              message = "Space after opening quote";
              count = cnt;
            }
        else None
    | _ ->
        let cnt = count_substring s "\" " + count_substring s "' " in
        if cnt > 0 then
          Some
            {
              id = "TYPO-029";
              severity = Warning;
              message = "Space after opening quote";
              count = cnt;
            }
        else None
  in
  { id = "TYPO-029"; run }

(* CMD-001: Deprecated LaTeX commands present in the document *)
let l1_cmd_001_rule : rule =
  let run s =
    let deprecated = [ "over"; "centerline"; "bf"; "it" ] in
    let names = extract_command_names s in
    let cnt =
      List.fold_left
        (fun acc name ->
          if List.exists (( = ) name) deprecated then acc + 1 else acc)
        0 names
    in
    if cnt > 0 then
      Some
        {
          id = "CMD-001";
          severity = Warning;
          message = "Deprecated LaTeX command: use modern equivalent";
          count = cnt;
        }
    else None
  in
  { id = "CMD-001"; run }

let l1_cmd_003_rule : rule =
  let run s =
    let deep_sectioning = [ "paragraph"; "subparagraph"; "subsubsection" ] in
    let names = extract_command_names s in
    let cnt =
      List.fold_left
        (fun acc name ->
          if List.exists (( = ) name) deep_sectioning then acc + 1 else acc)
        0 names
    in
    if cnt > 0 then
      Some
        {
          id = "CMD-003";
          severity = Info;
          message = "Deep sectioning level may affect readability";
          count = cnt;
        }
    else None
  in
  { id = "CMD-003"; run }

(* Removed earlier generic L1 rules not aligned to catalogue; will add
   package-focused L1 rules later *)

let r_typo_030 : rule =
  let run s =
    let cnt = count_substring s "----" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-030";
          severity = Warning;
          message = "More than three hyphens detected (----)";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-030"; run }

let rules_pilot : rule list =
  rules_pilot @ [ r_typo_026; r_typo_027; r_typo_028; r_typo_029; r_typo_030 ]

(* Unicode: mixed dash styles — Unicode en/em dashes present alongside ASCII
   patterns *)
let r_typo_031 : rule =
  let run s =
    (* Paragraph-aware: flag only if mixing occurs within at least one
       paragraph *)
    let paras = split_into_paragraphs s in
    let mixed_in_para =
      List.exists
        (fun (off, len) ->
          let seg = strip_math_segments (String.sub s off len) in
          let has_u = Unicode.has_en_dash seg || Unicode.has_em_dash seg in
          let has_a =
            count_substring seg "--" + count_substring seg "---" > 0
          in
          has_u && has_a)
        (if paras = [] then [ (0, String.length s) ] else paras)
    in
    if mixed_in_para then
      Some
        {
          id = "TYPO-031";
          severity = Info;
          message = "Mixed dash styles detected (ASCII and Unicode)";
          count = 1;
        }
    else None
  in
  { id = "TYPO-031"; run }

let rules_pilot : rule list = rules_pilot @ [ r_typo_031 ]

(* Unicode dash normalization suggestion *)
let r_typo_032 : rule =
  let run s =
    (* Paragraph-aware dominance check: prefer Unicode when it dominates within
       blocks *)
    let paras = split_into_paragraphs s in
    let check seg =
      let u = Unicode.count_en_dash seg + Unicode.count_em_dash seg in
      (* normalize ASCII dash sequences without double-counting '---' as '--' +
         '---' *)
      let a =
        let n = String.length seg in
        let rec loop i acc =
          if i + 1 >= n then acc
          else if
            i + 2 < n
            && String.unsafe_get seg i = '-'
            && String.unsafe_get seg (i + 1) = '-'
            && String.unsafe_get seg (i + 2) = '-'
          then loop (i + 3) (acc + 1)
          else if
            String.unsafe_get seg i = '-' && String.unsafe_get seg (i + 1) = '-'
          then loop (i + 2) (acc + 1)
          else loop (i + 1) acc
        in
        loop 0 0
      in
      u > a && a > 0
    in
    let ascii_sporadic =
      if paras = [] then check s
      else List.exists (fun (off, len) -> check (String.sub s off len)) paras
    in
    if ascii_sporadic then
      Some
        {
          id = "TYPO-032";
          severity = Info;
          message =
            "Prefer Unicode dashes consistently; ASCII --/--- appear \
             sporadically";
          count = 1;
        }
    else None
  in
  { id = "TYPO-032"; run }

let rules_pilot : rule list = rules_pilot @ [ r_typo_032 ]

(* Unicode ellipsis normalization suggestion *)
let r_typo_033 : rule =
  let run s =
    (* Paragraph-aware mixing for ellipsis as well *)
    let paras = split_into_paragraphs s in
    let mixed =
      List.exists
        (fun (off, len) ->
          let seg = String.sub s off len in
          Unicode.has_ellipsis_char seg && count_substring seg "..." > 0)
        (if paras = [] then [ (0, String.length s) ] else paras)
    in
    if mixed then
      Some
        {
          id = "TYPO-033";
          severity = Info;
          message = "Mixed ellipsis styles detected (Unicode and ASCII)";
          count = 1;
        }
    else None
  in
  { id = "TYPO-033"; run }

let rules_pilot : rule list = rules_pilot @ [ r_typo_033 ]

(* L1 modernization and expansion checks (using post-commands heuristics) *)
let l1_mod_001_rule : rule =
  let run s =
    (* MOD-001: Legacy font commands present; prefer modern commands *)
    let names = extract_command_names s in
    let legacy = [ "bf"; "it"; "tt"; "rm"; "sl"; "sf" ] in
    let cnt =
      List.fold_left
        (fun acc n -> if List.exists (( = ) n) legacy then acc + 1 else acc)
        0 names
    in
    if cnt > 0 then
      Some
        {
          id = "MOD-001";
          severity = Warning;
          message =
            "Legacy font commands (\\bf/\\it/...) present; prefer \
             \\textbf/\\emph";
          count = cnt;
        }
    else None
  in
  { id = "MOD-001"; run }

let l1_exp_001_rule : rule =
  let run s =
    (* EXP-001: Incomplete expansion — strip targets still present
       post-expansion *)
    let names = extract_command_names s in
    let targets = [ "textbf"; "emph"; "section"; "bfseries" ] in
    let cnt =
      List.fold_left
        (fun acc n -> if List.exists (( = ) n) targets then acc + 1 else acc)
        0 names
    in
    if cnt > 0 then
      Some
        {
          id = "EXP-001";
          severity = Info;
          message =
            "Incomplete expansion: catalogue commands remain post-expansion";
          count = cnt;
        }
    else None
  in
  { id = "EXP-001"; run }

(* Helpers for L1 paragraph-aware mixing using post-command spans *)
let has_mixed_in_paragraphs (s : string) ~(legacy : string list)
    ~(modern : string list) : bool =
  let paras = split_into_paragraphs s in
  let pcs = Validators_context.get_post_commands () in
  let has_ctx = pcs <> [] in
  let names = if has_ctx then [] else extract_command_names s in
  let check_para off len =
    if has_ctx then
      let has_legacy =
        List.exists
          (fun (pc : Validators_context.post_command) ->
            pc.s >= off
            && pc.s < off + len
            && List.exists (( = ) pc.name) legacy)
          pcs
      in
      let has_modern =
        List.exists
          (fun (pc : Validators_context.post_command) ->
            pc.s >= off
            && pc.s < off + len
            && List.exists (( = ) pc.name) modern)
          pcs
      in
      has_legacy && has_modern
    else
      (* Fallback without spans: coarse check over entire text *)
      List.exists (fun n -> List.exists (( = ) n) names) legacy
      && List.exists (fun n -> List.exists (( = ) n) names) modern
  in
  let ranges = if paras = [] then [ (0, String.length s) ] else paras in
  List.exists (fun (off, len) -> check_para off len) ranges

let l1_mod_002_rule : rule =
  let run s =
    (* MOD-002: Mixed legacy and modern bold commands in same paragraph *)
    let legacy = [ "bf" ] and modern = [ "textbf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-002";
          severity = Warning;
          message = "Mixed legacy and modern bold commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-002"; run }

let l1_mod_003_rule : rule =
  let run s =
    (* MOD-003: Mixed legacy and modern italic commands in same paragraph *)
    let legacy = [ "it" ] and modern = [ "emph"; "textit" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-003";
          severity = Warning;
          message = "Mixed legacy and modern italic commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-003"; run }

let l1_mod_004_rule : rule =
  let run s =
    (* MOD-004: Mixed legacy and modern roman family commands in same
       paragraph *)
    let legacy = [ "rm" ] and modern = [ "textrm" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-004";
          severity = Warning;
          message = "Mixed legacy and modern roman commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-004"; run }

let l1_mod_005_rule : rule =
  let run s =
    (* MOD-005: Mixed legacy and modern typewriter commands in same paragraph *)
    let legacy = [ "tt" ] and modern = [ "texttt" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-005";
          severity = Warning;
          message =
            "Mixed legacy and modern typewriter commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-005"; run }

let l1_mod_006_rule : rule =
  let run s =
    (* MOD-006: Mixed legacy and modern sans-serif commands in same paragraph *)
    let legacy = [ "sf" ] and modern = [ "textsf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-006";
          severity = Warning;
          message =
            "Mixed legacy and modern sans-serif commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-006"; run }

let l1_mod_007_rule : rule =
  let run s =
    (* MOD-007: Mixed legacy and modern small-caps commands in same paragraph *)
    let legacy = [ "sc" ] and modern = [ "textsc" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-007";
          severity = Warning;
          message =
            "Mixed legacy and modern small-caps commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-007"; run }

let l1_mod_008_rule : rule =
  let run s =
    (* MOD-008: Mixed NFSS series switch vs inline macro in same paragraph
       (bfseries vs textbf) *)
    let legacy = [ "bfseries" ] and modern = [ "textbf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-008";
          severity = Warning;
          message = "Mixed NFSS bfseries and inline \\textbf in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-008"; run }

let l1_mod_009_rule : rule =
  let run s =
    (* MOD-009: Mixed NFSS shape switch vs inline macro in same paragraph
       (itshape vs textit/emph) *)
    let legacy = [ "itshape" ] and modern = [ "textit"; "emph" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-009";
          severity = Warning;
          message =
            "Mixed NFSS itshape and inline \\textit/\\emph in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-009"; run }

let l1_mod_010_rule : rule =
  let run s =
    (* MOD-010: Mixed NFSS family switch vs inline macro (sffamily vs textsf) *)
    let legacy = [ "sffamily" ] and modern = [ "textsf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-010";
          severity = Warning;
          message = "Mixed NFSS sffamily and inline \\textsf in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-010"; run }

let l1_mod_011_rule : rule =
  let run s =
    (* MOD-011: Mixed NFSS family switch vs inline macro (ttfamily vs texttt) *)
    let legacy = [ "ttfamily" ] and modern = [ "texttt" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-011";
          severity = Warning;
          message = "Mixed NFSS ttfamily and inline \\texttt in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-011"; run }

let l1_mod_012_rule : rule =
  let run s =
    (* MOD-012: Mixed NFSS family switch vs inline macro (rmfamily vs textrm) *)
    let legacy = [ "rmfamily" ] and modern = [ "textrm" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-012";
          severity = Warning;
          message = "Mixed NFSS rmfamily and inline \\textrm in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-012"; run }

let l1_mod_013_rule : rule =
  let run s =
    (* MOD-013: Mixed NFSS shape switch vs inline macro (scshape vs textsc) *)
    let legacy = [ "scshape" ] and modern = [ "textsc" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-013";
          severity = Warning;
          message = "Mixed NFSS scshape and inline \\textsc in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-013"; run }

(* Global modernization suggestions (document-wide mixing across paragraphs) *)
let has_global_mixing names legacy modern : bool =
  let has_any xs = List.exists (fun n -> List.exists (( = ) n) names) xs in
  has_any legacy && has_any modern

let l1_mod_020_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "bfseries" ] [ "textbf" ] then
      Some
        {
          id = "MOD-020";
          severity = Info;
          message =
            "Global mix: NFSS bfseries and inline \\textbf appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-020"; run }

let l1_mod_021_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "itshape" ] [ "textit"; "emph" ] then
      Some
        {
          id = "MOD-021";
          severity = Info;
          message =
            "Global mix: NFSS itshape and inline \\textit/\\emph appear in \
             different paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-021"; run }

let l1_mod_022_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "rmfamily" ] [ "textrm" ] then
      Some
        {
          id = "MOD-022";
          severity = Info;
          message =
            "Global mix: NFSS rmfamily and inline \\textrm appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-022"; run }

let l1_mod_023_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "sffamily" ] [ "textsf" ] then
      Some
        {
          id = "MOD-023";
          severity = Info;
          message =
            "Global mix: NFSS sffamily and inline \\textsf appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-023"; run }

let l1_mod_024_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "ttfamily" ] [ "texttt" ] then
      Some
        {
          id = "MOD-024";
          severity = Info;
          message =
            "Global mix: NFSS ttfamily and inline \\texttt appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-024"; run }

let rules_l1 : rule list =
  [
    l1_cmd_001_rule;
    l1_cmd_003_rule;
    l1_mod_001_rule;
    l1_exp_001_rule;
    l1_mod_002_rule;
    l1_mod_003_rule;
    l1_mod_004_rule;
    l1_mod_005_rule;
    l1_mod_006_rule;
    l1_mod_007_rule;
    l1_mod_008_rule;
    l1_mod_009_rule;
    l1_mod_010_rule;
    l1_mod_011_rule;
    l1_mod_012_rule;
    l1_mod_013_rule;
    l1_mod_020_rule;
    l1_mod_021_rule;
    l1_mod_022_rule;
    l1_mod_023_rule;
    l1_mod_024_rule;
  ]

let get_rules () : rule list =
  match Sys.getenv_opt "L0_VALIDATORS" with
  | Some ("1" | "true" | "pilot" | "PILOT") -> rules_pilot @ rules_l1
  | _ -> rules_basic @ rules_l1

let run_all (src : string) : result list =
  let rec go acc = function
    | [] -> List.rev acc
    | r :: rs ->
        let t0 = Unix.gettimeofday () in
        let acc =
          match r.run src with
          | Some res ->
              let t1 = Unix.gettimeofday () in
              let dur_ms = (t1 -. t0) *. 1000.0 in
              Validators_metrics.record ~id:res.id ~count:res.count ~dur_ms;
              res :: acc
          | None -> acc
        in
        go acc rs
  in
  go [] (get_rules ())

let run_all_with_timings (src : string) :
    result list * float * (string * float) list =
  let rules = get_rules () in
  let timings = ref [] in
  let t0 = Unix.gettimeofday () in
  let rec exec acc = function
    | [] -> List.rev acc
    | r :: rs ->
        let t_rule0 = Unix.gettimeofday () in
        let acc' =
          match r.run src with
          | Some res ->
              let t_rule1 = Unix.gettimeofday () in
              let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
              timings := (r.id, dur_ms) :: !timings;
              Validators_metrics.record ~id:res.id ~count:res.count ~dur_ms;
              res :: acc
          | None ->
              let t_rule1 = Unix.gettimeofday () in
              let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
              timings := (r.id, dur_ms) :: !timings;
              acc
        in
        exec acc' rs
  in
  let results = exec [] rules in
  let t1 = Unix.gettimeofday () in
  (results, (t1 -. t0) *. 1000.0, List.rev !timings)

(* Precondition wiring (stubs) *)
type layer = L0 | L1 | L2 | L3 | L4

let precondition_of_rule_id (id : string) : layer =
  match id with
  | _ when String.length id >= 5 && String.sub id 0 5 = "TYPO-" -> L0
  | _ when String.length id >= 4 && String.sub id 0 4 = "CMD-" -> L1
  | _ when String.length id >= 4 && String.sub id 0 4 = "MOD-" -> L1
  | _ when String.length id >= 4 && String.sub id 0 4 = "EXP-" -> L1
  | _ -> L0

let allow_for_layer (id : string) (ly : layer) : bool =
  match (precondition_of_rule_id id, ly) with
  | L0, L0 -> true
  | L1, L1 -> true
  | L2, L2 -> true
  | L3, L3 -> true
  | L4, L4 -> true
  | _ -> false

let run_all_with_timings_for_layer (src : string) (ly : layer) :
    result list * float * (string * float) list =
  let rules = get_rules () in
  let timings = ref [] in
  let t0 = Unix.gettimeofday () in
  let rec exec acc = function
    | [] -> List.rev acc
    | r :: rs ->
        let t_rule0 = Unix.gettimeofday () in
        let acc' =
          if allow_for_layer r.id ly then (
            match r.run src with
            | Some res ->
                let t_rule1 = Unix.gettimeofday () in
                let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
                timings := (r.id, dur_ms) :: !timings;
                Validators_metrics.record ~id:res.id ~count:res.count ~dur_ms;
                res :: acc
            | None ->
                let t_rule1 = Unix.gettimeofday () in
                let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
                timings := (r.id, dur_ms) :: !timings;
                acc)
          else
            let t_rule1 = Unix.gettimeofday () in
            let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
            timings := (r.id, dur_ms) :: !timings;
            acc
        in
        exec acc' rs
  in
  let results = exec [] rules in
  let t1 = Unix.gettimeofday () in
  (results, (t1 -. t0) *. 1000.0, List.rev !timings)

let severity_to_string = function
  | Error -> "error"
  | Warning -> "warning"
  | Info -> "info"
