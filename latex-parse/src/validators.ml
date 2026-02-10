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

(* Tokenize LaTeX command names (with offsets) using Tokenizer_lite *)
let command_tokens (s : string) : (string * int) list =
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
             if !k > i then
               let name = String.sub s i (!k - i) in
               (name, t.s) :: acc
             else acc
         | _ -> acc)
       [] toks

(* Extract LaTeX command names from source, combining context and token scan *)
let extract_command_names (s : string) : string list =
  let ctx = Validators_context.get_post_commands () in
  let tokens = command_tokens s in
  let token_names = List.map fst tokens in
  if ctx = [] then token_names
  else
    let ctx_names_rev =
      List.fold_left
        (fun acc (pc : Validators_context.post_command) ->
          if List.exists (( = ) pc.name) acc then acc else pc.name :: acc)
        [] ctx
    in
    List.rev_append ctx_names_rev token_names

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
          let seg = strip_math_segments (String.sub s off len) in
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

(* BEGIN VPD-generated validators v0.3.0 — DO NOT EDIT BELOW THIS LINE *)

(* Spurious space before footnote command \footnote *)
let r_typo_034 : rule =
  let run s =
    let cnt = count_substring s " \\footnote" in
    if cnt > 0 then
      Some
        {
          id = "TYPO-034";
          severity = Info;
          message = "Spurious space before \\footnote";
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
          message =
            "Space before French punctuation mark; use non-breaking space ~";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-035"; run }

(* Suspicious consecutive capitalised words (shouting) *)
let r_typo_036 : rule =
  let run s =
    let re = Str.regexp "\\b[A-Z][A-Z]+ [A-Z][A-Z]+ [A-Z][A-Z]+\\b" in
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
          message =
            "Suspicious consecutive capitalised words; check for inadvertent \
             shouting";
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
  let run s =
    let re = Str.regexp "[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]+" in
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
          message = "Bare e-mail address found; wrap in \\href{mailto:...}";
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
          message = "Incorrect spacing around \\ldots; check for missing space";
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
          message = "Multiple consecutive question marks";
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
          message =
            "Smart (curly) quotes detected; verbatim sections require ASCII \
             quotes";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-043"; run }

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
          message = "En-dash character used where minus sign expected";
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
          message = "Thin space U+2009 found; prefer \\thinspace or \\, macro";
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
          message = "Unicode midline ellipsis U+22EF found; use \\cdots instead";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-053"; run }

(* Hair-space required after en-dash in word-word ranges *)
let r_typo_054 : rule =
  let run s =
    let re = Str.regexp "[a-zA-Z]\xe2\x80\x93[a-zA-Z]" in
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
          message =
            "En-dash adjacent to letter without spacing; consider thin space";
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
          message =
            "Consecutive \\, thin-spaces detected; collapse into single space";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-055"; run }

(* Missing thin-space before degree symbol *)
let r_typo_057 : rule =
  let run s =
    let re = Str.regexp "[0-9]\xc2\xb0" in
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
          message =
            "Number directly adjacent to degree symbol; insert thin space";
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
          message =
            "Unicode multiplication sign found; prefer \\times in math mode";
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
          message = "Non-breaking hyphen U+2011 found; use standard hyphen";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-063"; run }

(* URL split across lines without \url{} *)
let r_typo_039 : rule =
  let run s =
    let re = Str.regexp "https?://[^ \t\n}]+" in
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
  let run s =
    let re = Str.regexp "\\$\\([^$]+\\)\\$" in
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
          message = "Inline math $...$ exceeds 80 characters";
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
          message = "Non-ASCII punctuation in math mode";
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
          message = "Use of \\begin{math} instead of $...$";
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
  let run s =
    let re = Str.regexp "\\\\['^`\"~=.][{][a-zA-Z][}]" in
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
          message =
            "Legacy TeX accent command found; use UTF-8 character directly";
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
          message = "Greek homograph letter found in Latin text";
          count = cnt;
        }
    else None
  in
  { id = "TYPO-058"; run }

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
          message = "Zero-width space U+200B present";
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
          message = "C1 control characters U+0080-009F present";
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
          message = "Word joiner U+2060 present";
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
          message = "Interlinear annotation chars U+FFF9-FFFB detected";
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
          message = "Narrow no-break space U+202F present";
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
          message = "Bidirectional embedding chars U+202A-U+202E present";
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
          message = "Non-UTF-8 byte sequence detected";
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
          message = "BOM U+FEFF present in middle of file";
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
          message = "LATIN-1 smart quotes detected (bare bytes 0x91-0x94)";
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
          message = "Windows-1252 characters outside UTF-8 detected";
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
          message = "Mixed CRLF and LF line endings in file";
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
          message = "UTF-16 byte-order mark present";
          count = !cnt;
        }
    else None
  in
  { id = "ENC-014"; run }

let rules_enc : rule list =
  [
    r_enc_001;
    r_enc_002;
    r_enc_003;
    r_enc_004;
    r_enc_007;
    r_enc_012;
    r_enc_013;
    r_enc_014;
    r_enc_017;
    r_enc_020;
    r_enc_021;
    r_enc_022;
    r_enc_023;
    r_enc_024;
  ]

(* ── CHAR rules: control character detection ───────────────────────── *)

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
          message = "Bidirectional isolate chars U+2066-U+2069 present";
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
          message = "Unicode replacement character U+FFFD found; decoding error";
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
          message =
            "Zero-width no-break space U+FEFF inside paragraph (stray BOM)";
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
          message = "Full-width Latin letters detected";
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
          message = "Deprecated ligature characters present (U+FB00-FB04)";
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
          message = "Deprecated tag characters U+E0000-E007F present";
          count = !cnt;
        }
    else None
  in
  { id = "CHAR-022"; run }

let rules_char : rule list =
  [
    r_char_006;
    r_char_007;
    r_char_008;
    r_char_009;
    r_char_013;
    r_char_014;
    r_char_015;
    r_char_017;
    r_char_018;
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
          message = "Line longer than 120 characters";
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
          message = "Hard tab mixed with spaces in indentation";
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
          message = "Bare carriage return U+000D without LF";
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
          message = "BOM U+FEFF not at file start";
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
          message = "Multiple consecutive non-breaking spaces (~~)";
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
          message = "Non-breaking space at line start";
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
          message = "Whitespace-only paragraph";
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
          message = "Mixed LF and CRLF line endings in file";
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
          message = "Indentation exceeds 8 spaces";
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
          message = "Trailing full-width space U+3000 at line end";
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
          message = "Space before ellipsis";
          count = cnt;
        }
    else None
  in
  { id = "SPC-025"; run }

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
          message = "Line starts with full-width space U+3000";
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
          message = "Indentation with mix of NBSP and regular space";
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
          message = "No-break space before em-dash";
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
          message = "Thin-space before en-dash";
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
          message = "Leading thin-space U+2009 at start of line";
          count = matched;
        }
    else None
  in
  { id = "SPC-035"; run }

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
    r_spc_012;
    r_spc_013;
    r_spc_014;
    r_spc_015;
    r_spc_016;
    r_spc_019;
    r_spc_021;
    r_spc_024;
    r_spc_025;
    r_spc_028;
    r_spc_029;
    r_spc_030;
    r_spc_031;
    r_spc_032;
    r_spc_033;
    r_spc_034;
    r_spc_035;
  ]

(* ── TYPO-062: Literal backslash in text ───────────────────────────── *)
let r_typo_062 : rule =
  let run s =
    (* Count \textbackslash suggestions -- look for \\ not followed by a letter
       (i.e. bare backslash, not a command) outside math *)
    let s = strip_math_segments s in
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 1 do
      if s.[!i] = '\\' && s.[!i + 1] = '\\' then (
        (* Check it's not a linebreak command like \\[2pt] or \\* *)
        if !i + 2 < n then (
          let c = s.[!i + 2] in
          if c <> '[' && c <> '*' then incr cnt)
        else incr cnt;
        i := !i + 2)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "TYPO-062";
          severity = Warning;
          message = "Literal backslash in text; use \\textbackslash";
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-062"; run }

(* Combined ENC + CHAR + SPC + new TYPO rules *)
let rules_enc_char_spc : rule list =
  rules_enc @ rules_char @ rules_spc @ [ r_typo_062 ]

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
    let targets = [ "textbf"; "emph"; "section" ] in
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
  let tokens = command_tokens s in
  let matches set value = List.exists (( = ) value) set in
  let ctx_has off len names =
    List.exists
      (fun (pc : Validators_context.post_command) ->
        pc.s >= off && pc.s < off + len && matches names pc.name)
      pcs
  in
  let tokens_have off len names =
    List.exists
      (fun (name, pos) -> pos >= off && pos < off + len && matches names name)
      tokens
  in
  let has_cmd off len names =
    ctx_has off len names || tokens_have off len names
  in
  let check_para off len = has_cmd off len legacy && has_cmd off len modern in
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
  | Some ("1" | "true" | "pilot" | "PILOT") ->
      rules_pilot @ rules_vpd_gen @ rules_enc_char_spc @ rules_l1
  | _ -> rules_basic @ rules_enc_char_spc @ rules_l1

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
  | _ when String.length id >= 4 && String.sub id 0 4 = "ENC-" -> L0
  | _ when String.length id >= 5 && String.sub id 0 5 = "CHAR-" -> L0
  | _ when String.length id >= 4 && String.sub id 0 4 = "SPC-" -> L0
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
