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

(* Helper: extract content blocks between \begin{env}...\end{env} *)
let extract_env_blocks (env : string) (s : string) : string list =
  let open_tag = "\\begin{" ^ env ^ "}" in
  let close_tag = "\\end{" ^ env ^ "}" in
  let open_len = String.length open_tag in
  let close_len = String.length close_tag in
  let n = String.length s in
  let blocks = ref [] in
  let i = ref 0 in
  while !i <= n - open_len do
    if String.sub s !i open_len = open_tag then (
      let start = !i + open_len in
      (* skip optional [...] after \begin{lstlisting} *)
      let content_start = ref start in
      if !content_start < n && s.[!content_start] = '[' then (
        while !content_start < n && s.[!content_start] <> ']' do
          incr content_start
        done;
        if !content_start < n then incr content_start);
      (* find matching \end{env} *)
      let found = ref false in
      let j = ref !content_start in
      while !j <= n - close_len && not !found do
        if String.sub s !j close_len = close_tag then (
          blocks := String.sub s !content_start (!j - !content_start) :: !blocks;
          i := !j + close_len;
          found := true)
        else incr j
      done;
      if not !found then i := n)
    else incr i
  done;
  List.rev !blocks

(* Helper: check if string is inside \begin{document}...\end{document} body *)
let extract_document_body (s : string) : string option =
  let tag = "\\begin{document}" in
  let etag = "\\end{document}" in
  let tlen = String.length tag in
  let elen = String.length etag in
  let n = String.length s in
  let start = ref (-1) in
  let i = ref 0 in
  while !i <= n - tlen do
    if String.sub s !i tlen = tag then (
      start := !i + tlen;
      i := n)
    else incr i
  done;
  if !start < 0 then None
  else
    let finish = ref n in
    let j = ref !start in
    while !j <= n - elen do
      if String.sub s !j elen = etag then (
        finish := !j;
        j := n)
      else incr j
    done;
    Some (String.sub s !start (!finish - !start))

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
            "Smart quotes present inside lstlisting/verbatim environments";
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
          message = "Private-use codepoint detected";
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
          message =
            "Non-canonical NFC form: combining diacritical after ASCII letter";
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
          message = "Byte sequence resembles MacRoman/CP1252 encoding";
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
          message =
            "Non-NFKC homoglyph character (micro sign, ohm sign, angstrom, or \
             long s)";
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
          message = "Arabic numerals replaced by Unicode look-alikes";
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
          message = "Invalid UTF-8 continuation byte";
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
          message = "Overlong UTF-8 encoding sequence";
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
          message = "Non-breaking hyphen U+2011 present outside URLs";
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
          message = "Control characters U+0000-001F present";
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
          message = "Double-width CJK punctuation in ASCII context";
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
          message = "Sharp S (\xc3\x9f) in uppercase context; consider using SS";
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
          message = "Right-to-left mark U+200F outside RTL context";
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
          message = "Left-to-right mark U+200E unnecessary";
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
          message = "Zero-width joiner U+200D outside ligature context";
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

(* SPC-017: Missing thin space before units — detect patterns like "5cm",
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
          message = "Missing thin space before unit (e.g. 5cm should be 5\\,cm)";
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

(* SPC-010: Two spaces after sentence-ending period *)
let r_spc_010 : rule =
  let run s =
    let s = strip_math_segments s in
    (* Match ". " (period + two spaces) followed by an uppercase letter *)
    let re = Str.regexp "\\. +[A-Z]" in
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
  let run s =
    let s = strip_math_segments s in
    let re = Str.regexp "\\.[A-Z]" in
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
          message = "No space after sentence-ending period";
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
  let run s =
    let re = Str.regexp "\\\\url{\\([^}]*\\)}" in
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
          message = "Space before newline inside $$...$$ display";
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
          message = "Non-ASCII quotes inside verbatim";
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
          message = "Verbatim line > 120 characters";
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
  let re = Str.regexp {|`[^`\n]+`|} in
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
          message = "Inline code uses back-ticks instead of \\verb";
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
          message = "Unknown lstlisting language";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-011"; run }

(* VERB-012: minted block missing autogobble *)
let r_verb_012 : rule =
  let re = Str.regexp {|\\begin{minted}[ \t\n]*\(\[[^\]]*\]\)?[ \t\n]*{|} in
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
          message = "Code line > 120 glyphs";
          count = !cnt;
        }
    else None
  in
  { id = "VERB-013"; run }

(* VERB-015: Verbatim uses catcode changes instead of \verb *)
let r_verb_015 : rule =
  let re = Str.regexp {|\\catcode[ \t\n]*`|} in
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
            "`minted` without `escapeinside` while containing back-ticks";
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
          message = "`minted` lacks `linenos` in code block > 20 lines";
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
          message = "Full-width comma U+FF0C in ASCII context";
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
          message = "Full-width period U+FF0E in ASCII context";
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
    for i = 1 to n - 1 do
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
          message = "Half-width CJK punctuation in full-width context";
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
          message = "Inter-punct U+30FB outside CJK run";
          count = !cnt;
        }
    else None
  in
  { id = "CJK-014"; run }

let rules_cjk : rule list = [ r_cjk_001; r_cjk_002; r_cjk_010; r_cjk_014 ]

(* ── CMD rules: command definition checks ────────────────────────────── *)

(* CMD-002: Command redefined with \def instead of \renewcommand *)
let r_cmd_002 : rule =
  let re = Str.regexp {|\\def\\[a-zA-Z]+|} in
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
          id = "CMD-002";
          severity = Warning;
          message = "Command redefined with \\def instead of \\renewcommand";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-002"; run }

(* CMD-004: CamelCase command names discouraged *)
let r_cmd_004 : rule =
  let re = Str.regexp {|\\newcommand\|\\renewcommand\|\\def|} in
  let camel_re = Str.regexp {|{?\\[a-z]+[A-Z][a-zA-Z]*}?|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re s !i in
         let after = pos + String.length (Str.matched_string s) in
         (* skip whitespace *)
         let j = ref after in
         while !j < String.length s && (s.[!j] = ' ' || s.[!j] = '\t') do
           incr j
         done;
         (try
            let _ = Str.search_forward camel_re s !j in
            if Str.match_beginning () = !j then incr cnt
          with Not_found -> ());
         i := max (after + 1) (pos + 1)
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "CMD-004";
          severity = Info;
          message = "CamelCase command names discouraged";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-004"; run }

(* CMD-005: Single-letter macro created *)
let r_cmd_005 : rule =
  let re =
    Str.regexp {|\\\(newcommand\|renewcommand\|def\)[ \t\n]*{?\\[a-zA-Z]}|}
  in
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
          id = "CMD-005";
          severity = Warning;
          message = "Single-letter macro created (\\x)";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-005"; run }

(* CMD-006: Macro defined inside document body *)
let r_cmd_006 : rule =
  let re = Str.regexp {|\\\(newcommand\|renewcommand\|def\)[ \t\n]*{?\\|} in
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body ->
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let _ = Str.search_forward re body !i in
             incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "CMD-006";
              severity = Info;
              message = "Macro defined inside document body";
              count = !cnt;
            }
        else None
  in
  { id = "CMD-006"; run }

(* CMD-008: Macro uses \@ in name outside maketitle context *)
let r_cmd_008 : rule =
  let re =
    Str.regexp
      {|\\\(newcommand\|renewcommand\|def\)[ \t\n]*{?\\[a-zA-Z]*@[a-zA-Z]*}?|}
  in
  let run s =
    let has_makeatletter =
      try
        let _ = Str.search_forward (Str.regexp_string "\\makeatletter") s 0 in
        true
      with Not_found -> false
    in
    if has_makeatletter then None
    else
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
            id = "CMD-008";
            severity = Warning;
            message = "Macro uses \\@ in name outside maketitle context";
            count = !cnt;
          }
      else None
  in
  { id = "CMD-008"; run }

(* CMD-009: Macro name contains digits *)
let r_cmd_009 : rule =
  let re =
    Str.regexp
      {|\\\(newcommand\|renewcommand\|def\)[ \t\n]*{?\\[a-zA-Z]*[0-9]+[a-zA-Z0-9]*}?|}
  in
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
          id = "CMD-009";
          severity = Info;
          message = "Macro name contains digits";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-009"; run }

(* CMD-011: Macro defined with \def/\edef in preamble without \makeatletter
   guard *)
let r_cmd_011 : rule =
  let run s =
    (* Extract preamble: everything before \begin{document} *)
    let tag = "\\begin{document}" in
    let preamble =
      try
        let pos = Str.search_forward (Str.regexp_string tag) s 0 in
        String.sub s 0 pos
      with Not_found -> s
    in
    let re = Str.regexp {|\\\(def\|edef\)[ \t\n]*\\[a-zA-Z@]+|} in
    let has_makeatletter =
      try
        let _ =
          Str.search_forward (Str.regexp_string "\\makeatletter") preamble 0
        in
        true
      with Not_found -> false
    in
    if has_makeatletter then None
    else
      let cnt = ref 0 in
      let i = ref 0 in
      (try
         while true do
           let _ = Str.search_forward re preamble !i in
           incr cnt;
           i := Str.match_end ()
         done
       with Not_found -> ());
      if !cnt > 0 then
        Some
          {
            id = "CMD-011";
            severity = Warning;
            message =
              "Macro defined with \\def/\\edef in preamble without \
               \\makeatletter guard";
            count = !cnt;
          }
      else None
  in
  { id = "CMD-011"; run }

(* CMD-013: \def\arraystretch declared inside document body *)
let r_cmd_013 : rule =
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body ->
        let pat = Str.regexp_string "\\def\\arraystretch" in
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let _ = Str.search_forward pat body !i in
             incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "CMD-013";
              severity = Info;
              message = "\\def\\arraystretch declared inside document body";
              count = !cnt;
            }
        else None
  in
  { id = "CMD-013"; run }

let rules_cmd : rule list =
  [
    r_cmd_002;
    r_cmd_004;
    r_cmd_005;
    r_cmd_006;
    r_cmd_008;
    r_cmd_009;
    r_cmd_011;
    r_cmd_013;
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

(* ── MATH rules: mathematics-related lexical checks ──────────────── *)

(* MATH-083: Unicode minus U+2212 inside text mode — should be a hyphen-minus in
   text or $-$ / \textminus in math context. We detect U+2212 (E2 88 92) outside
   of math mode segments. *)
let r_math_083 : rule =
  let run s =
    let s_text = strip_math_segments s in
    (* U+2212 MINUS SIGN = E2 88 92 *)
    let cnt = count_substring s_text "\xe2\x88\x92" in
    if cnt > 0 then
      Some
        {
          id = "MATH-083";
          severity = Warning;
          message =
            "Unicode minus U+2212 in text mode; use hyphen-minus or math";
          count = cnt;
        }
    else None
  in
  { id = "MATH-083"; run }

(* Combined ENC + CHAR + SPC + VERB + CJK + CMD + MATH + new TYPO rules *)
let rules_enc_char_spc : rule list =
  rules_enc
  @ rules_char
  @ rules_spc
  @ rules_verb
  @ rules_cjk
  @ rules_cmd
  @ [ r_typo_062; r_math_083 ]

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

(* ── DELIM rules: delimiter matching (L1 — operate on expanded text) ── *)

(* Helper: extract math segment contents from source. Returns a list of strings,
   each being the content inside a math environment ($...$, \(...\), \[...\], or
   math-class \begin{env}...\end{env}). Unlike strip_math_segments which removes
   math, this returns only the math parts. *)
let extract_math_segments (s : string) : string list =
  let len = String.length s in
  let segments = ref [] in
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
    if not (starts_with "\\begin{" idx) then None
    else
      let name_start = idx + 7 in
      let j = ref name_start in
      while !j < len && String.unsafe_get s !j <> '}' do
        incr j
      done;
      if !j >= len then None
      else Some (String.sub s name_start (!j - name_start), !j + 1)
  in
  let rec skip_env_end name idx =
    let end_prefix = "\\end{" ^ name ^ "}" in
    let end_len = String.length end_prefix in
    if idx >= len then len
    else if (not (is_escaped idx)) && starts_with end_prefix idx then
      idx + end_len
    else skip_env_end name (idx + 1)
  in
  let in_dollar = ref false in
  let dollar_start = ref 0 in
  let rec loop i =
    if i >= len then ()
    else if !in_dollar then
      if (not (is_escaped i)) && s.[i] = '$' then (
        segments := String.sub s !dollar_start (i - !dollar_start) :: !segments;
        in_dollar := false;
        loop (i + 1))
      else loop (i + 1)
    else if (not (is_escaped i)) && s.[i] = '$' then (
      in_dollar := true;
      dollar_start := i + 1;
      loop (i + 1))
    else if (not (is_escaped i)) && starts_with "\\(" i then (
      let start = i + 2 in
      let j = ref start in
      while
        !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\)" !j)
      do
        incr j
      done;
      if !j < len - 1 then (
        segments := String.sub s start (!j - start) :: !segments;
        loop (!j + 2))
      else loop (i + 1))
    else if (not (is_escaped i)) && starts_with "\\[" i then (
      let start = i + 2 in
      let j = ref start in
      while
        !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\]" !j)
      do
        incr j
      done;
      if !j < len - 1 then (
        segments := String.sub s start (!j - start) :: !segments;
        loop (!j + 2))
      else loop (i + 1))
    else if (not (is_escaped i)) && starts_with "\\begin{" i then
      match parse_begin i with
      | Some (name, after_begin) when is_math_env name ->
          let end_pos = skip_env_end name after_begin in
          let end_tag = "\\end{" ^ name ^ "}" in
          let content_end = end_pos - String.length end_tag in
          if content_end > after_begin then
            segments :=
              String.sub s after_begin (content_end - after_begin) :: !segments;
          loop end_pos
      | _ -> loop (i + 1)
    else loop (i + 1)
  in
  loop 0;
  List.rev !segments

(* DELIM-001: Unmatched delimiters { } after expansion. Count opening vs closing
   braces, ignoring escaped \{ and \}. *)
let l1_delim_001_rule : rule =
  let run s =
    let n = String.length s in
    let opens = ref 0 in
    let closes = ref 0 in
    let i = ref 0 in
    while !i < n do
      let c = s.[!i] in
      if c = '\\' && !i + 1 < n then (* skip escaped characters *)
        i := !i + 2
      else if c = '{' then (
        incr opens;
        incr i)
      else if c = '}' then (
        incr closes;
        incr i)
      else incr i
    done;
    let imbalance = abs (!opens - !closes) in
    if imbalance > 0 then
      Some
        {
          id = "DELIM-001";
          severity = Error;
          message = "Unmatched delimiters { } after macro expansion";
          count = imbalance;
        }
    else None
  in
  { id = "DELIM-001"; run }

(* DELIM-002: Extra closing } detected. Scan left-to-right tracking brace depth;
   if depth ever goes negative, count those positions. *)
let l1_delim_002_rule : rule =
  let run s =
    let n = String.length s in
    let depth = ref 0 in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let c = s.[!i] in
      if c = '\\' && !i + 1 < n then i := !i + 2
      else if c = '{' then (
        incr depth;
        incr i)
      else if c = '}' then (
        decr depth;
        if !depth < 0 then (
          incr cnt;
          depth := 0);
        incr i)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-002";
          severity = Error;
          message = "Extra closing } detected";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-002"; run }

(* DELIM-003: Unmatched \left without \right in math mode *)
let l1_delim_003_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let lefts = count_substring seg "\\left" in
        let rights = count_substring seg "\\right" in
        if lefts > rights then cnt := !cnt + (lefts - rights))
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-003";
          severity = Error;
          message = "Unmatched \\left without \\right";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-003"; run }

(* DELIM-004: Unmatched \right without \left in math mode *)
let l1_delim_004_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let lefts = count_substring seg "\\left" in
        let rights = count_substring seg "\\right" in
        if rights > lefts then cnt := !cnt + (rights - lefts))
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-004";
          severity = Error;
          message = "Unmatched \\right without \\left";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-004"; run }

(* DELIM-005: Mismatched parenthesis sizing (\big vs \Bigg) — detect \bigl/\bigr
   paired with \Biggl/\Biggr or similar size mismatches. *)
let l1_delim_005_rule : rule =
  let size_of s =
    if count_substring s "\\Bigg" > 0 then 4
    else if count_substring s "\\bigg" > 0 then 3
    else if count_substring s "\\Big" > 0 then 2
    else if count_substring s "\\big" > 0 then 1
    else 0
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Look for \left...\right pairs and check if sizing commands within
           differ *)
        let re_left = Str.regexp {|\\left|} in
        let re_right = Str.regexp {|\\right|} in
        let lefts = ref [] and rights = ref [] in
        let i = ref 0 in
        (try
           while true do
             let p = Str.search_forward re_left seg !i in
             lefts := p :: !lefts;
             i := p + 5
           done
         with Not_found -> ());
        i := 0;
        (try
           while true do
             let p = Str.search_forward re_right seg !i in
             rights := p :: !rights;
             i := p + 6
           done
         with Not_found -> ());
        (* For each left-right pair, check sizing around them *)
        let left_list = List.rev !lefts and right_list = List.rev !rights in
        let pairs = min (List.length left_list) (List.length right_list) in
        let ll = Array.of_list left_list and rl = Array.of_list right_list in
        for k = 0 to pairs - 1 do
          let lp = ll.(k) and rp = rl.(k) in
          (* Check context around each delimiter for sizing commands *)
          let l_ctx = String.sub seg (max 0 (lp - 10)) (min 10 (max 0 lp)) in
          let r_ctx = String.sub seg (max 0 (rp - 10)) (min 10 (max 0 rp)) in
          let l_size = size_of l_ctx and r_size = size_of r_ctx in
          if l_size > 0 && r_size > 0 && l_size <> r_size then incr cnt
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-005";
          severity = Info;
          message =
            "Mismatched parenthesis sizing (e.g. \\big vs \\Bigg in same pair)";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-005"; run }

(* DELIM-006: \big delimiters used outside display math — detect \big, \bigl,
   \bigr etc. in inline math ($...$, \(...\)) rather than display math. *)
let l1_delim_006_rule : rule =
  let re_big = Str.regexp {|\\[Bb]ig[lrmg]?\b\|\\[Bb]igg[lrmg]?\b|} in
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    (* Scan for inline math contexts and look for \big within them *)
    let starts_with prefix idx =
      let plen = String.length prefix in
      idx + plen <= len && String.sub s idx plen = prefix
    in
    let is_escaped idx = idx > 0 && s.[idx - 1] = '\\' in
    let i = ref 0 in
    while !i < len do
      (* Inline math: $...$ (not $$) *)
      if
        (not (is_escaped !i))
        && s.[!i] = '$'
        && (!i + 1 >= len || s.[!i + 1] <> '$')
      then (
        let start = !i + 1 in
        let j = ref start in
        while
          !j < len
          && not
               ((not (is_escaped !j))
               && s.[!j] = '$'
               && (!j + 1 >= len || s.[!j + 1] <> '$'))
        do
          incr j
        done;
        if !j < len then (
          let inline_seg = String.sub s start (!j - start) in
          let k = ref 0 in
          (try
             while true do
               let _ = Str.search_forward re_big inline_seg !k in
               incr cnt;
               k := Str.match_end ()
             done
           with Not_found -> ());
          i := !j + 1)
        else i := !i + 1)
      else if (not (is_escaped !i)) && starts_with "\\(" !i then (
        let start = !i + 2 in
        let j = ref start in
        while
          !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\)" !j)
        do
          incr j
        done;
        if !j < len - 1 then (
          let inline_seg = String.sub s start (!j - start) in
          let k = ref 0 in
          (try
             while true do
               let _ = Str.search_forward re_big inline_seg !k in
               incr cnt;
               k := Str.match_end ()
             done
           with Not_found -> ());
          i := !j + 2)
        else i := !i + 1)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-006";
          severity = Info;
          message = "\\big delimiters used in inline math (prefer display math)";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-006"; run }

(* DELIM-007: Angle bracket \langle without matching \rangle in math *)
let l1_delim_007_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let langles = count_substring seg "\\langle" in
        let rangles = count_substring seg "\\rangle" in
        let diff = abs (langles - rangles) in
        if diff > 0 then cnt := !cnt + diff)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-007";
          severity = Error;
          message = "Unmatched \\langle / \\rangle pair";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-007"; run }

(* DELIM-008: Empty \left. ... \right. pair — redundant invisible delimiters *)
let l1_delim_008_rule : rule =
  let re = Str.regexp {|\\left\.[ \t\n]*\\right\.|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _ = Str.search_forward re seg !i in
            incr cnt;
            i := Str.match_end ()
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-008";
          severity = Info;
          message =
            "Empty \\left. ... \\right. pair (redundant invisible delimiters)";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-008"; run }

(* DELIM-009: Nested delimiter type mismatch — e.g. { ... ( ... ) ... } where
   brace group contains parenthesized expression or vice versa in math *)
let l1_delim_009_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let stack = Stack.create () in
        let i = ref 0 in
        while !i < n do
          let c = seg.[!i] in
          if c = '\\' && !i + 1 < n then i := !i + 2
          else if c = '{' || c = '(' || c = '[' then (
            Stack.push c stack;
            incr i)
          else if c = '}' || c = ')' || c = ']' then (
            let expected = match c with '}' -> '{' | ')' -> '(' | _ -> '[' in
            if (not (Stack.is_empty stack)) && Stack.top stack <> expected then
              incr cnt;
            if not (Stack.is_empty stack) then ignore (Stack.pop stack);
            incr i)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-009";
          severity = Warning;
          message = "Nested delimiter type mismatch in math mode";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-009"; run }

(* DELIM-010: Display math uses \big instead of \Big — in display math contexts,
   convention is to use capital sizing commands *)
let l1_delim_010_rule : rule =
  let re_small_big = Str.regexp {|\\big[lrmg]?\b|} in
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let starts_with prefix idx =
      let plen = String.length prefix in
      idx + plen <= len && String.sub s idx plen = prefix
    in
    let is_escaped idx = idx > 0 && s.[idx - 1] = '\\' in
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
        "displaymath";
      ]
    in
    (* Check \[...\] display math *)
    let i = ref 0 in
    while !i < len do
      if (not (is_escaped !i)) && starts_with "\\[" !i then (
        let start = !i + 2 in
        let j = ref start in
        while
          !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\]" !j)
        do
          incr j
        done;
        if !j < len - 1 then (
          let seg = String.sub s start (!j - start) in
          let k = ref 0 in
          (try
             while true do
               let _ = Str.search_forward re_small_big seg !k in
               incr cnt;
               k := Str.match_end ()
             done
           with Not_found -> ());
          i := !j + 2)
        else i := !i + 1)
      else incr i
    done;
    (* Check display math environments *)
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            let k = ref 0 in
            try
              while true do
                let _ = Str.search_forward re_small_big blk !k in
                incr cnt;
                k := Str.match_end ()
              done
            with Not_found -> ())
          blocks)
      math_envs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-010";
          severity = Info;
          message =
            "Display math uses \\big instead of \\Big (prefer capital sizing)";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-010"; run }

(* DELIM-011: \middle delimiter used without \left...\right pair *)
let l1_delim_011_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let middles = count_substring seg "\\middle" in
        if middles > 0 then
          (* Check if there are sufficient \left..\right pairs *)
          let lefts = count_substring seg "\\left" in
          let rights = count_substring seg "\\right" in
          let pairs = min lefts rights in
          if middles > 0 && pairs = 0 then cnt := !cnt + middles)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-011";
          severity = Warning;
          message = "\\middle delimiter used without \\left...\\right pair";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-011"; run }

(* ═══════════════════════════════════════════════════════════════════════════
   SCRIPT family — L1 subscript / superscript validators SCRIPT-001 through
   SCRIPT-022
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Helper: extract inline math segments only ($...$ and \(...\)) *)
let extract_inline_math_segments (s : string) : string list =
  let len = String.length s in
  let segments = ref [] in
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
  let i = ref 0 in
  while !i < len do
    if
      (not (is_escaped !i))
      && s.[!i] = '$'
      && (!i + 1 >= len || s.[!i + 1] <> '$')
    then (
      let start = !i + 1 in
      let j = ref start in
      while
        !j < len
        && not
             ((not (is_escaped !j))
             && s.[!j] = '$'
             && (!j + 1 >= len || s.[!j + 1] <> '$'))
      do
        incr j
      done;
      if !j < len then (
        segments := String.sub s start (!j - start) :: !segments;
        i := !j + 1)
      else i := !i + 1)
    else if (not (is_escaped !i)) && starts_with "\\(" !i then (
      let start = !i + 2 in
      let j = ref start in
      while
        !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\)" !j)
      do
        incr j
      done;
      if !j < len - 1 then (
        segments := String.sub s start (!j - start) :: !segments;
        i := !j + 2)
      else i := !i + 1)
    else incr i
  done;
  List.rev !segments

(* Helper: count regex matches in a string *)
let count_re_matches (re : Str.regexp) (s : string) : int =
  let cnt = ref 0 in
  let i = ref 0 in
  (try
     while true do
       let _ = Str.search_forward re s !i in
       incr cnt;
       i := Str.match_end ()
     done
   with Not_found -> ());
  !cnt

(* SCRIPT-001: Multi-char subscript without braces — e.g. _ab where the
   subscript has 2+ chars without { } *)
let l1_script_001_rule : rule =
  (* Match _X where X is 2+ alphanumeric chars not wrapped in braces *)
  let re = Str.regexp {|_\([A-Za-z0-9][A-Za-z0-9]+\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            (* Make sure it's not _{ ... } — check char before match group *)
            if pos + 1 < n && seg.[pos + 1] <> '{' then incr cnt;
            i := Str.match_end ()
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-001";
          severity = Warning;
          message = "Multi-character subscript without braces";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-001"; run }

(* SCRIPT-002: Superscript dash typed as unicode non-breaking hyphen U+2011
   instead of \textsuperscript{--} *)
let l1_script_002_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          (* Check for ^ followed by U+2011 (non-breaking hyphen: \xe2\x80\x91)
             or U+2010 (hyphen: \xe2\x80\x90) *)
          if
            seg.[!i] = '^'
            && !i + 3 < n
            && seg.[!i + 1] = '\xe2'
            && seg.[!i + 2] = '\x80'
            && (seg.[!i + 3] = '\x91' || seg.[!i + 3] = '\x90')
          then (
            incr cnt;
            i := !i + 4)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-002";
          severity = Info;
          message =
            "Superscript dash typed as Unicode hyphen instead of \
             \\textsuperscript{--}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-002"; run }

(* SCRIPT-003: Comma-separated superscripts lack braces — e.g. ^a,b instead of
   ^{a,b} *)
let l1_script_003_rule : rule =
  let re = Str.regexp {|\^\([A-Za-z0-9],[A-Za-z0-9,]+\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-003";
          severity = Warning;
          message = "Comma-separated superscripts lack braces";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-003"; run }

(* SCRIPT-004: Subscript after prime notation mis-ordered — e.g. f'_i instead of
   f_i' *)
let l1_script_004_rule : rule =
  let re = Str.regexp {|''+_\|'_|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-004";
          severity = Info;
          message = "Subscript after prime notation is mis-ordered";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-004"; run }

(* SCRIPT-005: Superscript uses letter l instead of \ell *)
let l1_script_005_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if seg.[!i] = '^' then
            let j = !i + 1 in
            if j < n then
              if seg.[j] = 'l' then (
                (* Make sure next char is not alphanumeric (standalone l) *)
                let after = j + 1 in
                let is_end =
                  after >= n
                  ||
                  let c = seg.[after] in
                  not
                    ((c >= 'a' && c <= 'z')
                    || (c >= 'A' && c <= 'Z')
                    || (c >= '0' && c <= '9'))
                in
                if is_end then incr cnt;
                i := after)
              else if seg.[j] = '{' then (
                (* check for ^{l} *)
                if j + 2 < n && seg.[j + 1] = 'l' && seg.[j + 2] = '}' then
                  incr cnt;
                i := j + 1)
              else i := j + 1
            else i := j + 1
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-005";
          severity = Info;
          message = "Superscript uses letter 'l' instead of \\ell";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-005"; run }

(* SCRIPT-006: Degree symbol typed ° (U+00B0) instead of ^\circ in math *)
let l1_script_006_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* U+00B0 = \xc2\xb0 in UTF-8 *)
        cnt := !cnt + count_substring seg "\xc2\xb0")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-006";
          severity = Info;
          message =
            "Degree symbol typed as Unicode ° instead of ^{\\circ} in math";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-006"; run }

(* SCRIPT-007: Subscript text not wrapped in \text{} — e.g. x_{max} where "max"
   is a word (3+ alpha chars) without \text *)
let l1_script_007_rule : rule =
  let re = Str.regexp {|_{\([A-Za-z][A-Za-z][A-Za-z][A-Za-z]*\)}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            let matched = Str.matched_group 1 seg in
            let next_i = Str.match_end () in
            (* Exclude common math abbreviations *)
            let is_operator =
              List.mem matched
                [
                  "min";
                  "max";
                  "lim";
                  "inf";
                  "sup";
                  "det";
                  "dim";
                  "ker";
                  "log";
                  "exp";
                  "sin";
                  "cos";
                  "tan";
                  "arg";
                  "deg";
                  "gcd";
                  "hom";
                  "mod";
                  "Pr";
                ]
            in
            (if not is_operator then
               (* Check prefix for \text{, \mathrm{, \operatorname{ using string
                  operations (not Str) to avoid clobbering global match state *)
               let prefix_start = max 0 (pos - 16) in
               let prefix =
                 String.sub seg prefix_start (pos - prefix_start + 2)
               in
               let has_wrapper =
                 count_substring prefix "\\text{"
                 + count_substring prefix "\\mathrm{"
                 + count_substring prefix "\\operatorname{"
                 > 0
               in
               if not has_wrapper then incr cnt);
            i := next_i
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-007";
          severity = Warning;
          message = "Subscript text not wrapped in \\text{} or \\mathrm{}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-007"; run }

(* SCRIPT-008: Chemical formula lacks \mathrm{} in subscript — e.g. $H_2O$ vs
   $\mathrm{H}_2\mathrm{O}$ — detects element+subscript digit pattern outside
   \mathrm{} or \ce{} *)
let l1_script_008_rule : rule =
  (* Pattern: uppercase letter optionally followed by lowercase, then _digit
     e.g. H_2, Na_2, O_2 — these look like chemical formulas *)
  let re = Str.regexp {|\([A-Z][a-z]?\)_\([0-9]+\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Skip if inside \ce{} or \mathrm{} context *)
        if
          count_substring seg "\\ce{" = 0 && count_substring seg "\\mathrm{" = 0
        then cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-008";
          severity = Info;
          message = "Chemical formula in subscript lacks \\mathrm{} wrapping";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-008"; run }

(* SCRIPT-009: Isotope superscript mass number missing — e.g. ^{}_{Z}X or just
   _ZX without a mass number superscript *)
let l1_script_009_rule : rule =
  (* Detect: ^{}_ or ^{ }_ pattern indicating empty mass number *)
  let re = Str.regexp {|\^{[ ]*}_{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-009";
          severity = Info;
          message = "Isotope notation has empty superscript mass number";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-009"; run }

(* SCRIPT-010: Use of \limits on inline operator — \limits in inline math
   ($...$, \(...\)) forces display-style limits *)
let l1_script_010_rule : rule =
  let re_limits = Str.regexp {|\\limits|} in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_re_matches re_limits seg)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-010";
          severity = Info;
          message = "\\limits used on inline operator (prefer display math)";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-010"; run }

(* SCRIPT-011: Nested superscript three levels deep — e.g. x^{a^{b^{c}}} *)
let l1_script_011_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let depth = ref 0 in
        let max_depth = ref 0 in
        let i = ref 0 in
        while !i < n do
          if seg.[!i] = '\\' then i := !i + 2
          else if seg.[!i] = '^' then (
            incr depth;
            if !depth > !max_depth then max_depth := !depth;
            incr i)
          else if seg.[!i] = '}' then (
            if !depth > 0 then decr depth;
            incr i)
          else incr i
        done;
        if !max_depth >= 3 then incr cnt)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-011";
          severity = Warning;
          message = "Nested superscript three or more levels deep";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-011"; run }

(* SCRIPT-012: Prime notation f''' (> 3 primes) — prefer ^{(n)} *)
let l1_script_012_rule : rule =
  let re = Str.regexp {|''''|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-012";
          severity = Info;
          message =
            "More than 3 prime marks — prefer ^{(n)} derivative notation";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-012"; run }

(* SCRIPT-013: Plus/minus typed directly in subscript — e.g. x_{+} or x_{-}
   where \pm or \mp would be more appropriate *)
let l1_script_013_rule : rule =
  let re = Str.regexp {|_{\([+-]\)}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-013";
          severity = Info;
          message =
            "Plus/minus typed directly in subscript (consider \\pm or \\mp)";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-013"; run }

(* SCRIPT-014: Logarithm base subscript italic — \log_x where x is a bare italic
   letter, should be \log_{x} or upright *)
let l1_script_014_rule : rule =
  (* Match \log_ followed by a single letter NOT in braces *)
  let re = Str.regexp {|\\log_\([A-Za-z]\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            (* Check it's not \log_{...} — the char after \log_ should not be
               { *)
            let after_underscore = pos + 5 in
            if
              after_underscore < String.length seg
              && seg.[after_underscore] <> '{'
            then incr cnt;
            i := Str.match_end ()
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-014";
          severity = Info;
          message = "Logarithm base subscript is bare italic letter";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-014"; run }

(* SCRIPT-015: Time derivative dot mis-aligned — \dot or \ddot used in
   subscript/superscript context *)
let l1_script_015_rule : rule =
  let re = Str.regexp {|[_^]{\\d?dot{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-015";
          severity = Info;
          message = "Time derivative \\dot/\\ddot used inside sub/superscript";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-015"; run }

(* SCRIPT-016: Prime on Greek letter typed '' not ^\prime — e.g. \alpha''
   instead of \alpha^{\prime\prime} *)
let l1_script_016_rule : rule =
  let greeks =
    [
      "\\alpha";
      "\\beta";
      "\\gamma";
      "\\delta";
      "\\epsilon";
      "\\zeta";
      "\\eta";
      "\\theta";
      "\\iota";
      "\\kappa";
      "\\lambda";
      "\\mu";
      "\\nu";
      "\\xi";
      "\\pi";
      "\\rho";
      "\\sigma";
      "\\tau";
      "\\upsilon";
      "\\phi";
      "\\chi";
      "\\psi";
      "\\omega";
      "\\Gamma";
      "\\Delta";
      "\\Theta";
      "\\Lambda";
      "\\Xi";
      "\\Pi";
      "\\Sigma";
      "\\Upsilon";
      "\\Phi";
      "\\Psi";
      "\\Omega";
      "\\varepsilon";
      "\\vartheta";
      "\\varpi";
      "\\varrho";
      "\\varsigma";
      "\\varphi";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun g ->
            let pat = g ^ "''" in
            cnt := !cnt + count_substring seg pat)
          greeks)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-016";
          severity = Info;
          message =
            "Prime on Greek letter typed as '' instead of ^{\\prime\\prime}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-016"; run }

(* SCRIPT-017: Inconsistent order of sub/superscripts — detects when some atoms
   use x_a^b and others use x^b_a in the same document *)
let l1_script_017_rule : rule =
  let re_sub_sup =
    Str.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)\^\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let re_sup_sub =
    Str.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let run s =
    let math_segs = extract_math_segments s in
    let sub_sup_count = ref 0 in
    let sup_sub_count = ref 0 in
    List.iter
      (fun seg ->
        sub_sup_count := !sub_sup_count + count_re_matches re_sub_sup seg;
        sup_sub_count := !sup_sub_count + count_re_matches re_sup_sub seg)
      math_segs;
    (* Fire only if both orderings are used *)
    if !sub_sup_count > 0 && !sup_sub_count > 0 then
      Some
        {
          id = "SCRIPT-017";
          severity = Info;
          message =
            "Inconsistent order of sub/superscripts (mixed _a^b and ^b_a)";
          count = min !sub_sup_count !sup_sub_count;
        }
    else None
  in
  { id = "SCRIPT-017"; run }

(* SCRIPT-018: Degree symbol in superscript without braces — e.g. ^\circ without
   braces: should be ^{\circ} *)
let l1_script_018_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Match ^\\circ not preceded by ^{ *)
        let n = String.length seg in
        let target = "^\\circ" in
        let tlen = String.length target in
        let i = ref 0 in
        while !i + tlen <= n do
          if String.sub seg !i tlen = target then (
            (* Check it's not ^{\circ} *)
            if !i + 1 < n && seg.[!i + 1] <> '{' then incr cnt;
            i := !i + tlen)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-018";
          severity = Warning;
          message = "^\\circ without braces — use ^{\\circ}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-018"; run }

(* SCRIPT-019: Double prime '' instead of ^{\prime\prime} *)
let l1_script_019_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i + 1 < n do
          if seg.[!i] = '\'' && seg.[!i + 1] = '\'' then
            if
              (* Skip triple+ primes — those are handled by SCRIPT-012/022 *)
              !i + 2 < n && seg.[!i + 2] = '\''
            then
              (* skip the run of primes *)
              while !i < n && seg.[!i] = '\'' do
                incr i
              done
            else (
              incr cnt;
              i := !i + 2)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-019";
          severity = Info;
          message = "Double prime '' used instead of ^{\\prime\\prime}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-019"; run }

(* SCRIPT-020: Subscript text italic instead of \mathrm — e.g. $T_{eff}$ where
   the subscript is a multi-char word rendered in italic by default, should use
   \mathrm{eff} *)
let l1_script_020_rule : rule =
  (* Reuses the same detection as SCRIPT-007 but focuses specifically on
     subscripts that are abbreviation-like 2-3 char lowercase words *)
  let re = Str.regexp {|_{\([a-z][a-z]+\)}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            let matched = Str.matched_group 1 seg in
            let next_i = Str.match_end () in
            (* Exclude single-letter and known math operators *)
            let is_operator =
              List.mem matched
                [
                  "min";
                  "max";
                  "lim";
                  "inf";
                  "sup";
                  "det";
                  "dim";
                  "ker";
                  "log";
                  "exp";
                  "sin";
                  "cos";
                  "tan";
                  "arg";
                  "deg";
                  "gcd";
                  "hom";
                  "mod";
                ]
            in
            (if (not is_operator) && String.length matched >= 2 then
               (* Check not already wrapped in \mathrm or \text *)
               let prefix_start = max 0 (pos - 9) in
               let prefix =
                 String.sub seg prefix_start (pos - prefix_start + 2)
               in
               if
                 count_substring prefix "\\mathrm{" = 0
                 && count_substring prefix "\\text{" = 0
               then incr cnt);
            i := next_i
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-020";
          severity = Info;
          message = "Subscript text is italic — consider \\mathrm{} for upright";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-020"; run }

(* SCRIPT-021: Sub-sup order not canonical — a_{b}^{c} vs a^{c}_{b} — flag when
   a_{...}^{...} is used (canonical is a^{...}_{...} per convention) *)
let l1_script_021_rule : rule =
  let re = Str.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)\^\({[^}]*}\|[A-Za-z0-9]\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-021";
          severity = Warning;
          message =
            "Sub/superscript order is not canonical — prefer a^{c}_{b} over \
             a_{b}^{c}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-021"; run }

(* SCRIPT-022: Superscript prime stacked > 3 — prefer ^{(n)} — similar to
   SCRIPT-012 but specifically for ^{'''...} notation *)
let l1_script_022_rule : rule =
  let re = Str.regexp {|\^{''''|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-022";
          severity = Info;
          message =
            "Superscript prime stacked > 3 in braces — prefer ^{(n)} notation";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-022"; run }

(* ═══════════════════════════════════════════════════════════════════════════
   MATH family (L1) — Core math-token validators MATH-009 through MATH-022
   ═══════════════════════════════════════════════════════════════════════════ *)

(* MATH-009: Bare 'sin/log/exp' in math — use \sin, \log, \exp etc. *)
let l1_math_009_rule : rule =
  let operators =
    [
      "sin";
      "cos";
      "tan";
      "cot";
      "sec";
      "csc";
      "log";
      "exp";
      "ln";
      "lim";
      "inf";
      "sup";
      "min";
      "max";
      "det";
      "dim";
      "ker";
      "hom";
      "arg";
      "deg";
      "gcd";
      "Pr";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun op ->
            let oplen = String.length op in
            let n = String.length seg in
            let i = ref 0 in
            while !i + oplen <= n do
              if String.sub seg !i oplen = op then (
                (* Check it's NOT preceded by \ (i.e. not \sin already) *)
                let preceded_by_backslash = !i > 0 && seg.[!i - 1] = '\\' in
                (* Check word boundary before: not alphanumeric *)
                let boundary_before =
                  !i = 0
                  ||
                  let c = seg.[!i - 1] in
                  not
                    ((c >= 'a' && c <= 'z')
                    || (c >= 'A' && c <= 'Z')
                    || (c >= '0' && c <= '9'))
                in
                (* Check word boundary after: not alphanumeric *)
                let boundary_after =
                  !i + oplen >= n
                  ||
                  let c = seg.[!i + oplen] in
                  not
                    ((c >= 'a' && c <= 'z')
                    || (c >= 'A' && c <= 'Z')
                    || (c >= '0' && c <= '9'))
                in
                if
                  (not preceded_by_backslash)
                  && boundary_before
                  && boundary_after
                then incr cnt;
                i := !i + oplen)
              else incr i
            done)
          operators)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-009";
          severity = Warning;
          message =
            "Bare function name in math mode — use \\sin, \\log, \\exp etc.";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-009"; run }

(* MATH-010: Division symbol ÷ (U+00F7) used — prefer \frac or solidus *)
let l1_math_010_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    (* U+00F7 = \xc3\xb7 in UTF-8 *)
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\xc3\xb7")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-010";
          severity = Warning;
          message =
            "Division symbol ÷ used in math — prefer \\frac or solidus /";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-010"; run }

(* MATH-011: Vector notation inconsistent within equation — detects when both
   \vec{} and \mathbf{} are used for vectors in the same document *)
let l1_math_011_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let vec_count = ref 0 in
    let mathbf_count = ref 0 in
    List.iter
      (fun seg ->
        vec_count := !vec_count + count_substring seg "\\vec{";
        mathbf_count := !mathbf_count + count_substring seg "\\mathbf{")
      math_segs;
    if !vec_count > 0 && !mathbf_count > 0 then
      Some
        {
          id = "MATH-011";
          severity = Info;
          message =
            "Inconsistent vector notation — both \\vec{} and \\mathbf{} used";
          count = min !vec_count !mathbf_count;
        }
    else None
  in
  { id = "MATH-011"; run }

(* MATH-012: Multi-letter function not in roman (\operatorname{}) — detects
   sequences of 2+ lowercase letters in math that look like function names but
   aren't standard operators *)
let l1_math_012_rule : rule =
  let re = Str.regexp {|\([a-z][a-z]+\)|} in
  let known_operators =
    [
      "sin";
      "cos";
      "tan";
      "cot";
      "sec";
      "csc";
      "log";
      "exp";
      "ln";
      "lim";
      "inf";
      "sup";
      "min";
      "max";
      "det";
      "dim";
      "ker";
      "hom";
      "arg";
      "deg";
      "gcd";
      "mod";
      "arcsin";
      "arccos";
      "arctan";
      "sinh";
      "cosh";
      "tanh";
      "coth";
      "sech";
      "csch";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            let matched = Str.matched_group 1 seg in
            let next_i = Str.match_end () in
            (* Skip if preceded by backslash or inside \text{}/\mathrm{} *)
            let preceded_by_backslash = pos > 0 && seg.[pos - 1] = '\\' in
            let is_known = List.mem matched known_operators in
            (* Skip 2-char that could just be variables like dx, dy *)
            let is_short_var = String.length matched <= 2 in
            (if
               (not preceded_by_backslash) && (not is_known) && not is_short_var
             then
               (* Check prefix for \text{, \mathrm{, \operatorname{ *)
               let prefix_start = max 0 (pos - 16) in
               let prefix = String.sub seg prefix_start (pos - prefix_start) in
               let has_wrapper =
                 count_substring prefix "\\text{"
                 + count_substring prefix "\\mathrm{"
                 + count_substring prefix "\\operatorname{"
                 > 0
               in
               if not has_wrapper then incr cnt);
            i := next_i
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-012";
          severity = Warning;
          message =
            "Multi-letter function name not in \\operatorname{} or \\mathrm{}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-012"; run }

(* MATH-013: Differential d not typeset roman — detects bare 'd' before a
   variable in integrands, e.g. \int f(x) dx where d should be \mathrm{d} *)
let l1_math_013_rule : rule =
  let re = Str.regexp {| d\([A-Za-z]\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Only trigger if segment contains integral-like context *)
        if
          count_substring seg "\\int" > 0
          || count_substring seg "\\iint" > 0
          || count_substring seg "\\iiint" > 0
          || count_substring seg "\\oint" > 0
        then
          let i = ref 0 in
          try
            while true do
              let pos = Str.search_forward re seg !i in
              let next_i = Str.match_end () in
              (* Make sure it's not already \mathrm{d} *)
              let prefix_start = max 0 (pos - 9) in
              let prefix =
                String.sub seg prefix_start (pos - prefix_start + 1)
              in
              if
                count_substring prefix "\\mathrm{" = 0
                && count_substring prefix "\\,d" = 0
              then incr cnt;
              i := next_i
            done
          with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-013";
          severity = Info;
          message = "Differential d not typeset in roman — consider \\mathrm{d}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-013"; run }

(* MATH-014: Inline \frac in running text — \frac inside $...$ or \(...\) can be
   hard to read *)
let l1_math_014_rule : rule =
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Count \frac occurrences, exclude \tfrac and \dfrac *)
        let total_frac = count_substring seg "\\frac{" in
        let tfrac = count_substring seg "\\tfrac{" in
        let dfrac = count_substring seg "\\dfrac{" in
        let bare_frac = total_frac - tfrac - dfrac in
        if bare_frac > 0 then cnt := !cnt + bare_frac)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-014";
          severity = Info;
          message =
            "\\frac used in inline math — consider \\tfrac or display math";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-014"; run }

(* MATH-015: \stackrel used — prefer \overset *)
let l1_math_015_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\stackrel{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-015";
          severity = Warning;
          message = "\\stackrel used — prefer \\overset";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-015"; run }

(* MATH-016: Nested subscripts without braces — e.g. x_i_j instead of x_{i_j} or
   x_{i,j} *)
let l1_math_016_rule : rule =
  let re = Str.regexp {|_\([A-Za-z0-9]\)_|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-016";
          severity = Warning;
          message = "Nested subscripts without braces — use _{i_j} or _{i,j}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-016"; run }

(* MATH-017: Mismatched \left\{ ... \right] pair — left and right delimiters
   don't match type *)
let l1_math_017_rule : rule =
  let left_delims =
    [
      ("\\left\\{", "brace");
      ("\\left\\[", "bracket");
      ("\\left[", "bracket");
      ("\\left(", "paren");
      ("\\left\\langle", "angle");
      ("\\left\\|", "double_bar");
      ("\\left\\lfloor", "floor");
      ("\\left\\lceil", "ceil");
      ("\\left.", "invisible");
    ]
  in
  let right_delims =
    [
      ("\\right\\}", "brace");
      ("\\right\\]", "bracket");
      ("\\right]", "bracket");
      ("\\right)", "paren");
      ("\\right\\rangle", "angle");
      ("\\right\\|", "double_bar");
      ("\\right\\rfloor", "floor");
      ("\\right\\rceil", "ceil");
      ("\\right.", "invisible");
    ]
  in
  let starts_with s idx prefix =
    let plen = String.length prefix in
    idx + plen <= String.length s && String.sub s idx plen = prefix
  in
  let find_delim_type delims s idx =
    List.fold_left
      (fun acc (prefix, dtype) ->
        match acc with
        | Some _ -> acc
        | None ->
            if starts_with s idx prefix then Some (dtype, String.length prefix)
            else None)
      None delims
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        (* Collect left delimiters in order *)
        let lefts = ref [] in
        let i = ref 0 in
        while !i < n do
          match find_delim_type left_delims seg !i with
          | Some (dtype, plen) ->
              lefts := dtype :: !lefts;
              i := !i + plen
          | None -> incr i
        done;
        let lefts = List.rev !lefts in
        (* Collect right delimiters in order *)
        let rights = ref [] in
        i := 0;
        while !i < n do
          match find_delim_type right_delims seg !i with
          | Some (dtype, plen) ->
              rights := dtype :: !rights;
              i := !i + plen
          | None -> incr i
        done;
        let rights = List.rev !rights in
        (* Compare paired delimiters *)
        let rec check ls rs =
          match (ls, rs) with
          | l :: ls', r :: rs' ->
              if l <> "invisible" && r <> "invisible" && l <> r then incr cnt;
              check ls' rs'
          | _ -> ()
        in
        check lefts rights)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-017";
          severity = Error;
          message = "Mismatched \\left/\\right delimiter types";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-017"; run }

(* MATH-018: π written numerically as 3.14... in math *)
let l1_math_018_rule : rule =
  let re = Str.regexp {|3\.14[0-9]*|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-018";
          severity = Info;
          message = "Numerical approximation of π (3.14...) — use \\pi instead";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-018"; run }

(* MATH-019: Inline stacked ^_ order wrong — same concept as SCRIPT-021 but
   specifically for the pattern where _ immediately follows ^ without braces in
   inline math, e.g. $\sum^n_i$ instead of $\sum_{i}^{n}$ *)
let l1_math_019_rule : rule =
  let re = Str.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|} in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-019";
          severity = Warning;
          message = "Inline math has ^{sup}_{sub} order — prefer _{sub}^{sup}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-019"; run }

(* MATH-020: Missing \cdot between coefficient and vector — detects digit
   immediately followed by \vec or \mathbf without \cdot *)
let l1_math_020_rule : rule =
  let re = Str.regexp {|[0-9]\(\\vec{\|\\mathbf{\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-020";
          severity = Info;
          message = "Missing \\cdot between coefficient and vector notation";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-020"; run }

(* MATH-021: Absolute value bars |x| instead of \lvert ... \rvert *)
let l1_math_021_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if seg.[!i] = '|' then (
            if
              (* Skip \| (double bar) and already-typed \lvert/\rvert *)
              !i > 0 && seg.[!i - 1] = '\\'
            then incr i
            else
              (* Look for matching closing | *)
              let j = ref (!i + 1) in
              while !j < n && seg.[!j] <> '|' do
                if seg.[!j] = '\\' then j := !j + 2 else incr j
              done;
              if !j < n then (
                (* Found |...| pair — this should be \lvert..\rvert *)
                incr cnt;
                i := !j + 1)
              else i := !i + 1)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-021";
          severity = Info;
          message = "Absolute value bars |x| — prefer \\lvert x \\rvert";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-021"; run }

(* MATH-022: Bold math italic without \bm or \mathbf — detects when \textbf is
   used inside math mode for bold math *)
let l1_math_022_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\textbf{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-022";
          severity = Info;
          message = "\\textbf used in math mode — use \\mathbf or \\bm instead";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-022"; run }

(* MATH-030: Overuse of \displaystyle in inline math — using \displaystyle in
   $...$ or \(...\) hurts line spacing *)
let l1_math_030_rule : rule =
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\displaystyle")
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-030";
          severity = Info;
          message =
            "\\displaystyle in inline math — consider display math environment";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-030"; run }

(* MATH-031: Operator spacing error — missing \; before \text in math *)
let l1_math_031_rule : rule =
  let re = Str.regexp {|[A-Za-z0-9}]\\text{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Count \text{ preceded by letter/digit/} without \; \, \quad etc. *)
        cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-031";
          severity = Info;
          message = "Missing spacing (\\; or \\,) before \\text in math mode";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-031"; run }

(* MATH-033: Use of \pm where +/- symbol required in text — \pm outside math *)
let l1_math_033_rule : rule =
  let run s =
    let text_parts = strip_math_segments s in
    let cnt = count_substring text_parts "\\pm" in
    if cnt > 0 then
      Some
        {
          id = "MATH-033";
          severity = Info;
          message =
            "\\pm used outside math mode — use ± symbol or wrap in $...$";
          count = cnt;
        }
    else None
  in
  { id = "MATH-033"; run }

(* MATH-034: Spacing before differential in integral missing \, — detects \int
   ... dx without \, before d *)
let l1_math_034_rule : rule =
  let diff_vars = "xytszrm" in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        if count_substring seg "\\int" > 0 then
          let n = String.length seg in
          let i = ref 0 in
          while !i < n - 1 do
            if seg.[!i] = 'd' && String.contains diff_vars seg.[!i + 1] then (
              (* Check the char after the differential var is not a letter *)
              let after_ok =
                !i + 2 >= n
                ||
                let c = seg.[!i + 2] in
                not ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'))
              in
              (if after_ok then
                 (* Check preceding context: should have \, before d *)
                 let has_thin_space =
                   !i >= 2 && seg.[!i - 2] = '\\' && seg.[!i - 1] = ','
                 in
                 let has_mathrm =
                   !i >= 8 && String.sub seg (!i - 8) 8 = "\\mathrm{"
                 in
                 if (not has_thin_space) && not has_mathrm then
                   (* Check there's a preceding letter/digit/paren before d *)
                   let prev_ok =
                     !i > 0
                     &&
                     let c = seg.[!i - 1] in
                     (c >= 'A' && c <= 'Z')
                     || (c >= 'a' && c <= 'z')
                     || (c >= '0' && c <= '9')
                     || c = ')'
                     || c = '}'
                     || c = ' '
                   in
                   if prev_ok then incr cnt);
              i := !i + 2)
            else incr i
          done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-034";
          severity = Info;
          message =
            "Missing \\, before differential in integral — use \\,dx not dx";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-034"; run }

(* MATH-035: Multiple subscripts stacked vertically without braces — a_{i}_{j}
   pattern instead of a_{i,j} *)
let l1_math_035_rule : rule =
  let re = Str.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)_|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-035";
          severity = Warning;
          message =
            "Multiple subscripts stacked without braces — use _{i,j} form";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-035"; run }

(* MATH-036: Superfluous \mathrm{} around single letter — \mathrm{x} is overkill
   for one letter *)
let l1_math_036_rule : rule =
  let re = Str.regexp {|\\mathrm{[A-Za-z]}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-036";
          severity = Info;
          message = "\\mathrm{} around single letter — may be superfluous";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-036"; run }

(* MATH-037: \sfrac (xfrac package) used outside text mode — \sfrac is for
   inline text fractions *)
let l1_math_037_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\sfrac{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-037";
          severity = Info;
          message =
            "\\sfrac used in math mode — intended for text mode fractions";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-037"; run }

(* MATH-038: Nested \frac three levels deep — readability issue *)
let l1_math_038_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Scan for \frac and track nesting depth via brace counting *)
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if
            !i + 5 < n
            && seg.[!i] = '\\'
            && seg.[!i + 1] = 'f'
            && seg.[!i + 2] = 'r'
            && seg.[!i + 3] = 'a'
            && seg.[!i + 4] = 'c'
            && seg.[!i + 5] = '{'
          then (
            (* Found \frac{, now count how many nested \frac{ appear in its
               arguments *)
            let depth = ref 1 in
            let brace_level = ref 1 in
            let j = ref (!i + 6) in
            let max_depth = ref 1 in
            (* scan through both arguments of \frac *)
            let args_seen = ref 0 in
            while !j < n && !args_seen < 2 do
              if seg.[!j] = '{' then (
                incr brace_level;
                (* Check if this is another \frac{ *)
                if
                  !j >= 5
                  && seg.[!j - 5] = '\\'
                  && seg.[!j - 4] = 'f'
                  && seg.[!j - 3] = 'r'
                  && seg.[!j - 2] = 'a'
                  && seg.[!j - 1] = 'c'
                then (
                  incr depth;
                  if !depth > !max_depth then max_depth := !depth);
                incr j)
              else if seg.[!j] = '}' then (
                decr brace_level;
                if !brace_level = 0 then (
                  incr args_seen;
                  if !args_seen < 2 && !j + 1 < n && seg.[!j + 1] = '{' then (
                    brace_level := 1;
                    j := !j + 2)
                  else incr j)
                else incr j)
              else incr j
            done;
            if !max_depth >= 3 then incr cnt;
            i := !i + 6)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-038";
          severity = Warning;
          message =
            "\\frac nested three or more levels deep — consider simplifying";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-038"; run }

(* MATH-039: Stacked relational operators without \substack — detects patterns
   like \underset{x}{\overset{y}{=}} which should use \substack *)
let l1_math_039_rule : rule =
  let re = Str.regexp {|\\underset{[^}]*}{\\overset{|} in
  let re2 = Str.regexp {|\\overset{[^}]*}{\\underset{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        cnt := !cnt + count_re_matches re seg + count_re_matches re2 seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-039";
          severity = Warning;
          message =
            "Stacked relational operators — consider \\substack or \\atop";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-039"; run }

(* MATH-040: Ellipsis \ldots used between operators on the center axis — should
   be \cdots for +, -, = etc. *)
let l1_math_040_rule : rule =
  let re = Str.regexp {|[+=<>-][ ]*\\ldots[ ]*[+=<>-]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-040";
          severity = Info;
          message =
            "\\ldots between center-axis operators — use \\cdots instead";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-040"; run }

(* MATH-041: Integral limits written inline in display — use \limits or
   \displaystyle \int for display integrals *)
let l1_math_041_rule : rule =
  let re = Str.regexp {|\\int_|} in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* \int_ in inline math — limits are typeset inline, suggest display *)
        cnt := !cnt + count_re_matches re seg)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-041";
          severity = Info;
          message =
            "Integral with limits in inline math — consider display math or \
             \\limits";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-041"; run }

(* MATH-042: Missing \, between number and unit in math — e.g. 5kg should be
   5\,\mathrm{kg} *)
let l1_math_042_rule : rule =
  let re = Str.regexp {|[0-9]\\mathrm{\|[0-9]\\text{\|[0-9]\\textrm{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-042";
          severity = Info;
          message = "Missing \\, between number and unit — use 5\\,\\mathrm{kg}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-042"; run }

(* MATH-043: Use of \text instead of \operatorname for function names in math —
   \text{Var} should be \operatorname{Var} *)
let l1_math_043_rule : rule =
  let re = Str.regexp {|\\text{[A-Z][a-z]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* \text{Xxx} in math is likely a function name that should use
           \operatorname *)
        cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-043";
          severity = Warning;
          message =
            "\\text{...} in math for function name — use \\operatorname{...}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-043"; run }

(* MATH-044: Binary relation typed as text char — e.g. < for \le, = for \equiv,
   etc., when text < > appear in math outside of delimiters *)
let l1_math_044_rule : rule =
  let re = Str.regexp {|[^\\]<=\|[^\\]>=|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-044";
          severity = Warning;
          message =
            "Compound relation <=/>= in math — use \\le, \\ge, \\leq, \\geq";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-044"; run }

(* MATH-045: Math italic capital Greek without \mathrm — e.g. bare \Gamma when
   the document uses upright Greek capitals *)
let l1_math_045_rule : rule =
  let greek_capitals =
    [
      "\\Gamma";
      "\\Delta";
      "\\Theta";
      "\\Lambda";
      "\\Xi";
      "\\Pi";
      "\\Sigma";
      "\\Upsilon";
      "\\Phi";
      "\\Psi";
      "\\Omega";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let has_upright = ref false in
    let bare_cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun gc ->
            let upright_form = "\\mathrm{" ^ gc ^ "}" in
            if count_substring seg upright_form > 0 then has_upright := true;
            let total = count_substring seg gc in
            let wrapped = count_substring seg upright_form in
            let bare = total - wrapped in
            if bare > 0 then bare_cnt := !bare_cnt + bare)
          greek_capitals)
      math_segs;
    (* Only flag if document mixes upright and italic for the same class *)
    if !has_upright && !bare_cnt > 0 then
      Some
        {
          id = "MATH-045";
          severity = Info;
          message =
            "Mixed italic/upright capital Greek — consider consistent \
             \\mathrm{} wrapping";
          count = !bare_cnt;
        }
    else None
  in
  { id = "MATH-045"; run }

(* MATH-046: Ellipsis \ldots on relation axis — prefer \cdots between commas, +
   etc. *)
let l1_math_046_rule : rule =
  let re = Str.regexp {|,[ ]*\\ldots[ ]*,|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-046";
          severity = Info;
          message =
            "\\ldots between commas — use \\cdots for center-axis ellipsis";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-046"; run }

(* MATH-047: Double superscript without braces — a^b^c is a TeX error *)
let l1_math_047_rule : rule =
  let re = Str.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)\^|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-047";
          severity = Error;
          message = "Double superscript a^b^c — braces required: a^{b^c}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-047"; run }

(* MATH-048: Boldface digits via \mathbf in math — \mathbf{1} etc. is typically
   unnecessary *)
let l1_math_048_rule : rule =
  let re = Str.regexp {|\\mathbf{[0-9]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-048";
          severity = Info;
          message = "\\mathbf applied to digits — digits are already upright";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-048"; run }

(* MATH-049: Missing spacing around \times — detects a\times b without
   surrounding spaces *)
let l1_math_049_rule : rule =
  let re_no_space_before = Str.regexp {|[A-Za-z0-9}]\\times|} in
  let re_no_space_after = Str.regexp {|\\times[A-Za-z0-9{]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let total_times = count_substring seg "\\times" in
        if total_times > 0 then
          let before = count_re_matches re_no_space_before seg in
          let after = count_re_matches re_no_space_after seg in
          let bad = min total_times (max before after) in
          if bad > 0 then cnt := !cnt + bad)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-049";
          severity = Info;
          message = "Missing spacing around \\times — add space for readability";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-049"; run }

(* MATH-050: Circumflex accent \hat on multi-letter argument — \hat{abc} should
   typically be \widehat{abc} *)
let l1_math_050_rule : rule =
  let re = Str.regexp {|\\hat{[A-Za-z][A-Za-z]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-050";
          severity = Warning;
          message =
            "\\hat on multi-letter argument — use \\widehat for wide accents";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-050"; run }

(* MATH-051: Radical \sqrt nested two levels — \sqrt{\sqrt{}} is hard to read *)
let l1_math_051_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Find \sqrt{ and look for nested \sqrt{ inside its argument *)
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if
            !i + 5 < n
            && seg.[!i] = '\\'
            && seg.[!i + 1] = 's'
            && seg.[!i + 2] = 'q'
            && seg.[!i + 3] = 'r'
            && seg.[!i + 4] = 't'
            && (seg.[!i + 5] = '{' || seg.[!i + 5] = '[')
          then (
            (* Found \sqrt{ or \sqrt[, scan the argument for nested \sqrt *)
            let start =
              if seg.[!i + 5] = '[' then (
                (* Skip optional argument \sqrt[n]{...} *)
                let j = ref (!i + 6) in
                while !j < n && seg.[!j] <> ']' do
                  incr j
                done;
                if !j < n && !j + 1 < n && seg.[!j + 1] = '{' then !j + 2
                else !i + 6)
              else !i + 6
            in
            let brace_level = ref 1 in
            let j = ref start in
            let found_nested = ref false in
            while !j < n && !brace_level > 0 do
              if seg.[!j] = '{' then (
                (* Check if this is \sqrt{ *)
                if
                  !j >= 5
                  && seg.[!j - 5] = '\\'
                  && seg.[!j - 4] = 's'
                  && seg.[!j - 3] = 'q'
                  && seg.[!j - 2] = 'r'
                  && seg.[!j - 1] = 't'
                then found_nested := true;
                incr brace_level;
                incr j)
              else if seg.[!j] = '}' then (
                decr brace_level;
                incr j)
              else incr j
            done;
            if !found_nested then incr cnt;
            i := !i + 6)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-051";
          severity = Warning;
          message =
            "Nested \\sqrt — consider rewriting with fractional exponents";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-051"; run }

(* MATH-052: \over primitive used — prefer \frac{a}{b} over {a \over b} *)
let l1_math_052_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Count \over that is NOT \overbrace, \overline, \overset,
           \overrightarrow, \overleftarrow, \overleftrightarrow *)
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if
            !i + 5 <= n
            && seg.[!i] = '\\'
            && seg.[!i + 1] = 'o'
            && seg.[!i + 2] = 'v'
            && seg.[!i + 3] = 'e'
            && seg.[!i + 4] = 'r'
          then (
            (* Check it's bare \over (followed by space, brace, or end) and not
               \overbrace etc *)
            let after = if !i + 5 < n then seg.[!i + 5] else ' ' in
            if
              after = ' '
              || after = '{'
              || after = '\\'
              || after = '\n'
              || after = '\t'
              || !i + 5 = n
            then incr cnt;
            i := !i + 5)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-052";
          severity = Warning;
          message = "\\over primitive used — prefer \\frac{a}{b}";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-052"; run }

(* MATH-053: Space after \left( — spurious space *)
let l1_math_053_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          let prefix = "\\left(" in
          let plen = String.length prefix in
          if
            !i + plen < n
            && String.sub seg !i plen = prefix
            && seg.[!i + plen] = ' '
          then (
            incr cnt;
            i := !i + plen)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-053";
          severity = Info;
          message = "Space after \\left( — remove spurious whitespace";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-053"; run }

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
    l1_delim_001_rule;
    l1_delim_002_rule;
    l1_delim_003_rule;
    l1_delim_004_rule;
    l1_delim_005_rule;
    l1_delim_006_rule;
    l1_delim_007_rule;
    l1_delim_008_rule;
    l1_delim_009_rule;
    l1_delim_010_rule;
    l1_delim_011_rule;
    l1_script_001_rule;
    l1_script_002_rule;
    l1_script_003_rule;
    l1_script_004_rule;
    l1_script_005_rule;
    l1_script_006_rule;
    l1_script_007_rule;
    l1_script_008_rule;
    l1_script_009_rule;
    l1_script_010_rule;
    l1_script_011_rule;
    l1_script_012_rule;
    l1_script_013_rule;
    l1_script_014_rule;
    l1_script_015_rule;
    l1_script_016_rule;
    l1_script_017_rule;
    l1_script_018_rule;
    l1_script_019_rule;
    l1_script_020_rule;
    l1_script_021_rule;
    l1_script_022_rule;
    l1_math_009_rule;
    l1_math_010_rule;
    l1_math_011_rule;
    l1_math_012_rule;
    l1_math_013_rule;
    l1_math_014_rule;
    l1_math_015_rule;
    l1_math_016_rule;
    l1_math_017_rule;
    l1_math_018_rule;
    l1_math_019_rule;
    l1_math_020_rule;
    l1_math_021_rule;
    l1_math_022_rule;
    l1_math_030_rule;
    l1_math_031_rule;
    l1_math_033_rule;
    l1_math_034_rule;
    l1_math_035_rule;
    l1_math_036_rule;
    l1_math_037_rule;
    l1_math_038_rule;
    l1_math_039_rule;
    l1_math_040_rule;
    l1_math_041_rule;
    l1_math_042_rule;
    l1_math_043_rule;
    l1_math_044_rule;
    l1_math_045_rule;
    l1_math_046_rule;
    l1_math_047_rule;
    l1_math_048_rule;
    l1_math_049_rule;
    l1_math_050_rule;
    l1_math_051_rule;
    l1_math_052_rule;
    l1_math_053_rule;
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
  | _ when String.length id >= 6 && String.sub id 0 6 = "DELIM-" -> L1
  | _ when String.length id >= 7 && String.sub id 0 7 = "SCRIPT-" -> L1
  | "MATH-083" -> L0
  | _ when String.length id >= 5 && String.sub id 0 5 = "MATH-" -> L1
  | _ when String.length id >= 5 && String.sub id 0 5 = "VERB-" -> L0
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
