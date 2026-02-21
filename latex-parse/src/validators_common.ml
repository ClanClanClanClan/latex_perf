(* ══════════════════════════════════════════════════════════════════════
   Validators_common — shared types and helpers for the validator engine
   ══════════════════════════════════════════════════════════════════════ *)

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

let contains_substring (s : string) (needle : string) : bool =
  try
    ignore (Str.search_forward (Str.regexp_string needle) s 0);
    true
  with Not_found -> false

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
  let math_env_tbl = Hashtbl.create 32 in
  List.iter (fun e -> Hashtbl.replace math_env_tbl e ()) math_envs;
  let is_math_env name = Hashtbl.mem math_env_tbl name in
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

(* ── Helper: extract env blocks with optional args ───────────────────── *)
(* Returns list of (optional_args_string, body_string) for each
   \begin{env}[opts]...\end{env} *)
let extract_env_blocks_with_opts (env : string) (s : string) :
    (string * string) list =
  let open_tag = "\\begin{" ^ env ^ "}" in
  let close_tag = "\\end{" ^ env ^ "}" in
  let open_len = String.length open_tag in
  let close_len = String.length close_tag in
  let n = String.length s in
  let blocks = ref [] in
  let i = ref 0 in
  while !i <= n - open_len do
    if String.sub s !i open_len = open_tag then (
      let after_open = !i + open_len in
      (* extract optional [...] if present *)
      let opts = ref "" in
      let content_start = ref after_open in
      if !content_start < n && s.[!content_start] = '[' then (
        let bracket_start = !content_start + 1 in
        let j = ref bracket_start in
        while !j < n && s.[!j] <> ']' do
          incr j
        done;
        if !j < n then (
          opts := String.sub s bracket_start (!j - bracket_start);
          content_start := !j + 1));
      (* find matching \end{env} *)
      let found = ref false in
      let j = ref !content_start in
      while !j <= n - close_len && not !found do
        if String.sub s !j close_len = close_tag then (
          blocks :=
            (!opts, String.sub s !content_start (!j - !content_start))
            :: !blocks;
          i := !j + close_len;
          found := true)
        else incr j
      done;
      if not !found then i := n)
    else incr i
  done;
  List.rev !blocks

(* ── Helper: extract preamble (everything before \begin{document}) ──── *)
let extract_preamble (s : string) : string =
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

(* ── Helper: extract all \usepackage occurrences with positions ─────── *)
(* Returns list of (position, package_name) *)
let extract_usepackages (s : string) : (int * string) list =
  let re = Str.regexp {|\\usepackage\(\[[^]]*\]\)?{|} in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let pos = Str.search_forward re s !i in
       let after_brace = Str.match_end () in
       (* find closing brace *)
       let j = ref after_brace in
       while !j < String.length s && s.[!j] <> '}' do
         incr j
       done;
       (if !j < String.length s then
          let pkg_str = String.sub s after_brace (!j - after_brace) in
          (* handle comma-separated packages *)
          let pkgs = String.split_on_char ',' pkg_str in
          List.iter
            (fun p ->
              let p = String.trim p in
              if p <> "" then results := (pos, p) :: !results)
            pkgs);
       i := !j + 1
     done
   with Not_found -> ());
  List.rev !results

(* ── Helper: check if a LaTeX package is loaded (handles options) ────── *)
(* Uses extract_usepackages which handles both \usepackage{pkg} and
   \usepackage[opts]{pkg} and comma-separated packages *)
let has_package (s : string) (pkg : string) : bool =
  let pkgs = extract_usepackages s in
  List.exists (fun (_pos, p) -> p = pkg) pkgs

(* ── Helper: extract env blocks for both env and env* ────────────────── *)
let extract_env_blocks_starred (env : string) (s : string) : string list =
  let plain = extract_env_blocks env s in
  let starred = extract_env_blocks (env ^ "*") s in
  plain @ starred

(* ── Helper: check for \caption{ or \caption[ (not \captionsetup etc.) *)
let has_caption (body : string) : bool =
  let re = Str.regexp {|\\caption\(\[\|{\)|} in
  try
    ignore (Str.search_forward re body 0);
    true
  with Not_found -> false

(* ── Helper: extract all \label{prefix:...} keys ──────────────────────── *)
let extract_labels_with_prefix (prefix : string) (s : string) :
    (int * string) list =
  let re = Str.regexp ("\\\\label{" ^ Str.quote prefix ^ "\\([^}]*\\)}") in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let pos = Str.search_forward re s !i in
       let key = Str.matched_group 1 s in
       results := (pos, prefix ^ key) :: !results;
       i := Str.match_end ()
     done
   with Not_found -> ());
  List.rev !results

(* ── Helper: extract all \ref{prefix:...}, \eqref{prefix:...},
   \autoref{prefix:...}, \cref{prefix:...} keys ──────────── *)
let extract_refs_with_prefix (prefix : string) (s : string) :
    (int * string) list =
  let re =
    Str.regexp
      ("\\\\\\(eq\\)?ref{"
      ^ Str.quote prefix
      ^ "\\([^}]*\\)}"
      ^ "\\|\\\\autoref{"
      ^ Str.quote prefix
      ^ "\\([^}]*\\)}"
      ^ "\\|\\\\cref{"
      ^ Str.quote prefix
      ^ "\\([^}]*\\)}"
      ^ "\\|\\\\Cref{"
      ^ Str.quote prefix
      ^ "\\([^}]*\\)}")
  in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let pos = Str.search_forward re s !i in
       (* Try each group to find the match *)
       let key =
         try Str.matched_group 2 s
         with Not_found -> (
           try Str.matched_group 3 s
           with Not_found -> (
             try Str.matched_group 4 s with Not_found -> Str.matched_group 5 s))
       in
       results := (pos, prefix ^ key) :: !results;
       i := Str.match_end ()
     done
   with Not_found -> ());
  List.rev !results

(* ── Helper: extract document class name ─────────────────────────────── *)
(* Matches \documentclass[opts]{classname} or \documentclass{classname}. *)
let extract_docclass (s : string) : string option =
  let re = Str.regexp "\\\\documentclass\\(\\[[^]]*\\]\\)?{\\([^}]+\\)}" in
  try
    ignore (Str.search_forward re s 0);
    Some (Str.matched_group 2 s)
  with Not_found -> None

(* Document classes that conventionally require \maketitle and abstract. *)
let article_like_classes =
  [
    "article";
    "report";
    "scrartcl";
    "scrreprt";
    "scrbook";
    "amsart";
    "IEEEtran";
    "llncs";
    "acmart";
    "revtex4-2";
    "elsarticle";
    "svjour3";
    "memoir";
    "book";
  ]

let is_article_like (s : string) : bool =
  match extract_docclass s with
  | None -> false
  | Some cls -> List.mem cls article_like_classes

(* ── Helper: extract usepackage with options ────────────────────────── *)
(* Returns list of (position, options_string, package_name). Options may be ""
   if no options bracket present. *)
let extract_usepackages_with_opts (s : string) : (int * string * string) list =
  let re = Str.regexp {|\\usepackage\(\[[^]]*\]\)?{|} in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let pos = Str.search_forward re s !i in
       let full = Str.matched_string s in
       let after_brace = Str.match_end () in
       let opts =
         try
           let _ = Str.search_forward (Str.regexp {|\[\([^]]*\)\]|}) full 0 in
           Str.matched_group 1 full
         with Not_found -> ""
       in
       let j = ref after_brace in
       while !j < String.length s && s.[!j] <> '}' do
         incr j
       done;
       (if !j < String.length s then
          let pkg_str = String.sub s after_brace (!j - after_brace) in
          let pkgs = String.split_on_char ',' pkg_str in
          List.iter
            (fun p ->
              let p = String.trim p in
              if p <> "" then results := (pos, opts, p) :: !results)
            pkgs);
       i := !j + 1
     done
   with Not_found -> ());
  List.rev !results

(* ── Helper: extract caption content from env body ──────────────────── *)
let extract_caption_content (body : string) : string option =
  let re = Str.regexp {|\\caption{|} in
  try
    let _ = Str.search_forward re body 0 in
    let start = Str.match_end () in
    let depth = ref 1 in
    let j = ref start in
    while !j < String.length body && !depth > 0 do
      (match body.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
      if !depth > 0 then incr j
    done;
    if !depth = 0 then Some (String.sub body start (!j - start)) else None
  with Not_found -> None

(* Helper: split bib content into individual entries. Each entry starts with
   @type{key, and ends at the next @ or EOF. *)
let split_bib_entries (s : string) : string list =
  let re = Str.regexp "@[a-zA-Z]+{" in
  let entries = ref [] in
  let starts = ref [] in
  let i = ref 0 in
  (try
     while true do
       let pos = Str.search_forward re s !i in
       starts := pos :: !starts;
       i := pos + 1
     done
   with Not_found -> ());
  let starts_list = List.rev !starts in
  let n = String.length s in
  let rec build = function
    | [] -> ()
    | [ p ] -> entries := String.sub s p (n - p) :: !entries
    | p :: (q :: _ as rest) ->
        entries := String.sub s p (q - p) :: !entries;
        build rest
  in
  build starts_list;
  List.rev !entries

(* Helper: count regex matches *)
let count_matches (re : Str.regexp) (s : string) : int =
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

(* Global modernization suggestions (document-wide mixing across paragraphs) *)
let has_global_mixing names legacy modern : bool =
  let has_any xs = List.exists (fun n -> List.exists (( = ) n) names) xs in
  has_any legacy && has_any modern

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
  let math_env_tbl = Hashtbl.create 32 in
  List.iter (fun e -> Hashtbl.replace math_env_tbl e ()) math_envs;
  let is_math_env name = Hashtbl.mem math_env_tbl name in
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

(* Helper: extract all \label{...} values from source *)
let extract_labels (s : string) : string list =
  let re = Str.regexp {|\\label{[^}]*}|} in
  let labels = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _ = Str.search_forward re s !i in
       let m = Str.matched_string s in
       let next = Str.match_end () in
       (* extract content between { and } *)
       let inner = String.sub m 7 (String.length m - 8) in
       labels := inner :: !labels;
       i := next
     done
   with Not_found -> ());
  List.rev !labels

(* Helper: extract all \ref{...} and \eqref{...} label references *)
let extract_refs (s : string) : string list =
  let re = Str.regexp {|\\eqref{[^}]*}\|\\ref{[^}]*}|} in
  let refs = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _ = Str.search_forward re s !i in
       let m = Str.matched_string s in
       let next = Str.match_end () in
       (* Find the { and extract content *)
       let brace_pos = String.index m '{' in
       let inner =
         String.sub m (brace_pos + 1) (String.length m - brace_pos - 2)
       in
       refs := inner :: !refs;
       i := next
     done
   with Not_found -> ());
  List.rev !refs

let severity_to_string = function
  | Error -> "error"
  | Warning -> "warning"
  | Info -> "info"

(* Precondition wiring (stubs) *)
type layer = L0 | L1 | L2 | L3 | L4
