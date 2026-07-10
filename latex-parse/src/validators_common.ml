(* ══════════════════════════════════════════════════════════════════════
   Validators_common — shared types and helpers for the validator engine
   ══════════════════════════════════════════════════════════════════════ *)

type severity = Error | Warning | Info

type candidate_fix = { c_edits : Cst_edit.t list; c_label : string }
(** A CANDIDATE fix (Bucket C): a suggested edit set that depends on author
    INTENT and therefore must NOT auto-apply. [c_edits] is a non-overlapping
    edit set; [c_label] is a human-readable description shown to the author for
    review. Candidates are surfaced by [--list-candidate-fixes] for an editor
    frontend to offer, but are deliberately ignored by [--apply-fixes] /
    [--apply-fixes-for], which only apply the [fix] field. *)

type result = {
  id : string;
  severity : severity;
  message : string;
  count : int;
  fix : Cst_edit.t list option;
      (** Optional fix suggestions. [None] = no fix available for this firing;
          [Some []] is ill-formed (use [None]); [Some edits] is a
          non-overlapping edit set that, when applied via
          [Rewrite_engine.apply], makes the rule stop firing on the output.
          Introduced in v26.2.1 to back the [--apply-fixes] CLI flag. See
          [docs/v26_2/FIX_STYLE_GUIDE.md] for producer conventions. *)
  candidate_fixes : candidate_fix list;
      (** Bucket-C CANDIDATE fixes: intent-dependent suggestions surfaced for
          author review via [--list-candidate-fixes]. Defaults to [[]] for every
          rule (set via the [mk_result] / [mk_result_with_fix] constructors); a
          rule opts in with [mk_result_with_candidates]. These are NEVER applied
          by [--apply-fixes]; only [fix] is. *)
}

(** Construct a [result] with no fix suggestion ([fix = None]). Every rule
    introduced before v26.2.1 should use this helper; rules that emit fix
    suggestions use [mk_result_with_fix] below. *)
let mk_result ~id ~severity ~message ~count =
  { id; severity; message; count; fix = None; candidate_fixes = [] }

(** Construct a [result] that carries a non-empty edit list. Fails if [fix] is
    the empty list — an empty [Some] is indistinguishable from [None]
    semantically but harder to audit, so the caller must pass [mk_result ...]
    when no fix is available. *)
let mk_result_with_fix ~id ~severity ~message ~count ~fix =
  if fix = [] then
    invalid_arg "Validators_common.mk_result_with_fix: empty fix list"
  else { id; severity; message; count; fix = Some fix; candidate_fixes = [] }

(** Construct a [result] carrying one or more Bucket-C CANDIDATE fixes (see
    {!type:candidate_fix}). Sets [fix = None] (candidates are never
    auto-applied) and [candidate_fixes = candidates]. Fails if [candidates = []]
    — a rule with no candidate to offer should use [mk_result] instead. The
    diagnostic [count] is supplied by the caller and is untouched, so attaching
    candidates never changes a rule's firing behaviour. *)
let mk_result_with_candidates ~id ~severity ~message ~count ~candidates =
  if candidates = [] then
    invalid_arg
      "Validators_common.mk_result_with_candidates: empty candidate list"
  else
    { id; severity; message; count; fix = None; candidate_fixes = candidates }

type rule = {
  id : string;
  run : string -> result option;
  languages : string list;
      (** Language codes this rule applies to (ISO 639-1). Empty list =
          universal (fires on all documents). Non-empty = only fires when
          document language matches. *)
}

(** Construct a universal rule (fires on all documents). *)
let mk_rule id run = { id; run; languages = [] }

(** Construct a language-specific rule. *)
let mk_lang_rule id run langs = { id; run; languages = langs }

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
  let slen = String.length s and nlen = String.length needle in
  if nlen = 0 then true
  else if nlen > slen then false
  else
    let rec loop i =
      if i > slen - nlen then false
      else if String.sub s i nlen = needle then true
      else loop (i + 1)
    in
    loop 0

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
      "alignat";
      "alignat*";
      "flalign";
      "flalign*";
      "eqnarray";
      "IEEEeqnarray";
      "IEEEeqnarray*";
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

(* find_math_ranges: half-open byte ranges of every math segment in the source.
   Mirrors strip_math_segments' detection logic but records ranges instead of
   producing a stripped buffer. Math segments include inline dollar pairs, paren
   math, bracket math, and 11 named math environments.

   Returned ranges are non-overlapping and sorted by start offset. At EOF with
   an unclosed segment, the range extends to length(s). Used by fix producers
   (TYPO-004 v27.0.6+) to filter match offsets that fall inside math, where a
   textual auto-replacement would corrupt the semantic meaning (e.g.,
   apostrophe-pair as double-prime). *)
let find_math_ranges (s : string) : (int * int) list =
  let len = String.length s in
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
      "alignat";
      "alignat*";
      "flalign";
      "flalign*";
      "eqnarray";
      "IEEEeqnarray";
      "IEEEeqnarray*";
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
  let ranges = ref [] in
  let in_dollar_start = ref None in
  let in_paren_start = ref None in
  let in_brack_start = ref None in
  let i = ref 0 in
  while !i < len do
    let pos = !i in
    if !in_dollar_start <> None then
      if (not (is_escaped pos)) && s.[pos] = '$' then (
        let start_i = match !in_dollar_start with Some s -> s | None -> pos in
        ranges := (start_i, pos + 1) :: !ranges;
        in_dollar_start := None;
        i := pos + 1)
      else i := pos + 1
    else if !in_paren_start <> None then
      if (not (is_escaped pos)) && starts_with "\\)" pos then (
        let start_i = match !in_paren_start with Some s -> s | None -> pos in
        ranges := (start_i, pos + 2) :: !ranges;
        in_paren_start := None;
        i := pos + 2)
      else i := pos + 1
    else if !in_brack_start <> None then
      if (not (is_escaped pos)) && starts_with "\\]" pos then (
        let start_i = match !in_brack_start with Some s -> s | None -> pos in
        ranges := (start_i, pos + 2) :: !ranges;
        in_brack_start := None;
        i := pos + 2)
      else i := pos + 1
    else if (not (is_escaped pos)) && starts_with "$$" pos then (
      (* Display math `$$..$$` matched-pair. Distinct from strip_math_segments'
         single-toggle behaviour: that function treats `$$x$$` as two empty math
         segments around literal `x`, which would let TYPO-004's fix corrupt
         `$$f''(x)=0$$` (the very bug v27.0.5 deferred against). Match `$$`
         first, then scan to the next un-escaped `$$`. *)
      let start_i = pos in
      let j = ref (pos + 2) in
      while !j < len && not ((not (is_escaped !j)) && starts_with "$$" !j) do
        incr j
      done;
      let end_i = if !j + 2 <= len then !j + 2 else len in
      ranges := (start_i, end_i) :: !ranges;
      i := end_i)
    else if (not (is_escaped pos)) && s.[pos] = '$' then (
      in_dollar_start := Some pos;
      i := pos + 1)
    else if (not (is_escaped pos)) && starts_with "\\(" pos then (
      in_paren_start := Some pos;
      i := pos + 2)
    else if (not (is_escaped pos)) && starts_with "\\[" pos then (
      in_brack_start := Some pos;
      i := pos + 2)
    else if (not (is_escaped pos)) && starts_with "\\begin{" pos then
      match parse_begin pos with
      | Some (name, after_begin) when is_math_env name ->
          let next_i = skip_env name after_begin 0 in
          ranges := (pos, next_i) :: !ranges;
          i := next_i
      | _ -> i := pos + 1
    else i := pos + 1
  done;
  (* Close any unmatched segment at EOF *)
  (match !in_dollar_start with
  | Some s -> ranges := (s, len) :: !ranges
  | None -> ());
  (match !in_paren_start with
  | Some s -> ranges := (s, len) :: !ranges
  | None -> ());
  (match !in_brack_start with
  | Some s -> ranges := (s, len) :: !ranges
  | None -> ());
  List.rev !ranges

(** [is_in_math_range ranges off] — true iff [off] falls inside any range in
    [ranges]. Linear in the number of ranges (typically small). Use with
    [find_math_ranges] to filter fix-edit offsets before emitting replaces. *)
let is_in_math_range (ranges : (int * int) list) (off : int) : bool =
  List.exists (fun (a, b) -> a <= off && off < b) ranges

(** [range_is_inline_math s (a, _b)] — true iff the math range starting at byte
    [a] in [s] is an inline math segment (`$..$` with single dollars, or
    `\(..\)`).  Returns [false] for display-math ranges (`$$..$$`, `\[..\]`,
    `\begin{equation}..\end{equation}`, etc.).

    Detection: inline ranges start either with a single `$` (next byte not `$`)
    or with `\(`.  Display ranges start with `$$`, `\[`, or `\begin{...}`.

    Used by MATH-014 (v27.0.67) to gate `\frac` → `\tfrac` replacement to
    inline math contexts only (where `\frac`'s full-size fraction is hard to
    read).  Composes with [find_math_ranges] / [is_in_math_range] for fix
    producers that need an inline-only filter. *)
let range_is_inline_math (s : string) ((a, _b) : int * int) : bool =
  let n = String.length s in
  if a >= n then false
  else if a + 1 < n then
    (s.[a] = '$' && s.[a + 1] <> '$') || (s.[a] = '\\' && s.[a + 1] = '(')
  else s.[a] = '$'

(* ── Context-exemption ranges (P3 token-aware variants) ───────────────────
   Byte ranges where typographic / lexical lint rules must NOT fire because the
   bytes are not ordinary prose: verbatim spans, line comments, and url/href
   targets — composed with [find_math_ranges] for math. The pilot L0 rules were
   string-level and context-blind (docs/archive/RULES_PILOT_TODO.md: "Runtime
   implementation is string-level; token-aware variants will follow post L0
   tokenizer rewire"), so they fired on `--`, `...`, ``..'' etc. inside code
   listings, comments and math. Composing a rule's candidate offsets with
   [is_in_exempt_range (find_exempt_ranges s)] makes it skip those regions — the
   post-pilot-gate prerequisite for graduating a Draft rule to the default
   set. *)

(* Environments whose body is verbatim (literal bytes, no typography
   applies). *)
let verbatim_envs =
  [
    "verbatim";
    "verbatim*";
    "Verbatim";
    "Verbatim*";
    "BVerbatim";
    "LVerbatim";
    "lstlisting";
    "minted";
    "alltt";
    "comment";
    "listing";
  ]

(** [find_verbatim_comment_url_ranges s] — single left-to-right pass returning
    the byte ranges covered by line comments (`%`..EOL, respecting `\%`),
    inline verbatim (`\verb<d>..<d>`, `\verb*`, `\lstinline<d>..<d>`), verbatim
    environments ([verbatim_envs]), and url targets (`\url{..}`, `\nolinkurl`,
    `\path`, and the FIRST argument of `\href{..}{..}`). Precedence is positional
    — whichever region opens first wins, and the scanner jumps past a region's
    end before looking for the next, so a `%`/`$`/`\verb` inside a verbatim span
    (or a `$` inside a comment) is correctly treated as literal.

    NB: callers use the memoised [find_verbatim_comment_url_ranges] wrapper
    below; this is the underlying computation. *)
let compute_verbatim_comment_url_ranges (s : string) : (int * int) list =
  let n = String.length s in
  let tbl = Hashtbl.create 32 in
  List.iter (fun e -> Hashtbl.replace tbl e ()) verbatim_envs;
  let is_verb_env name = Hashtbl.mem tbl name in
  let is_escaped idx =
    let rec count back acc =
      if back < 0 then acc
      else if String.unsafe_get s back = '\\' then count (back - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let starts_with p idx =
    let pl = String.length p in
    idx + pl <= n && String.sub s idx pl = p
  in
  let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  (* End (exclusive) of the brace group whose opening `{` is at [open_pos]. *)
  let brace_group_end open_pos =
    let depth = ref 0 in
    let k = ref open_pos in
    let stop = ref None in
    while !stop = None && !k < n do
      (if not (is_escaped !k) then
         match String.unsafe_get s !k with
         | '{' -> incr depth
         | '}' ->
             decr depth;
             if !depth = 0 then stop := Some (!k + 1)
         | _ -> ());
      incr k
    done;
    match !stop with Some e -> e | None -> n
  in
  let ranges = ref [] in
  let i = ref 0 in
  while !i < n do
    let pos = !i in
    let c = String.unsafe_get s pos in
    if c = '%' && not (is_escaped pos) then (
      let j = ref pos in
      while !j < n && String.unsafe_get s !j <> '\n' do
        incr j
      done;
      ranges := (pos, !j) :: !ranges;
      i := !j)
    else if c = '\\' && not (is_escaped pos) then
      if starts_with "\\begin{" pos then (
        let ns = pos + 7 in
        let j = ref ns in
        while !j < n && String.unsafe_get s !j <> '}' do
          incr j
        done;
        if !j < n && is_verb_env (String.sub s ns (!j - ns)) then (
          let name = String.sub s ns (!j - ns) in
          let endp = "\\end{" ^ name ^ "}" in
          let el = String.length endp in
          let k = ref (!j + 1) in
          while !k < n && not (starts_with endp !k) do
            incr k
          done;
          let stop = if !k < n then !k + el else n in
          ranges := (pos, stop) :: !ranges;
          i := stop)
        else i := pos + 1)
      else if starts_with "\\verb" pos || starts_with "\\lstinline" pos then (
        let cmdlen = if starts_with "\\lstinline" pos then 10 else 5 in
        let after = ref (pos + cmdlen) in
        if !after < n && String.unsafe_get s !after = '*' then incr after;
        if !after < n && not (is_letter (String.unsafe_get s !after)) then (
          (* The next char is the delimiter; non-letter guard avoids swallowing
             longer command names (e.g. \verbatim, \verbatiminput). *)
          let delim = String.unsafe_get s !after in
          let k = ref (!after + 1) in
          while !k < n && String.unsafe_get s !k <> delim do
            incr k
          done;
          let stop = if !k < n then !k + 1 else n in
          ranges := (pos, stop) :: !ranges;
          i := stop)
        else i := pos + 1)
      else if
        starts_with "\\url{" pos
        || starts_with "\\nolinkurl{" pos
        || starts_with "\\path{" pos
      then (
        let bpos = String.index_from s pos '{' in
        let stop = brace_group_end bpos in
        ranges := (pos, stop) :: !ranges;
        i := stop)
      else if starts_with "\\href{" pos then (
        (* Only the first argument (the URL) is verbatim-ish; the link text is
           ordinary prose, so exempt just `\href{..}`. *)
        let bpos = pos + 5 in
        let stop = brace_group_end bpos in
        ranges := (pos, stop) :: !ranges;
        i := stop)
      else i := pos + 1
    else i := pos + 1
  done;
  List.rev !ranges

(* Per-document memoisation of the range scanners. In one [Validators.run_all]
   pass every rule is handed the SAME source-string object, so the ~30
   context-aware TYPO rules now in the DEFAULT set would otherwise each
   recompute these O(n) scans (and [find_exempt_ranges] also calls the vcu
   scanner). A 1-entry cache keyed by PHYSICAL equality ([==]) collapses that to
   a single computation per document. Correctness is unconditional: a different
   string simply misses and recomputes, and these are pure functions of [s]
   (strings are immutable; [compute_exempt_ranges] blanks a private [Bytes]
   copy, never [s]). Single-threaded validator pass ⇒ no races on the refs. *)
let _vcu_cache : (string * (int * int) list) option ref = ref None

(** Memoised [compute_verbatim_comment_url_ranges] — see the cache note above. *)
let find_verbatim_comment_url_ranges (s : string) : (int * int) list =
  match !_vcu_cache with
  | Some (s', r) when s' == s -> r
  | _ ->
      let r = compute_verbatim_comment_url_ranges s in
      _vcu_cache := Some (s, r);
      r

(** [find_exempt_ranges s] — all byte ranges where typography/lexical rules must
    not fire: verbatim + comments + url targets
    ([find_verbatim_comment_url_ranges]) plus math ([find_math_ranges]).

    To detect math correctly, the verbatim/comment/url spans are first BLANKED
    to spaces (offsets preserved) and [find_math_ranges] is run on the blanked
    copy. [find_math_ranges] is itself context-blind about comments/verbatim, so
    a stray `$` in a comment would otherwise desync all downstream math pairing;
    blanking neutralises those bytes (a space is never a math toggle) without
    shifting any offset, so the math ranges are accurate outside protected
    regions. The result is sorted by start; overlaps are harmless for the
    existential [is_in_exempt_range] check.

    NB: callers use the memoised [find_exempt_ranges] wrapper below; this is the
    underlying computation. Its internal vcu call goes through the memoised
    [find_verbatim_comment_url_ranges], so that scan is shared too. *)
let compute_exempt_ranges (s : string) : (int * int) list =
  let vcu = find_verbatim_comment_url_ranges s in
  let blanked = Bytes.of_string s in
  List.iter
    (fun (a, b) ->
      for k = a to b - 1 do
        Bytes.set blanked k ' '
      done)
    vcu;
  let math = find_math_ranges (Bytes.unsafe_to_string blanked) in
  List.sort (fun (a, _) (c, _) -> compare a c) (List.rev_append vcu math)

let _exempt_cache : (string * (int * int) list) option ref = ref None

(** Memoised [compute_exempt_ranges] — see the cache note above
    [find_verbatim_comment_url_ranges]. *)
let find_exempt_ranges (s : string) : (int * int) list =
  match !_exempt_cache with
  | Some (s', r) when s' == s -> r
  | _ ->
      let r = compute_exempt_ranges s in
      _exempt_cache := Some (s, r);
      r

(** [is_in_exempt_range ranges off] — true iff [off] is inside any exempt range.
    (Alias of the generic point-in-ranges test [is_in_math_range].) *)
let is_in_exempt_range = is_in_math_range

(** [mk_result_with_fix_exempt ~id ~severity ~message ~count ~src ~fix] —
    exempt-aware constructor for character/whitespace fix producers. Drops every
    edit in [fix] whose start offset falls inside a verbatim / inline \verb /
    comment / url / math region of [src] (via [find_exempt_ranges]), then builds
    a [mk_result_with_fix] from what survives, or a plain [mk_result] if nothing
    does. [count] is supplied by the caller and is NOT touched — the diagnostic
    still tallies every occurrence (so default-mode lint and the differential
    are unchanged); only the FIX is withheld inside protected regions, where
    rewriting literal bytes (a 3-byte fullwidth char → ASCII, a control byte or
    BOM deleted, a tab expanded) would corrupt content the author wrote
    verbatim. Centralises the P3 exempt principle for the older CHAR/CJK/ENC/SPC
    producers that predate it (v27.1.4 verbatim-exemption safety fix). *)
let mk_result_with_fix_exempt ~id ~severity ~message ~count ~src ~fix =
  let exempt = find_exempt_ranges src in
  let fix' =
    List.filter
      (fun (e : Cst_edit.t) -> not (is_in_exempt_range exempt e.start_offset))
      fix
  in
  if fix' = [] then mk_result ~id ~severity ~message ~count
  else mk_result_with_fix ~id ~severity ~message ~count ~fix:fix'

(** [mk_result_with_fix_vcu_exempt ~id ~severity ~message ~count ~src ~fix] —
    the MATH-targeting counterpart of [mk_result_with_fix_exempt]. A rule that
    fixes inside math (e.g. MATH-014 `\frac`→`\tfrac`, SCRIPT-016 `''`→prime)
    finds its targets via [find_math_ranges], which treats a `$..$` written
    inside a `verbatim` / `\verb` / comment as math — so the fix would rewrite
    that literal source. This drops only edits inside the verbatim/comment/url
    ([find_verbatim_comment_url_ranges]) set, KEEPING genuine in-math edits (it
    must not use the full exempt set, which includes math). Count is untouched. *)
let mk_result_with_fix_vcu_exempt ~id ~severity ~message ~count ~src ~fix =
  let vcu = find_verbatim_comment_url_ranges src in
  let fix' =
    List.filter
      (fun (e : Cst_edit.t) -> not (is_in_exempt_range vcu e.start_offset))
      fix
  in
  if fix' = [] then mk_result ~id ~severity ~message ~count
  else mk_result_with_fix ~id ~severity ~message ~count ~fix:fix'

(** [candidates_drop_exempt src cands] — Bucket-C candidate counterpart of
    [mk_result_with_fix_exempt], for TEXT rules. Drops every candidate whose
    FIRST edit's start offset falls inside a verbatim / inline \verb / comment /
    url / math region of [src] (via [find_exempt_ranges]), so a suggestion is
    never offered against bytes the author wrote literally. A candidate with an
    EMPTY [c_edits] carries no offset and therefore CANNOT be located here, so
    it is KEPT — a rule that emits such a label-only candidate is responsible
    for its own exempt gating (see VERB-006). The diagnostic count is
    unaffected: the caller degrades to [mk_result] itself if the surviving
    candidate list is empty. *)
let candidates_drop_exempt (src : string) (cands : candidate_fix list) :
    candidate_fix list =
  let exempt = find_exempt_ranges src in
  List.filter
    (fun (c : candidate_fix) ->
      match c.c_edits with
      | (e : Cst_edit.t) :: _ -> not (is_in_exempt_range exempt e.start_offset)
      | [] -> true)
    cands

(** [candidates_drop_vcu_exempt src cands] — MATH-targeting counterpart of
    [candidates_drop_exempt] (mirrors [mk_result_with_fix_vcu_exempt]). Drops
    only candidates whose first edit lands in a verbatim / comment / url region
    ([find_verbatim_comment_url_ranges]), KEEPING genuine in-math candidates —
    for rules whose targets are themselves math (align / matrix environments),
    where the full exempt set (which includes math) would wrongly discard every
    candidate. Label-only candidates (empty [c_edits]) are kept for the rule to
    gate itself. *)
let candidates_drop_vcu_exempt (src : string) (cands : candidate_fix list) :
    candidate_fix list =
  let vcu = find_verbatim_comment_url_ranges src in
  List.filter
    (fun (c : candidate_fix) ->
      match c.c_edits with
      | (e : Cst_edit.t) :: _ -> not (is_in_exempt_range vcu e.start_offset)
      | [] -> true)
    cands

(** [is_ascii_context ?window ?candidate_bytes s off] — heuristic that returns
    [true] iff the byte window of size [window] (default 32) on each side of the
    candidate UTF-8 sequence at [off] (of length [candidate_bytes], default 3)
    is majority ASCII (bytes < 0x80). The candidate's own bytes are excluded
    from the tally so the multibyte sequence under inspection cannot dominate
    its own context decision.

    Used by CJK rules (CJK-001 fullwidth comma, CJK-002 fullwidth period) to
    gate fixes that swap CJK punctuation for ASCII equivalents. The rule still
    diagnoses every occurrence; the fix is suppressed when surrounding text is
    majority non-ASCII (i.e. the document genuinely uses CJK punctuation and the
    U+FF0x form is intentional). Ties (ascii = extended) resolve to [false] —
    only a strict ASCII majority triggers a fix. *)
let is_ascii_context ?(window = 32) ?(candidate_bytes = 3) (s : string)
    (off : int) : bool =
  let n = String.length s in
  let lo = max 0 (off - window) in
  let hi = min (n - 1) (off + candidate_bytes - 1 + window) in
  let ascii = ref 0 in
  let extended = ref 0 in
  for j = lo to hi do
    if j < off || j >= off + candidate_bytes then
      if Char.code (String.unsafe_get s j) < 0x80 then incr ascii
      else incr extended
  done;
  !ascii > !extended

(** [is_extended_context ?window ?candidate_bytes s off] — symmetric inverse of
    [is_ascii_context]. Returns [true] iff the surrounding window contains
    strictly more extended bytes (≥ 0x80) than ASCII bytes (< 0x80). The
    candidate's own bytes are excluded.

    Used by CJK-010 (half-width punctuation in full-width context) to gate the
    inverse fix: replace an ASCII punctuation byte with its fullwidth Unicode
    equivalent only when the surrounding text is genuinely CJK-heavy. Ties
    resolve to [false] — only a strict extended majority triggers a fix, so an
    isolated ASCII-context character won't be promoted to fullwidth on the
    strength of a single neighbouring CJK byte. *)
let is_extended_context ?(window = 32) ?(candidate_bytes = 3) (s : string)
    (off : int) : bool =
  let n = String.length s in
  let lo = max 0 (off - window) in
  let hi = min (n - 1) (off + candidate_bytes - 1 + window) in
  let ascii = ref 0 in
  let extended = ref 0 in
  for j = lo to hi do
    if j < off || j >= off + candidate_bytes then
      if Char.code (String.unsafe_get s j) < 0x80 then incr ascii
      else incr extended
  done;
  !extended > !ascii

(** [has_cyrillic_context ?window s off] — [true] iff a Cyrillic character
    (U+0400..U+04FF, encoded in UTF-8 as a lead byte 0xD0..0xD3 followed by a
    0x80..0xBF continuation byte) occurs within [window] bytes (default 32) on
    either side of [off].

    Used to make the Russian NBSP-before-em-dash producer (RU-001, inserts a
    NBSP) and its English-oriented inverse (SPC-033, removes that NBSP) mutually
    exclusive BY CONTEXT: RU-001 only emits its fix when this returns [true],
    SPC-033 only emits its fix when it returns [false]. The two producers run
    universally (unfiltered by language) in the [--apply-fixes] converge loop,
    so without this complementary gate they would oscillate forever (space→NBSP→
    space…). Neither rule's COUNT is affected — only the fix-set is gated. *)
let has_cyrillic_context ?(window = 32) (s : string) (off : int) : bool =
  let n = String.length s in
  let lo = max 0 (off - window) in
  let hi = min (n - 1) (off + window) in
  let rec scan j =
    if j >= hi then false
    else
      let c = Char.code (String.unsafe_get s j) in
      let d = Char.code (String.unsafe_get s (j + 1)) in
      if c >= 0xD0 && c <= 0xD3 && d >= 0x80 && d <= 0xBF then true
      else scan (j + 1)
  in
  scan lo

(* -- Conservative sentence-boundary detection (Bucket-B pilot) --
   [is_sentence_end_period s i] decides whether the ASCII `.` at byte offset [i]
   is a GENUINE end-of-sentence period, as opposed to an abbreviation dot, an
   initial, a decimal point, or part of an ellipsis. Deliberately CONSERVATIVE:
   returns [false] when unsure. *)
let sentence_abbreviations : (string, unit) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  List.iter
    (fun w -> Hashtbl.replace tbl w ())
    [
      "e.g";
      "i.e";
      "etc";
      "cf";
      "vs";
      "al";
      "viz";
      "resp";
      "approx";
      "fig";
      "eq";
      "ch";
      "sec";
      "tab";
      "no";
      "pp";
      "vol";
      "ed";
      "eds";
      "dr";
      "mr";
      "mrs";
      "ms";
      "prof";
      "st";
      "jr";
      "sr";
      "inc";
      "ltd";
      "co";
      "corp";
      "univ";
      "dept";
      "e";
      "i";
      "w";
      (* v27.1.15: months, titles, plurals, scholarly abbrevs (verify-driven) *)
      "jan";
      "feb";
      "mar";
      "apr";
      "jun";
      "jul";
      "aug";
      "sep";
      "sept";
      "oct";
      "nov";
      "dec";
      "gen";
      "sen";
      "gov";
      "col";
      "capt";
      "lt";
      "sgt";
      "rev";
      "rep";
      "mt";
      "ave";
      "rd";
      "hon";
      "pres";
      "supt";
      "adm";
      "cmdr";
      "messrs";
      "op";
      "cit";
      "ibid";
      "seq";
      "ff";
      "ca";
      "circa";
      "chap";
      "par";
      "sect";
      "art";
      "div";
      "nos";
      "vols";
      "figs";
      "eqs";
      "chaps";
      "secs";
      "min";
      "max";
    ];
  tbl

let is_ascii_letter (c : char) : bool =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

let is_ascii_digit_c (c : char) : bool = c >= '0' && c <= '9'

(* -- Common-English-word ALLOWLIST (Bucket-B word-frequency layer) --
   [is_sentence_end_period] now fires only when the word ending at the `.` is a
   REAL, frequent English word. This flips the predicate from a blocklist (which
   could not distinguish an unknown lowercase word from a lowercase dotted
   identifier such as `github.Com`, `obj.Method`, `numpy.Array`) to a positive
   allowlist: a sentence that ends in an uncommon technical word is a MISS
   (acceptable for an auto-fix), while a lowercase identifier — never a common
   English word — is never corrupted.

   The set is ~1500 of the most frequent English words, deliberately including
   the common academic / technical words that end sentences in papers (result,
   method, theorem, lemma, proof, value, function, figure, table, section,
   model, data, etc.). Stored lowercased. Words are grouped per source line only
   for readability; each line is whitespace-split at load. *)
let common_english_words : (string, unit) Hashtbl.t =
  let tbl = Hashtbl.create 4096 in
  let src =
    [
      "done finished complete ready above below shown given holds thus hence";
      "next then now here there today first second third final also since while";
      "when where what which done";
      (* general high-frequency function/content words *)
      "the be to of and a in that have it for not on with he as you do at this";
      "but his by from they we say her she or an will my one all would there";
      "their what so up out if about who get which go me when make can like \
       time";
      "no just him know take people into year your good some could them see \
       other";
      "than then now look only come its over think also back after use two how \
       our";
      "work first well way even new want because any these give day most us is \
       are";
      "was were been has had did does said made went gone being am being here \
       where";
      "why while very much many more less few little own same such each every \
       both";
      "under above below between within without across through during before \
       after";
      "again against always never often sometimes usually already still yet \
       ever";
      "however therefore thus hence moreover furthermore nevertheless otherwise";
      "instead indeed rather quite almost enough perhaps maybe likely certainly";
      "clearly simply merely mainly mostly partly fully wholly nearly roughly";
      "around near far away along behind beside beyond toward towards onto upon";
      "off down inside outside forward backward upward downward left right top";
      "bottom middle centre center side front rear edge corner end start begin";
      "began begun finish finished complete completed continue continued remain";
      "remained become became turn turned keep kept hold held bring brought";
      "carry carried move moved run ran walk walked stand stood sit sat lie lay";
      "put set let get got give given take taken made make find found lose lost";
      "win won buy bought sell sold pay paid send sent read write wrote written";
      "speak spoke spoken tell told ask asked answer answered call called name";
      "named show shown showed prove proved proven mean meant meaning follow";
      "follows followed leading led allow allowed enable enabled require \
       required";
      "provide provided produce produced obtain obtained observe observed note";
      "noted notice noticed consider considered assume assumed suppose supposed";
      "define defined describe described denote denoted derive derived apply";
      "applied compute computed calculate calculated estimate estimated measure";
      "measured evaluate evaluated verify verified confirm confirmed check \
       checked";
      "test tested compare compared contrast related relate relates depend";
      "depends increase increased decrease decreased reduce reduced improve";
      "improved extend extended generalize generalized represent represented";
      "denote denotes satisfy satisfies satisfied hold holds imply implies";
      "yield yields express expressed express solve solved analyze analyzed";
      (* academic / paper vocabulary — sentence-ending words in prose *)
      "result results method methods theorem theorems lemma lemmas proof proofs";
      "corollary proposition conjecture definition definitions example examples";
      "value values function functions figure figures table tables section";
      "sections chapter chapters model models data case cases form forms set";
      "sets point points space spaces time times work paper papers study \
       studies";
      "analysis system systems problem problems solution solutions approach";
      "approaches algorithm algorithms matrix matrices vector vectors number";
      "numbers equation equations variable variables parameter parameters";
      "constant constants field fields group groups ring domain range image";
      "graph graphs tree trees node nodes edge path paths cycle chain series";
      "sequence sequences limit limits bound bounds error errors rate rates";
      "sample samples population mean median mode variance distribution density";
      "probability event events state states process processes measure measures";
      "metric metrics norm scalar tensor operator operators map mapping element";
      "elements subset subsets member members class classes object objects type";
      "types property properties feature features factor factors term terms";
      "condition conditions assumption assumptions hypothesis theory theories";
      "framework frameworks structure structures pattern patterns behavior";
      "behaviour performance accuracy precision recall quality property scheme";
      "strategy strategies technique techniques procedure procedures step steps";
      "phase phases stage stages level levels layer layers scale scales unit \
       units";
      "component components module modules network networks input inputs output";
      "outputs signal signals source sources target targets label labels weight";
      "weights score scores cost costs loss gradient function derivative \
       integral";
      "sum product ratio proportion fraction percentage average total count \
       size";
      "length width height depth area volume mass force energy power speed";
      "velocity distance position location region area boundary interior \
       surface";
      (* more everyday content words that legitimately end sentences *)
      "man woman child children person world life hand part place home school";
      "state country city house room door word words page book books story";
      "question questions idea ideas fact facts reason reasons power light \
       water";
      "air land food money business company family friend friends group team";
      "member game war history art music science nature light dark color colour";
      "line lines order group face book eye head heart mind body voice sound";
      "picture story fact truth change effect cause result matter subject topic";
      "issue point view side matter thing things something nothing anything";
      "everything someone anyone everyone nobody bar aside apart alike alone";
      "big small large great high low long short old young early late easy hard";
      "true false right wrong open close full empty free whole half main real";
      "clear certain sure common general special particular important necessary";
      "possible available different similar equal exact precise correct valid";
      "simple complex basic final initial current recent future past present";
      "actual usual normal standard typical natural human social global local";
      "physical mental formal informal direct indirect positive negative active";
      (* v27.1.20 depth: common long-tail nouns/verbs/adverbs (real English
         only) *)
      "month months week weeks hour hours minute minutes second seconds moment";
      "morning evening night day days year years today yesterday tomorrow";
      "job jobs service services business industry market markets economy";
      "father mother parent parents family families friend community society";
      "law laws court government president leader leaders policy policies";
      "car cars road roads street city town village country nation region";
      "health medicine doctor patient hospital disease treatment care";
      "office building room rooms house home floor wall window street";
      "party event meeting conference session lecture talk presentation";
      "research analysis experiment observation measurement sample dataset";
      "teacher student education school class course lesson exam degree";
      "information knowledge understanding awareness insight evidence detail";
      "make makes take takes give gives find finds use uses work works call";
      "need needs feel feels become leave leaves put mean means keep begins";
      "help talk turn start shows hear play run move live believe hold bring";
      "happen write provide sit stand lose pay meet include continue learn";
      "lead understand watch follow stop create speak read allow add spend";
      "grow open walk win offer remember love consider appear buy wait serve";
      "die send expect build stay fall cut reach remain apply differ occur";
      "again once always never often sometimes usually already still soon";
      "later indeed instead rather quite very really almost enough perhaps";
      "kind sort type way ways part parts lot piece pieces bit range set";
    ]
  in
  List.iter
    (fun line ->
      List.iter
        (fun w -> if String.length w > 0 then Hashtbl.replace tbl w ())
        (String.split_on_char ' ' line))
    src;
  tbl

(* [?require_common]: when [true] (default), the word ending at the `.` must be
   in the common-English allowlist for a positive result. This is the SAFE mode
   used by the SPC-018 auto-fix (byte-editing) so that lowercase dotted
   identifiers are never corrupted. Non-editing consumers that only need
   high-recall sentence SEGMENTATION (e.g. the L4 style rules' [sentence_split])
   pass [~require_common:false] to keep the pre-allowlist recall — they never
   rewrite bytes, so a lowercase identifier boundary there is harmless. *)
let is_sentence_end_period ?(require_common = true) (s : string) (i : int) :
    bool =
  let n = String.length s in
  if i < 0 || i >= n || s.[i] <> '.' then false
  else if (i + 1 < n && s.[i + 1] = '.') || (i > 0 && s.[i - 1] = '.') then
    false
  else if
    i > 0
    && i + 1 < n
    && is_ascii_digit_c s.[i - 1]
    && is_ascii_digit_c s.[i + 1]
  then false
  else if i = 0 || not (is_ascii_letter s.[i - 1]) then false
  else
    let rec back j =
      if j > 0 && is_ascii_letter s.[j - 1] then back (j - 1) else j
    in
    let ws = back i in
    let word = String.sub s ws (i - ws) in
    let word_lc = String.lowercase_ascii word in
    if String.length word < 2 then false
      (* Abbreviation blocklist is checked FIRST: an abbreviation whose spelling
         coincides with a common word (e.g. `no`, `co`) must still SUPPRESS. *)
    else if Hashtbl.mem sentence_abbreviations word_lc then false
    else if word.[0] >= 'A' && word.[0] <= 'Z' then
      (* the word ending at the period starts with a capital: a proper noun, an
         initialism (Ph.D), or a dotted identifier (System.Console) — never
         auto-treat as a sentence end. Conservative: costs recall on sentences
         that end in a proper noun, but eliminates the identifier/initialism
         false-positive class. *)
      false
    else if require_common && not (Hashtbl.mem common_english_words word_lc)
    then
      (* Positive ALLOWLIST requirement (Bucket-B word-frequency layer): fire
         only when the lowercase word is a KNOWN common English word. A bare
         lowercase dotted identifier — `github.Com`, `obj.Method`, `numpy.Array`
         — is never a common word, so it is suppressed and never corrupted. A
         sentence ending in an uncommon technical word is a MISS, which is
         acceptable for an auto-fix: a false positive (identifier corruption) is
         far worse than a miss. *)
      false
    else
      let rec next j =
        if j >= n then true
        else if s.[j] = ' ' || s.[j] = '\t' then next (j + 1)
        else
          let c = s.[j] in
          c >= 'A' && c <= 'Z'
      in
      next (i + 1)

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
          (* dedup within ctx, and drop any ctx name already seen by the token
             scan — the post-command summary and the literal token scan are two
             views of the same commands, so appending both double-counts. *)
          if
            List.exists (( = ) pc.name) acc
            || List.exists (( = ) pc.name) token_names
          then acc
          else pc.name :: acc)
        [] ctx
    in
    List.rev_append ctx_names_rev token_names

(* Helper: extract content blocks between \begin{env}...\end{env}

   DEPRECATED (Tier 2 Stage 2, V27_2 plan): this substring open/close scan is
   NOT comment/verbatim-aware and does NOT track nesting, so it matches a
   `\begin{env}` written inside a `%` comment or a verbatim/`\verb` span and can
   close the wrong `\end`. New code MUST use [Ast_semantic_state.environments] /
   [Ast_semantic_state.envs_named] (see [Validators_l2.ast_env_bodies] for the
   substring-materialising wrapper), which fixes both bug classes. Retained only
   for the not-yet-migrated legacy callers; the regex-vs-AST divergence on the
   lint corpus is pinned by scripts/tools/check_ast_parity.py. *)
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

(* [extract_env_block_ranges env s] — like [extract_env_blocks] but returns the
   absolute (content_start, content_end) byte range of each block body instead
   of the substring. Mirrors [extract_env_blocks]' open/close scan +
   optional-[...] skip byte-for-byte, so the bytes covered are identical — used
   by VERB-002 to emit edits at absolute offsets while keeping its
   substring-based count exact. *)
let extract_env_block_ranges (env : string) (s : string) : (int * int) list =
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
      let content_start = ref start in
      if !content_start < n && s.[!content_start] = '[' then (
        while !content_start < n && s.[!content_start] <> ']' do
          incr content_start
        done;
        if !content_start < n then incr content_start);
      let found = ref false in
      let j = ref !content_start in
      while !j <= n - close_len && not !found do
        if String.sub s !j close_len = close_tag then (
          blocks := (!content_start, !j) :: !blocks;
          i := !j + close_len;
          found := true)
        else incr j
      done;
      if not !found then i := n)
    else incr i
  done;
  List.rev !blocks

(** [find_verbatim_comment_ranges s] — byte ranges covering ONLY literal
    verbatim blocks (`verbatim`/`lstlisting`/`minted` environment bodies) and
    percent line-comments. Unlike [find_verbatim_comment_url_ranges] it
    deliberately EXCLUDES url targets, so a producer whose whole purpose is to
    edit `\url{}` content (SPC-027) can still fire in prose while withholding
    edits that land inside a verbatim block or comment. The comment scan honours
    backslash-escaping (`\%` is a literal percent, not a comment). *)
let find_verbatim_comment_ranges (s : string) : (int * int) list =
  let n = String.length s in
  let ranges =
    List.concat_map
      (fun env -> extract_env_block_ranges env s)
      [ "verbatim"; "lstlisting"; "minted" ]
  in
  let is_escaped idx =
    let rec count back acc =
      if back < 0 then acc
      else if String.unsafe_get s back = '\\' then count (back - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let ranges = ref ranges in
  let i = ref 0 in
  while !i < n do
    if String.unsafe_get s !i = '%' && not (is_escaped !i) then (
      let j = ref !i in
      while !j < n && String.unsafe_get s !j <> '\n' do
        incr j
      done;
      ranges := (!i, !j) :: !ranges;
      i := !j)
    else incr i
  done;
  List.sort (fun (a, _) (c, _) -> compare a c) !ranges

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
  let re = Re_compat.regexp {|\\usepackage\(\[[^]]*\]\)?{|} in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re s !i in
       let after_brace = Re_compat.match_end _mr in
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

(** [mk_usepackage_insert s pkg] — the fix edit(s) for an `insert_usepackage`
    producer: insert a `\usepackage{pkg}` line into the preamble, immediately
    after the `\documentclass{...}` line. Returns [] when there is no
    `\documentclass` (a fragment) so the producer degrades to diagnose-only
    there rather than inserting into an unknown position.

    Pairs with a detector gated on [not (has_package s pkg)]: after the insert
    [extract_usepackages] sees the new `\usepackage{pkg}`, so [has_package s pkg]
    holds and the rule no longer fires — idempotent and convergent (no producer
    removes a `\usepackage` line). The inserted text is pure ASCII, so it can
    never split a multibyte sequence, and the offset is an absolute position in
    the ORIGINAL [s]. The chosen packages (booktabs, csquotes, xeCJK, ruby,
    hyperref-when-nothing-else-provides-it) are load-order-insensitive at this
    position, so inserting right after \documentclass is safe. *)
let mk_usepackage_insert (s : string) (pkg : string) : Cst_edit.t list =
  let re = Re_compat.regexp_string "\\documentclass" in
  match
    try
      let mr, _ = Re_compat.search_forward re s 0 in
      Some (Re_compat.match_beginning mr)
    with Not_found -> None
  with
  | None -> []
  | Some dc ->
      let n = String.length s in
      let rec find_nl i =
        if i >= n then n else if s.[i] = '\n' then i else find_nl (i + 1)
      in
      let nl = find_nl dc in
      let at = if nl < n then nl + 1 else n in
      [ Cst_edit.insert ~at (Printf.sprintf "\\usepackage{%s}\n" pkg) ]

(** [control_word_repl s after word] — terminate a control-word replacement so
    it can never glue onto a following letter. A fix that replaces a symbol with
    a control word like [\cdot] must not yield [\cdotb] (an UNDEFINED control
    word / compile error) when the next source byte is a letter: TeX reads a
    control word greedily up to the first non-letter. This appends a single
    space to [word] iff the byte at [after] in [s] is an ASCII letter; digits,
    symbols, whitespace, multibyte bytes and EOF already terminate a control
    word, so those cases are byte-unchanged. In math mode the space is
    invisible, so no rendering changes — it only prevents the glue. Mirrors the
    trailing space MATH-044 already bakes into [\le ]/[\ge ]. *)
let control_word_repl (s : string) (after : int) (word : string) : string =
  if after < String.length s then
    let c = s.[after] in
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') then word ^ " "
    else word
  else word

(* ── Helper: extract env blocks for both env and env* ────────────────── *)
let extract_env_blocks_starred (env : string) (s : string) : string list =
  let plain = extract_env_blocks env s in
  let starred = extract_env_blocks (env ^ "*") s in
  plain @ starred

(* ── Helper: check for \caption{ or \caption[ (not \captionsetup etc.) *)
let has_caption (body : string) : bool =
  let re = Re_compat.regexp {|\\caption\(\[\|{\)|} in
  try
    let _mr, _ = Re_compat.search_forward re body 0 in
    ignore _mr;
    true
  with Not_found -> false

(* ── Helper: extract all \label{prefix:...} keys ──────────────────────── *)
(* DEPRECATED (Tier 2 Stage 2, V27_2 plan): this regex scan matches `\label{}`
   tokens inside comments / verbatim / `\verb` / url spans (false matches). The
   comment/verbatim-aware replacement is [Ast_semantic_state.labels] (+
   [labels_by_env]); REF-008/REF-010 already run on it. New label/ref code MUST
   use the AST extractors. This helper is retained only for the remaining legacy
   callers (MATH-024/MATH-023 eq: and the fig:/caption rules); the regex-vs-AST
   divergence is pinned by scripts/tools/check_ast_parity.py, which asserts the
   two agree except on protected-region false matches. *)
let extract_labels_with_prefix (prefix : string) (s : string) :
    (int * string) list =
  let re =
    Re_compat.regexp ("\\\\label{" ^ Re_compat.quote prefix ^ "\\([^}]*\\)}")
  in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re s !i in
       let key = Re_compat.matched_group _mr 1 s in
       results := (pos, prefix ^ key) :: !results;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  List.rev !results

(* ── Helper: extract all \ref{prefix:...}, \eqref{prefix:...},
   \autoref{prefix:...}, \cref{prefix:...} keys ──────────── *)
(* DEPRECATED (Tier 2 Stage 2): comment/verbatim-blind, like
   [extract_labels_with_prefix]. Replacement: [Ast_semantic_state.refs]. See the
   note on [extract_labels_with_prefix] above and check_ast_parity.py. *)
let extract_refs_with_prefix (prefix : string) (s : string) :
    (int * string) list =
  let re =
    Re_compat.regexp
      ("\\\\\\(eq\\)?ref{"
      ^ Re_compat.quote prefix
      ^ "\\([^}]*\\)}"
      ^ "\\|\\\\autoref{"
      ^ Re_compat.quote prefix
      ^ "\\([^}]*\\)}"
      ^ "\\|\\\\cref{"
      ^ Re_compat.quote prefix
      ^ "\\([^}]*\\)}"
      ^ "\\|\\\\Cref{"
      ^ Re_compat.quote prefix
      ^ "\\([^}]*\\)}")
  in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re s !i in
       (* Try each group to find the match *)
       let key =
         try Re_compat.matched_group _mr 2 s
         with Not_found -> (
           try Re_compat.matched_group _mr 3 s
           with Not_found -> (
             try Re_compat.matched_group _mr 4 s
             with Not_found -> Re_compat.matched_group _mr 5 s))
       in
       results := (pos, prefix ^ key) :: !results;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  List.rev !results

(* ── Helper: extract document class name ─────────────────────────────── *)
(* Matches \documentclass[opts]{classname} or \documentclass{classname}. *)
let extract_docclass (s : string) : string option =
  let re =
    Re_compat.regexp "\\\\documentclass\\(\\[[^]]*\\]\\)?{\\([^}]+\\)}"
  in
  try
    let _mr, _ = Re_compat.search_forward re s 0 in
    ignore _mr;
    Some (Re_compat.matched_group _mr 2 s)
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
  let re = Re_compat.regexp {|\\usepackage\(\[[^]]*\]\)?{|} in
  let re_opts = Re_compat.regexp {|\[\([^]]*\)\]|} in
  let results = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re s !i in
       let full = Re_compat.matched_string _mr s in
       let after_brace = Re_compat.match_end _mr in
       let opts =
         try
           let _mr, _ = Re_compat.search_forward re_opts full 0 in
           Re_compat.matched_group _mr 1 full
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
  let re = Re_compat.regexp {|\\caption{|} in
  try
    let _mr, _ = Re_compat.search_forward re body 0 in
    let start = Re_compat.match_end _mr in
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
  let re = Re_compat.regexp "@[a-zA-Z]+{" in
  let entries = ref [] in
  let starts = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re s !i in
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
let count_matches (re : Re_compat.regexp) (s : string) : int =
  let cnt = ref 0 in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re s !i in
       incr cnt;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  !cnt

(* Helpers for L1 paragraph-aware mixing using post-command spans *)

(* [mixed_paragraph_ranges s ~legacy ~modern] — the (offset, len) spans of every
   paragraph that contains BOTH a legacy and a modern command (from the given
   sets). This is the offset-carrying core of [has_mixed_in_paragraphs] (which
   is just [<> []]); the MOD-002..007 Bucket-C candidates use the ranges to
   locate the legacy tokens that need normalising, so the returned spans and the
   boolean firing decision stay in lock-step (the diagnostic count is
   unchanged). *)
let mixed_paragraph_ranges (s : string) ~(legacy : string list)
    ~(modern : string list) : (int * int) list =
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
  List.filter (fun (off, len) -> check_para off len) ranges

let has_mixed_in_paragraphs (s : string) ~(legacy : string list)
    ~(modern : string list) : bool =
  mixed_paragraph_ranges s ~legacy ~modern <> []

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
      "alignat";
      "alignat*";
      "flalign";
      "flalign*";
      "eqnarray";
      "IEEEeqnarray";
      "IEEEeqnarray*";
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
let count_re_matches (re : Re_compat.regexp) (s : string) : int =
  let cnt = ref 0 in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re s !i in
       incr cnt;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  !cnt

(* Helper: extract all \label{...} values from source *)
let extract_labels (s : string) : string list =
  let re = Re_compat.regexp {|\\label{[^}]*}|} in
  let labels = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re s !i in
       let m = Re_compat.matched_string _mr s in
       let next = Re_compat.match_end _mr in
       (* extract content between { and } *)
       let inner = String.sub m 7 (String.length m - 8) in
       labels := inner :: !labels;
       i := next
     done
   with Not_found -> ());
  List.rev !labels

(* Helper: extract all \ref{...} and \eqref{...} label references *)
let extract_refs (s : string) : string list =
  let re = Re_compat.regexp {|\\eqref{[^}]*}\|\\ref{[^}]*}|} in
  let refs = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re s !i in
       let m = Re_compat.matched_string _mr s in
       let next = Re_compat.match_end _mr in
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
