(* ══════════════════════════════════════════════════════════════════════
   Ast_semantic_state — Tier 2 Stage 1 of V27_L3_AST_PLAN
   (specs/v27/L3_MIGRATION_INVENTORY.md).

   A small, byte-accurate, AST-derived structural model of a LaTeX source
   string: the load-bearing new capability is a comment/verbatim-aware,
   correctly-nested `\begin{..}..\end{..}` environment extractor plus a thin
   wrapper over [Validators_common.find_math_ranges] / [range_is_inline_math]
   that tags each math segment inline-vs-display.

   This module is ADDITIVE. It reuses the existing protected-region and
   math-range scanners from [Validators_common] rather than reimplementing them
   — the whole point is to fix the comment/verbatim false-match and nesting bugs
   of the regex environment extractor it is meant to replace.

   Design note (why not a regex): a `\begin{figure}` written inside a `%`
   comment, a verbatim environment, or an inline `\verb|...|` is NOT an
   environment; and `\end{name}` must close the matching `\begin{name}` even
   under nesting. Both properties fall out of a single left-to-right scan that
   (a) consults [find_verbatim_comment_url_ranges] to skip protected bytes and
   (b) maintains an explicit open-environment stack.
   ══════════════════════════════════════════════════════════════════════ *)

open Validators_common

type span = { start_off : int; end_off : int }
(** Half-open byte span from start_off (inclusive) to end_off (exclusive). *)

type env_node = {
  name : string;
  body : span;
  opt_args : string list;
  depth : int;
}
(** One `\begin{name}[opt]..\end{name}` block.

    - [name] is the environment name (starred names such as [align*] are
      kept verbatim).
    - [body] is the half-open span of the environment body: it starts
      immediately after the closing `}` of `\begin{name}` and its
      optional `[...]` arguments, and ends at the `\` of the matching
      `\end{name}`.
    - [opt_args] holds the raw contents of each `[...]` optional argument
      group that immediately follows `\begin{name}` (top-to-bottom).
    - [depth] is the nesting depth, 0 for a top-level environment and +1
      for each enclosing environment. *)

type math_seg = { seg : span; display : bool }
(** A math segment. [seg] is the byte span (including the delimiters), and
    [display] is [true] for display math (`$$..$$`, `\[..\]`, and the math
    display environments) and [false] for inline math (`$..$`, `\(..\)`). *)

(* ── Local byte helpers (kept private to this module) ─────────────────── *)

let is_escaped (s : string) (idx : int) : bool =
  let rec count back acc =
    if back < 0 then acc
    else if String.unsafe_get s back = '\\' then count (back - 1) (acc + 1)
    else acc
  in
  count (idx - 1) 0 land 1 = 1

let starts_with (s : string) (prefix : string) (idx : int) : bool =
  let plen = String.length prefix in
  idx + plen <= String.length s && String.sub s idx plen = prefix

(* [off] is inside one of [ranges] (half-open). Ranges are small in practice
   (comments/verbatim/url spans), so a linear scan is fine. *)
let in_ranges (ranges : (int * int) list) (off : int) : bool =
  List.exists (fun (a, b) -> a <= off && off < b) ranges

(* Read the `{name}` group whose `{` is at [brace] (a `}`-terminated run with no
   nested braces — environment names never contain braces). Returns [(name,
   idx_after_close_brace)] or [None] if unterminated. *)
let read_env_name (s : string) (brace : int) : (string * int) option =
  let n = String.length s in
  if brace >= n || s.[brace] <> '{' then None
  else
    let j = ref (brace + 1) in
    while !j < n && String.unsafe_get s !j <> '}' do
      incr j
    done;
    if !j >= n then None
    else Some (String.sub s (brace + 1) (!j - brace - 1), !j + 1)

(* Parse the run of `[...]` optional-argument groups that immediately follow
   position [p]. Returns [(contents, body_start)] where [contents] is the raw
   text of each group top-to-bottom and [body_start] is the first byte past the
   last group (= [p] when there is none). *)
let read_opt_args (s : string) (p : int) : string list * int =
  let n = String.length s in
  let rec loop pos acc =
    if pos < n && String.unsafe_get s pos = '[' then (
      let k = ref (pos + 1) in
      while !k < n && String.unsafe_get s !k <> ']' do
        incr k
      done;
      if !k >= n then (List.rev acc, pos) (* unterminated: no opt arg *)
      else loop (!k + 1) (String.sub s (pos + 1) (!k - pos - 1) :: acc))
    else (List.rev acc, pos)
  in
  loop p []

(* Internal open-environment stack frame. *)
type frame = {
  fname : string;
  fbody_start : int;
  fbegin : int; (* offset of the `\` in `\begin{..}` — used for ordering *)
  fdepth : int;
  fopt : string list;
}

(** [environments s] — every environment block in [s], returned top-to-
    bottom by opening position, with correctly-nested body spans. A
    `\begin`/`\end` inside a comment, verbatim environment, `\verb`/
    `\lstinline` span, or url argument is NOT treated as an environment
    (those bytes are literal). Unmatched `\end{..}` and unclosed
    `\begin{..}` are dropped gracefully (no node, no exception). *)
let environments (s : string) : env_node list =
  let n = String.length s in
  let protected = find_verbatim_comment_url_ranges s in
  let stack = ref [] in
  let out = ref [] in
  let i = ref 0 in
  while !i < n do
    let pos = !i in
    if
      String.unsafe_get s pos = '\\'
      && (not (is_escaped s pos))
      && not (in_ranges protected pos)
    then
      if starts_with s "\\begin{" pos then
        match read_env_name s (pos + 6) with
        | Some (name, after_name) ->
            let opt, body_start = read_opt_args s after_name in
            let depth = List.length !stack in
            stack :=
              {
                fname = name;
                fbody_start = body_start;
                fbegin = pos;
                fdepth = depth;
                fopt = opt;
              }
              :: !stack;
            i := body_start
        | None -> incr i
      else if starts_with s "\\end{" pos then
        match read_env_name s (pos + 4) with
        | Some (ename, after_name) ->
            (* Find the nearest open frame with this name. Frames above it are
               unclosed and discarded (graceful crossing handling). *)
            let rec split = function
              | [] -> None
              | fr :: rest ->
                  if fr.fname = ename then Some (fr, rest) else split rest
            in
            (match split !stack with
            | Some (fr, rest) ->
                stack := rest;
                out :=
                  ( fr.fbegin,
                    {
                      name = fr.fname;
                      body = { start_off = fr.fbody_start; end_off = pos };
                      opt_args = fr.fopt;
                      depth = fr.fdepth;
                    } )
                  :: !out
            | None -> () (* unmatched \end — drop *));
            i := after_name
        | None -> incr i
      else incr i
    else incr i
  done;
  (* Order top-to-bottom by opening position. *)
  !out |> List.sort (fun (a, _) (b, _) -> compare a b) |> List.map snd

(** [envs_named s name] — [environments s] filtered to a single environment name
    (exact match, so [envs_named s "align"] does not return [align*] blocks). *)
let envs_named (s : string) (name : string) : env_node list =
  List.filter (fun e -> e.name = name) (environments s)

(** [math_segments s] — every math segment of [s], each tagged
    inline-vs-display. Wraps [Validators_common.find_math_ranges] /
    [range_is_inline_math]; verbatim/comment/url bytes are blanked to spaces
    first (offsets preserved) so a stray `$` in a comment or code listing cannot
    desync math pairing. *)
let math_segments (s : string) : math_seg list =
  let vcu = find_verbatim_comment_url_ranges s in
  let blanked = Bytes.of_string s in
  List.iter
    (fun (a, b) ->
      for k = a to b - 1 do
        Bytes.set blanked k ' '
      done)
    vcu;
  let ranges = find_math_ranges (Bytes.unsafe_to_string blanked) in
  List.map
    (fun (a, b) ->
      {
        seg = { start_off = a; end_off = b };
        display = not (range_is_inline_math s (a, b));
      })
    ranges

(* ══════════════════════════════════════════════════════════════════════
   Stage-2 semantic label / ref / cite extraction (V27_2 plan T2-Stage2).

   These are the comment/verbatim-aware replacements for the regex extractors in
   [Semantic_state] ([extract_labels] / [extract_refs]) and the inline
   [Validators_common.extract_labels_with_prefix] / [extract_refs_with_prefix]
   regexes used by REF-008 / REF-010. A `\label{..}` / `\ref{..}` / `@entry{..}`
   token written inside a `%` comment, a verbatim environment, an inline
   `\verb|..|` / `\lstinline` span, or a url argument is NOT a real semantic
   declaration — those bytes are literal — so it is dropped here.

   PARITY CONTRACT (enforced by scripts/tools/check_ast_parity.py and
   test_ast_parity.ml): apart from that single correction — a match whose token
   offset lies inside a [find_verbatim_comment_url_ranges] span — these
   extractors return EXACTLY the same (offset, key) set as the regex extractors
   they replace. The scanners deliberately mirror the regex token grammar
   (`\label{`, `\(eq\)?ref{`, `\autoref{`, `\cref{`, `\Cref{`, `@[a-zA-Z]+{[
   \t]*<key>`), including NOT guarding against an escaped backslash, so the ONLY
   behavioural delta is the protected-region drop.
   ══════════════════════════════════════════════════════════════════════ *)

type label_entry = {
  key : string;  (** full label key, e.g. ["fig:overview"]. *)
  prefix : string;  (** ["fig:"] / ["eq:"] / … (up to and incl. first `:`). *)
  off : int;  (** byte offset of the `\` of `\label`. *)
  def_env : string option;
      (** name of the innermost enclosing environment, if any (figure, table,
          equation, …); [None] at top level. *)
}

type ref_entry = {
  key : string;
  command : string;  (** "ref" | "eqref" | "autoref" | "cref" | "Cref". *)
  off : int;  (** byte offset of the `\`. *)
}

type cite_entry = {
  key : string;  (** the bib entry key, e.g. ["knuth1984"]. *)
  etype : string;  (** the `@`-type letters, e.g. ["article"], ["book"]. *)
  off : int;  (** byte offset of the `@`. *)
}

let label_prefix (key : string) : string =
  match String.index_opt key ':' with
  | Some i -> String.sub key 0 (i + 1)
  | None -> ""

(* Innermost environment (deepest) whose body span contains [off]. *)
let innermost_env_of (envs : env_node list) (off : int) : string option =
  List.fold_left
    (fun acc e ->
      if e.body.start_off <= off && off < e.body.end_off then
        match acc with
        | Some (d, _) when d >= e.depth -> acc
        | _ -> Some (e.depth, e.name)
      else acc)
    None envs
  |> Option.map snd

(** [labels s] — every real `\label{..}` declaration, comment/verbatim-aware,
    tagged with its enclosing environment. Drop-in for
    [Validators_common.extract_labels_with_prefix ""] apart from the
    protected-region correction. *)
let labels (s : string) : label_entry list =
  let n = String.length s in
  let protected = find_verbatim_comment_url_ranges s in
  let envs = environments s in
  let out = ref [] in
  let i = ref 0 in
  while !i < n do
    let pos = !i in
    if
      String.unsafe_get s pos = '\\'
      && (not (in_ranges protected pos))
      && starts_with s "\\label{" pos
    then
      match read_env_name s (pos + 6) with
      | Some (key, after) ->
          out :=
            {
              key;
              prefix = label_prefix key;
              off = pos;
              def_env = innermost_env_of envs pos;
            }
            :: !out;
          i := after
      | None -> incr i
    else incr i
  done;
  List.rev !out

(** [labels_by_env s name] — [labels s] restricted to declarations whose
    innermost enclosing environment is exactly [name] (e.g. ["figure"]). *)
let labels_by_env (s : string) (name : string) : label_entry list =
  List.filter (fun l -> l.def_env = Some name) (labels s)

(* Reference commands recognised, longest-first is irrelevant because each has a
   distinct byte right after the `\`. Mirrors extract_refs_with_prefix. *)
let ref_commands =
  [
    ("\\eqref{", "eqref", 7);
    ("\\autoref{", "autoref", 9);
    ("\\cref{", "cref", 6);
    ("\\Cref{", "Cref", 6);
    ("\\ref{", "ref", 5);
  ]

(** [refs s] — every real cross-reference (`\ref` / `\eqref` / `\autoref` /
    `\cref` / `\Cref`), comment/verbatim-aware. Drop-in for
    [Validators_common.extract_refs_with_prefix ""]. *)
let refs (s : string) : ref_entry list =
  let n = String.length s in
  let protected = find_verbatim_comment_url_ranges s in
  let out = ref [] in
  let i = ref 0 in
  while !i < n do
    let pos = !i in
    if String.unsafe_get s pos = '\\' && not (in_ranges protected pos) then
      match
        List.find_opt (fun (tok, _, _) -> starts_with s tok pos) ref_commands
      with
      | Some (_, command, len) -> (
          match read_env_name s (pos + len - 1) with
          | Some (key, after) ->
              out := { key; command; off = pos } :: !out;
              i := after
          | None -> incr i)
      | None -> incr i
    else incr i
  done;
  List.rev !out

(** [cites s] — every BibTeX `@type{key, …}` entry key, comment/verbatim-aware.
    Drop-in for REF-008's `@[a-zA-Z]+{[ \t]*<key>` regex scan. This is the
    bib-entry key surface REF-008 (duplicate cite/bib keys) needs. *)
let cites (s : string) : cite_entry list =
  let n = String.length s in
  let protected = find_verbatim_comment_url_ranges s in
  let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  let is_key_byte c =
    c <> ',' && c <> ' ' && c <> '\t' && c <> '\n' && c <> '}'
  in
  let out = ref [] in
  let i = ref 0 in
  while !i < n do
    let pos = !i in
    if String.unsafe_get s pos = '@' && not (in_ranges protected pos) then (
      (* [a-zA-Z]+ *)
      let j = ref (pos + 1) in
      while !j < n && is_alpha (String.unsafe_get s !j) do
        incr j
      done;
      if !j > pos + 1 && !j < n && String.unsafe_get s !j = '{' then (
        let etype = String.sub s (pos + 1) (!j - pos - 1) in
        (* skip [ \t]* *)
        let k = ref (!j + 1) in
        while !k < n && (s.[!k] = ' ' || s.[!k] = '\t') do
          incr k
        done;
        let key_start = !k in
        while !k < n && is_key_byte (String.unsafe_get s !k) do
          incr k
        done;
        if !k > key_start then (
          out :=
            { key = String.sub s key_start (!k - key_start); etype; off = pos }
            :: !out;
          i := !k)
        else incr i)
      else incr i)
    else incr i
  done;
  List.rev !out
