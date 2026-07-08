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
