(** Unit tests for [Ast_semantic_state] — the comment/verbatim-aware,
    nesting-correct environment extractor and the inline-vs-display math
    segmenter (Tier 2 Stage 1 of V27_L3_AST_PLAN).

    The regex environment extractor this module replaces had two bug
    classes: (a) it matched `\begin{..}` tokens inside comments / verbatim
    / `\verb`, and (b) it did not track nesting, so `\end` could close the
    wrong `\begin`. These tests assert the exact byte spans (never
    [expect true]) for both the happy path and every one of those failure
    modes, plus graceful handling of unbalanced / unclosed environments. *)

open Printf
open Latex_parse_lib.Ast_semantic_state

let fails = ref 0
let total = ref 0

(* Compact rendering of an env_node for failure diagnostics. *)
let show_env (e : env_node) : string =
  sprintf "{name=%S depth=%d body=[%d,%d) opt=[%s]}" e.name e.depth
    e.body.start_off e.body.end_off
    (String.concat ";" e.opt_args)

(* Assert an env list matches the expected tuples (name, depth, body_start,
   body_end, opt_args), position-by-position. *)
let check_envs label src
    (expected : (string * int * int * int * string list) list) : unit =
  incr total;
  let got = environments src in
  let ok =
    List.length got = List.length expected
    && List.for_all2
         (fun (e : env_node) (name, depth, bs, be, opt) ->
           e.name = name
           && e.depth = depth
           && e.body.start_off = bs
           && e.body.end_off = be
           && e.opt_args = opt)
         got expected
  in
  if not ok then (
    incr fails;
    eprintf "[ast-env] FAIL %s\n  src: %S\n  expected %d env(s):\n" label src
      (List.length expected);
    List.iter
      (fun (name, depth, bs, be, opt) ->
        eprintf "    {name=%S depth=%d body=[%d,%d) opt=[%s]}\n" name depth bs
          be (String.concat ";" opt))
      expected;
    eprintf "  got %d env(s):\n" (List.length got);
    List.iter (fun e -> eprintf "    %s\n" (show_env e)) got;
    eprintf "%!")

(* Assert a math-segment list matches (start, end, display) tuples. *)
let check_math label src (expected : (int * int * bool) list) : unit =
  incr total;
  let got = math_segments src in
  let ok =
    List.length got = List.length expected
    && List.for_all2
         (fun (m : math_seg) (a, b, d) ->
           m.seg.start_off = a && m.seg.end_off = b && m.display = d)
         got expected
  in
  if not ok then (
    incr fails;
    eprintf "[ast-math] FAIL %s\n  src: %S\n  expected:\n" label src;
    List.iter
      (fun (a, b, d) -> eprintf "    [%d,%d) display=%b\n" a b d)
      expected;
    eprintf "  got:\n";
    List.iter
      (fun m ->
        eprintf "    [%d,%d) display=%b\n" m.seg.start_off m.seg.end_off
          m.display)
      got;
    eprintf "%!")

let () =
  (* ── 1. Nested: align inside figure, opt-arg on figure. ───────────── *)
  let nested =
    "\\begin{figure}[ht]\ncap\n\\begin{align}\nx=1\n\\end{align}\n\\end{figure}"
  in
  check_envs "nested align-in-figure" nested
    [ ("figure", 0, 18, 53, [ "ht" ]); ("align", 1, 36, 41, []) ];

  (* ── 2. `\begin` inside a % comment is NOT an environment. ─────────── *)
  let commented =
    "text\n% \\begin{figure}\nreal\n\\begin{table}\nT\n\\end{table}"
  in
  check_envs "begin-in-comment ignored" commented [ ("table", 0, 40, 43, []) ];

  (* ── 3. `\begin`/`\end` inside a verbatim environment are literal. ── *)
  let verb_env =
    "\\begin{verbatim}\n\
     \\begin{figure}\n\
     \\end{verbatim}\n\
     \\begin{table}\n\
     X\n\
     \\end{table}"
  in
  check_envs "begin-in-verbatim ignored" verb_env [ ("table", 0, 60, 63, []) ];

  (* ── 4. `\begin` inside inline `\verb|...|` is literal. ───────────── *)
  let verb_inline =
    "before \\verb|\\begin{figure}| after \\begin{itemize}\nA\n\\end{itemize}"
  in
  check_envs "begin-in-verb-inline ignored" verb_inline
    [ ("itemize", 0, 50, 53, []) ];

  (* ── 5. Starred environments; envs_named is exact-match by name. ──── *)
  let starred =
    "\\begin{align*}\ny=2\n\\end{align*}\n\\begin{align}\nz=3\n\\end{align}"
  in
  check_envs "starred + plain both parsed" starred
    [ ("align*", 0, 14, 19, []); ("align", 0, 45, 50, []) ];
  (* envs_named exact-match semantics. *)
  incr total;
  (match envs_named starred "align" with
  | [ e ] when e.name = "align" && e.body.start_off = 45 && e.body.end_off = 50
    ->
      ()
  | got ->
      incr fails;
      eprintf
        "[ast-env] FAIL envs_named \"align\" excludes \"align*\"\n  got: %s\n%!"
        (String.concat ", " (List.map show_env got)));
  incr total;
  (match envs_named starred "align*" with
  | [ e ] when e.name = "align*" && e.body.start_off = 14 -> ()
  | got ->
      incr fails;
      eprintf "[ast-env] FAIL envs_named \"align*\"\n  got: %s\n%!"
        (String.concat ", " (List.map show_env got)));

  (* ── 6. Unbalanced `\end{align}` (never opened) dropped gracefully; the
     enclosing figure still closes correctly. ─────────────────── *)
  let unbalanced =
    "\\begin{figure}\ncontent\n\\end{align}\nmore\n\\end{figure}"
  in
  check_envs "unbalanced end dropped" unbalanced [ ("figure", 0, 14, 40, []) ];

  (* ── 7. Unclosed `\begin` yields no node (no exception). ──────────── *)
  let unclosed = "text \\begin{figure} no end here" in
  check_envs "unclosed begin dropped" unclosed [];

  (* ── 8. Math: inline ($..$, \(..\)) vs display ($$..$$, \[..\]). ──── *)
  let math_mix = "a $x+1$ b $$y=2$$ c \\(z\\) d \\[w\\]" in
  check_math "inline vs display" math_mix
    [ (2, 7, false); (10, 17, true); (20, 25, false); (28, 33, true) ];

  (* ── 9. A `$` inside a comment does not desync math pairing. ──────── *)
  let math_comment = "a $x$ % $ignored comment\nb $y$" in
  check_math "comment dollar ignored" math_comment
    [ (2, 5, false); (27, 30, false) ];

  if !fails = 0 then (
    printf "[ast-semantic-state] PASS %d cases\n%!" !total;
    exit 0)
  else (
    eprintf "[ast-semantic-state] %d/%d FAILED\n%!" !fails !total;
    exit 1)
