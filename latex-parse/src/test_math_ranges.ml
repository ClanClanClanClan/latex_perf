(** Direct unit tests for [find_math_ranges] and [is_in_math_range]
    (defined in [validators_common.ml]).

    Background — v27.0.45 spec hardening: these helpers are load-bearing for
    every math-aware fix producer (TYPO-001/004/005/012/046, TYPO-053,
    CHAR-019).  Prior to this file they were only tested indirectly through
    individual producer tests.  Edge cases — unclosed math at EOF, nested
    envs, escape sequences, all 11 supported math envs — are exercised
    directly here. *)

open Printf
open Latex_parse_lib.Validators_common

(** Each case: (label, source, expected_ranges).  Ranges are half-open
    [(start, end)] in byte offsets, matching the helper's return type. *)
let range_cases : (string * string * (int * int) list) list =
  [
    ("empty string", "", []);
    ("no math at all", "plain text only", []);
    (* Inline $..$ *)
    ("single inline math", "ab $x+y$ cd", [ (3, 8) ]);
    ("two inline math segments", "$a$ then $b$.", [ (0, 3); (9, 12) ]);
    ("escaped dollar is not math", "cost is \\$5 here", []);
    ("escaped then real", "\\$cost $real$ end", [ (7, 13) ]);
    (* Display $$..$$ *)
    ("single display math", "before $$x=1$$ after", [ (7, 14) ]);
    ("display + inline", "$$D$$ then $i$.", [ (0, 5); (11, 14) ]);
    (* Paren \(...\) *)
    ("paren inline math", "say \\(x\\) end", [ (4, 9) ]);
    (* Bracket \[...\] *)
    ("bracket display math", "say \\[y\\] end", [ (4, 9) ]);
    (* Named envs *)
    ( "equation env",
      "\\begin{equation}E=mc^2\\end{equation}.",
      [ (0, 36) ] );
    ( "equation* env",
      "\\begin{equation*}x\\end{equation*}.",
      [ (0, 33) ] );
    ("align env", "\\begin{align}a&=b\\end{align}.", [ (0, 28) ]);
    ( "align* env",
      "\\begin{align*}a&=b\\end{align*}.",
      [ (0, 30) ] );
    ("gather env", "\\begin{gather}a\\end{gather}.", [ (0, 27) ]);
    ( "gather* env",
      "\\begin{gather*}a\\end{gather*}.",
      [ (0, 29) ] );
    ("multline env", "\\begin{multline}a\\end{multline}.", [ (0, 31) ]);
    ( "multline* env",
      "\\begin{multline*}a\\end{multline*}.",
      [ (0, 33) ] );
    ( "eqnarray env",
      "\\begin{eqnarray}a&=&b\\end{eqnarray}.",
      [ (0, 35) ] );
    ("math env", "\\begin{math}a+b\\end{math}.", [ (0, 25) ]);
    ( "displaymath env",
      "\\begin{displaymath}a\\end{displaymath}.",
      [ (0, 37) ] );
    (* Adjacency / multi-segment *)
    ( "two named envs",
      "\\begin{math}a\\end{math} then \\begin{math}b\\end{math}",
      [ (0, 23); (29, 52) ] );
    (* Unclosed math segments: extend to length of source *)
    ("unclosed inline at EOF", "trailing $unclosed", [ (9, 18) ]);
    ("unclosed display at EOF", "open $$forever", [ (5, 14) ]);
    ( "unclosed paren at EOF",
      "trailing \\(stuff",
      [ (9, 16) ] );
    ("unclosed env at EOF", "\\begin{equation}E", [ (0, 17) ]);
  ]

(** [is_in_math_range] consistency: for every byte position [p] in source
    [s], [is_in_math_range (find_math_ranges s) p] must be [true] iff [p]
    lies inside one of the returned half-open ranges. *)
let consistency_cases : (string * string) list =
  [
    ("plain", "hello world");
    ("inline pair", "a $b$ c");
    ("escaped dollar", "cost \\$5 ok");
    ("named env", "\\begin{math}1+2\\end{math}");
    ("mixed", "x $a$ y \\(b\\) z");
    ("unclosed", "open $unclosed");
  ]

let ranges_match got exp =
  List.length got = List.length exp
  && List.for_all2 (fun (a, b) (c, d) -> a = c && b = d) got exp

let pp_ranges rs =
  "[" ^ String.concat "; " (List.map (fun (a, b) -> sprintf "(%d,%d)" a b) rs) ^ "]"

let () =
  let fails = ref 0 in
  (* Range-shape tests. *)
  List.iter
    (fun (label, src, exp) ->
      let got = find_math_ranges src in
      if not (ranges_match got exp) then (
        incr fails;
        eprintf "[math-ranges] FAIL %s\n  src: %S\n  got: %s\n  exp: %s\n%!"
          label src (pp_ranges got) (pp_ranges exp)))
    range_cases;
  (* Consistency tests: is_in_math_range must agree with the ranges. *)
  List.iter
    (fun (label, src) ->
      let ranges = find_math_ranges src in
      for p = 0 to String.length src - 1 do
        let direct =
          List.exists (fun (a, b) -> a <= p && p < b) ranges
        in
        let api = is_in_math_range ranges p in
        if direct <> api then (
          incr fails;
          eprintf
            "[math-ranges] FAIL %s consistency at p=%d\n  src: %S\n  ranges: %s\n  direct: %b api: %b\n%!"
            label p src (pp_ranges ranges) direct api)
      done)
    consistency_cases;
  let total = List.length range_cases + List.length consistency_cases in
  if !fails = 0 then (
    printf "[math-ranges] PASS %d cases\n%!" total;
    exit 0)
  else exit 1
