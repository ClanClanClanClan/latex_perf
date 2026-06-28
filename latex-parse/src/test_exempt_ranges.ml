(** Unit tests for the context-exemption scanner (P3 token-aware variants):
    [Validators_common.find_exempt_ranges] / [is_in_exempt_range].

    The scanner identifies byte ranges where typography/lexical rules must NOT
    fire — verbatim spans, line comments, url targets, and math. These tests pin
    each context, the math-masking correctness (a `$` inside a comment/verbatim
    is literal, not a math toggle), and boundary behaviour. *)

open Latex_parse_lib.Validators_common
open Test_helpers

(* Byte offset of the first occurrence of [sub] in [s] (or -1). *)
let find_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i =
    if i + m > n then -1 else if String.sub s i m = sub then i else go (i + 1)
  in
  go 0

(* Is the first occurrence of [sub] inside an exempt range? *)
let exempt s sub =
  let i = find_sub s sub in
  if i < 0 then failwith ("test bug: substring not found: " ^ sub)
  else is_in_exempt_range (find_exempt_ranges s) i

let () =
  (* ── Comments ──────────────────────────────────────────────────────── *)
  run "comment body is exempt" (fun tag ->
      expect (exempt "ok % a -- b dash\nmore" "-- b") (tag ^ ": -- in comment"));
  run "text before a comment is NOT exempt" (fun tag ->
      expect
        (not (exempt "real -- text % c\n" "-- text"))
        (tag ^ ": prose dash before % stays live"));
  run "escaped percent is not a comment" (fun tag ->
      expect
        (not (exempt "cost 50\\% and -- here\n" "-- here"))
        (tag ^ ": \\% does not open a comment"));

  (* ── Inline verbatim ───────────────────────────────────────────────── *)
  run "\\verb|..| body is exempt" (fun tag ->
      expect (exempt "x \\verb|a -- b| y" "-- b") (tag ^ ": -- inside \\verb"));
  run "\\verb*|..| body is exempt" (fun tag ->
      expect (exempt "x \\verb*|a -- b| y" "-- b") (tag ^ ": -- inside \\verb*"));
  run "\\lstinline|..| body is exempt" (fun tag ->
      expect
        (exempt "x \\lstinline|a -- b| y" "-- b")
        (tag ^ ": -- inside \\lstinline"));
  run "\\verbatim-like command is NOT misparsed as \\verb" (fun tag ->
      (* \verbatiminput{f} — letter after \verb means it is not inline \verb;
         the `--` in following prose must stay live. *)
      expect
        (not (exempt "\\verbatiminput{f} then -- here" "-- here"))
        (tag ^ ": letter-delimiter guard"));
  run "text after \\verb|..| is live again" (fun tag ->
      expect
        (not (exempt "\\verb|code| then -- prose" "-- prose"))
        (tag ^ ": dash after the closing delimiter fires"));

  (* ── Verbatim environments ─────────────────────────────────────────── *)
  run "verbatim environment body is exempt" (fun tag ->
      expect
        (exempt "\\begin{verbatim}\na -- b\n\\end{verbatim}" "-- b")
        (tag ^ ": -- inside verbatim env"));
  run "lstlisting environment body is exempt" (fun tag ->
      expect
        (exempt "\\begin{lstlisting}\nx -- y\n\\end{lstlisting}" "-- y")
        (tag ^ ": -- inside lstlisting"));
  run "non-verbatim environment body is NOT exempt" (fun tag ->
      expect
        (not (exempt "\\begin{itemize}\n\\item -- z\n\\end{itemize}" "-- z"))
        (tag ^ ": itemize is ordinary prose"));

  (* ── Math (composition) ────────────────────────────────────────────── *)
  run "$..$ inline math is exempt" (fun tag ->
      expect (exempt "t $a -- b$ u" "-- b") (tag ^ ": -- in $..$"));
  run "\\(..\\) inline math is exempt" (fun tag ->
      expect (exempt "t \\(a -- b\\) u" "-- b") (tag ^ ": -- in \\(..\\)"));
  run "\\[..\\] display math is exempt" (fun tag ->
      expect (exempt "t \\[a -- b\\] u" "-- b") (tag ^ ": -- in \\[..\\]"));
  run "equation environment is exempt" (fun tag ->
      expect
        (exempt "\\begin{equation}\na -- b\n\\end{equation}" "-- b")
        (tag ^ ": -- in equation env"));
  (* v27.1.1: amsmath alignat/flalign and IEEEtrantools IEEEeqnarray are
     top-level display-math environments; their content must be exempt (an
     adversarial review found TYPO-002/003/004 were corrupting math inside
     them). *)
  run "alignat environment is exempt" (fun tag ->
      expect
        (exempt "\\begin{alignat}{1}\na -- b\n\\end{alignat}" "-- b")
        (tag ^ ": -- in alignat env"));
  run "flalign* environment is exempt" (fun tag ->
      expect
        (exempt "\\begin{flalign*}\na -- b\n\\end{flalign*}" "-- b")
        (tag ^ ": -- in flalign* env"));
  run "IEEEeqnarray environment is exempt" (fun tag ->
      expect
        (exempt "\\begin{IEEEeqnarray}{l}\na -- b\n\\end{IEEEeqnarray}" "-- b")
        (tag ^ ": -- in IEEEeqnarray env"));

  (* ── Math masking: a $ in a comment/verbatim must not toggle math ──── *)
  run "stray $ in a comment does not desync later math" (fun tag ->
      (* The `$` in the comment must NOT open math; the prose `-- here` after
         the comment line must therefore stay LIVE (not swallowed by phantom
         math). *)
      let s = "% price is $5 today\nreal -- here and $x$ end" in
      expect (not (exempt s "-- here")) (tag ^ ": comment $ neutralised"));
  run "real math after a comment-$ still detected" (fun tag ->
      let s = "% $ stray\nkeep $a -- b$ exempt" in
      expect (exempt s "-- b") (tag ^ ": $a -- b$ still math"));
  run "$ inside verbatim is literal, not math" (fun tag ->
      expect
        (not (exempt "\\verb|$| then -- prose" "-- prose"))
        (tag ^ ": verbatim $ does not open math"));

  (* ── URLs ──────────────────────────────────────────────────────────── *)
  run "\\url{..} target is exempt" (fun tag ->
      expect
        (exempt "see \\url{http://a--b.com} now" "--b")
        (tag ^ ": -- inside \\url"));
  run "\\href first arg exempt, link text live" (fun tag ->
      let s = "\\href{http://a--b.com}{the -- text}" in
      expect (exempt s "--b") (tag ^ ": url arg exempt");
      expect (not (exempt s "-- text")) (tag ^ ": link text is prose"));

  (* ── Plain text + boundaries ───────────────────────────────────────── *)
  run "plain prose is never exempt" (fun tag ->
      expect (not (exempt "just a -- dash here" "-- dash")) (tag ^ ": live"));
  run "empty string yields no ranges" (fun tag ->
      expect (find_exempt_ranges "" = []) (tag ^ ": no ranges"));

  (* ── Per-document memoisation contract ─────────────────────────────────
     [find_exempt_ranges] / [find_verbatim_comment_url_ranges] are memoised with
     a 1-entry physical-equality cache. Verify it is transparent: the cache-HIT
     path (same string object twice) returns the same result, and interleaving
     DISTINCT documents never returns a stale result from the other one. *)
  run "cache hit: same object returns identical ranges" (fun tag ->
      let a = "x \\verb|a -- b| y % c -- d\n$e -- f$" in
      expect
        (find_exempt_ranges a = find_exempt_ranges a)
        (tag ^ ": idempotent on the same object"));
  run "cache miss: interleaved distinct docs are not stale" (fun tag ->
      let a = "\\verb|--|" and b = "plain -- prose" in
      let ra1 = find_exempt_ranges a in
      let rb = find_exempt_ranges b in
      let ra2 = find_exempt_ranges a in
      (* b has no exempt ranges; a does. If the cache leaked, rb would equal ra1
         or ra2 would be stale. *)
      expect
        (rb = [] && ra1 = ra2 && ra1 <> [])
        (tag ^ ": distinct docs computed independently"));

  finalise "exempt-ranges"
