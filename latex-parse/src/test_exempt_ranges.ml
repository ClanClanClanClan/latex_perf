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
  (* ── \lstinline's OPTIONAL argument, and blanks before the delimiter ──

     The scanner used to read the byte at a FIXED offset past the command name
     as the delimiter. Three measured defects followed, and all three are pinned
     below because each fails in a different direction. *)
  run "\\lstinline[opt] body is exempt" (fun tag ->
      expect
        (exempt "x \\lstinline[language=C]|a -- b| y" "-- b")
        (tag ^ ": the optional argument must be consumed before the delimiter"));

  run "prose AFTER \\lstinline[opt] stays live" (fun tag ->
      (* The over-reach case. With '[' taken as the delimiter and no later '[',
         the range ran to END OF FILE and silently withheld every fix in the
         rest of the document. Measured: a dash before the command was fixed and
         an identical dash after it was not. *)
      expect
        (not (exempt "\\lstinline[language=C]|code| then -- here" "-- here"))
        (tag ^ ": the range must END at the closing delimiter, not at EOF"));

  run "a bracket inside the option VALUE does not end the range early"
    (fun tag ->
      (* The corruption case: the range ended at the ']' inside {[x]}, leaving
         the verbatim body exposed, and the fixer rewrote a--b to an en dash. *)
      expect
        (exempt "\\lstinline[caption={[x]}]|a -- b|" "-- b")
        (tag ^ ": close only at an UNESCAPED ] at brace depth 0"));

  (* ── '[' is a legal \verb DELIMITER, not an optional argument ─────────

     Consuming a bracket group for \verb (which has no optional argument) walked
     past the real closing delimiter onto a letter and recorded NO RANGE, so the
     fixer rewrote the verbatim body. Both halves are pinned: the body must be
     exempt, and the prose after it must stay live. *)
  run "\\verb[..[ body is exempt" (fun tag ->
      expect
        (exempt "Code: \\verb[a -- b[ end, bracket ] here." "-- b")
        (tag ^ ": '[' is a \\verb delimiter; the body must not be rewritten"));

  run "prose after \\verb[..[ stays live" (fun tag ->
      expect
        (not (exempt "\\verb[ab[ tail ] then -- here" "-- here"))
        (tag ^ ": the \\verb range ends at the closing '['"));

  (* ── \lstinline{..} is a BRACE GROUP, not a '{' delimiter ───────────── *)
  run "\\lstinline{..} body is exempt" (fun tag ->
      expect
        (exempt "x \\lstinline{a -- b} y" "-- b")
        (tag ^ ": -- inside \\lstinline{}"));

  run "prose after \\lstinline{..} stays live" (fun tag ->
      (* The over-reach: '{' taken as a delimiter ran the range to the NEXT '{'
         — the brace of \textbf — withholding every fix in between. *)
      expect
        (not
           (exempt "\\lstinline{a b} then -- one, then \\textbf{bold}" "-- one"))
        (tag ^ ": the range must end at the matching '}', not the next '{'"));

  run "\\lstinline[opt]{..} consumes both the option and the group" (fun tag ->
      expect
        (exempt "\\lstinline[language=C]{a -- b} tail" "-- b")
        (tag ^ ": optional argument then brace group"));

  run "a space before the delimiter is absorbed" (fun tag ->
      (* TeX ends a control word at the first non-letter and absorbs following
         spaces, so `X \verb |ab| Y` is legal and its delimiter is '|'. The
         scanner took the SPACE. Verified: that document compiles, rc 0. *)
      expect
        (exempt "X \\verb |a -- b| Y" "-- b")
        (tag ^ ": the delimiter follows the blanks"));

  run "prose after a space-delimited \\verb stays live" (fun tag ->
      expect
        (not (exempt "X \\verb |ab| Y then -- here" "-- here"))
        (tag ^ ": the range must not swallow the remainder"));

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

  (* ── OPEN-007: the comment-aware feature view (2026-09-01) ──────────────
     [find_comment_ranges] is a first-byte PROJECTION of the vcu set;
     [blank_line_comments] blanks exactly those ranges; the fail-closed
     [comment_semantics_breaker] suppresses blanking whenever a construct
     changes what `%` means. Every shape below mirrors one of the committed
     fr_cmt_* breaker fixtures. *)
  run "find_comment_ranges: comments only, never verbatim/url" (fun tag ->
      let s = "a % c\n\\begin{verbatim}\n%v\n\\end{verbatim}\n\\url{x%y}\n" in
      let cr = find_comment_ranges s in
      let vcu = find_verbatim_comment_url_ranges s in
      expect
        (List.length cr = 1
        && List.length vcu = 3
        && List.for_all (fun r -> List.mem r vcu) cr
        && fst (List.hd cr) = 2)
        (tag ^ ": exactly the % range survives the projection"));
  run "blank_line_comments: length-preserving, EOL kept" (fun tag ->
      let s = "\\usepackage{a,% x\nfontspec}\n" in
      let b = blank_line_comments s in
      expect
        (String.length b = String.length s
        && b = "\\usepackage{a,   \nfontspec}\n")
        (tag ^ ": % and comment bytes to spaces, newline untouched"));
  run "blank_line_comments: CR-only comment terminator kept" (fun tag ->
      let s = "x % c\ry" in
      expect (blank_line_comments s = "x    \ry") (tag ^ ": CR preserved"));
  run "blank_line_comments: verbatim % is NOT blanked (g1 liveness)" (fun tag ->
      let s = "\\begin{verbatim}\n% live\n\\end{verbatim}\n" in
      expect
        (blank_line_comments s == s)
        (tag ^ ": physical identity, zero bytes blanked"));
  run "space-form env OPEN is verbatim; spaced END does NOT close (OPEN-038/M2)"
    (fun tag ->
      (* TeX asymmetry, both measured: `\begin {verbatim}` opens the env
         (sibling compiles rc 0,0) but `\end {verbatim}` does NOT terminate it
         (\@xverbatim wants the LITERAL `\end{verbatim}` bytes: "File ended
         while scanning"). So this doc's range runs to EOF and NO byte in it is
         ever a comment — blanking anything here would expose live verbatim
         bytes. *)
      let s = "\\begin {verbatim}\n% live\n\\end {verbatim}\nz % x\n" in
      let cr = find_comment_ranges s in
      match find_verbatim_comment_url_ranges s with
      | [ (0, e) ] ->
          expect
            (e = String.length s && cr = [])
            (tag ^ ": one range to EOF, zero comment ranges")
      | _ -> expect false (tag ^ ": single EOF-bounded range expected"));
  run "single-newline \\begin form IS verbatim; blank line is NOT" (fun tag ->
      (* measured: \begin+one newline+{verbatim} compiles AND is verbatim; a
         BLANK line in between is "Paragraph ended before \begin was complete" —
         fatal, and the scanner must NOT recognise it. *)
      let one = "\\begin\n{verbatim}\n% live\n\\end{verbatim}\n" in
      let two = "\\begin\n\n{verbatim}\n% x\n" in
      expect
        (find_comment_ranges one = []
        && List.length (find_comment_ranges two) = 1)
        (tag ^ ": one EOL absorbed, a blank line never"));
  run "tcblisting body is verbatim to the scanner" (fun tag ->
      let s = "\\begin{tcblisting}{}\n% live\n\\end{tcblisting}\n" in
      expect (find_comment_ranges s = []) (tag ^ ": its % is never blanked"));
  run "space-form open with exact close still bounded" (fun tag ->
      let s = "\\begin {verbatim}x\\end{verbatim}tail" in
      match find_verbatim_comment_url_ranges s with
      | [ (0, e) ] -> expect (e = String.length s - 4) (tag ^ ": stops at close")
      | _ -> expect false (tag ^ ": one bounded range expected"));
  run "space-form NON-verbatim env is not swallowed" (fun tag ->
      let s = "\\begin {itemize} % c\n\\end {itemize}" in
      expect
        (List.length (find_comment_ranges s) = 1)
        (tag ^ ": itemize stays prose; its % is a real comment"));
  run "\\beginner is not an env open" (fun tag ->
      let s = "\\beginner{verbatim} % c\n" in
      expect
        (List.length (find_comment_ranges s) = 1)
        (tag ^ ": longer control word"));
  run "breaker: custom verbatim env definitions (m1)" (fun tag ->
      expect
        (comment_semantics_breaker "\\lstnewenvironment{code}{}{}"
        && comment_semantics_breaker
             "\\DefineVerbatimEnvironment{c}{Verbatim}{}"
        && comment_semantics_breaker "\\newtcblisting{c}{}"
        && comment_semantics_breaker "\\newminted{py}{}"
        && comment_semantics_breaker
             "\\newenvironment{c}{\\verbatim}{\\endverbatim}")
        (tag ^ ": every definition form suppresses blanking"));
  run "breaker: letter-delimited \\verb (m3), both spellings" (fun tag ->
      expect
        (comment_semantics_breaker "x \\verb aQ%Ya z"
        && comment_semantics_breaker "x \\verb*aQ%Ya z")
        (tag ^ ": spaced and starred letter delimiters"));
  run "breaker: %-catcode surgery (m4/m4b) and short verb" (fun tag ->
      expect
        (comment_semantics_breaker "\\catcode`\\%=12"
        && comment_semantics_breaker "\\catcode37=14"
        && comment_semantics_breaker "\\MakePercentIgnore"
        && comment_semantics_breaker "\\MakeShortVerb{\\|}"
        && comment_semantics_breaker "\\DefineShortVerb{\\|}")
        (tag ^ ": every %-semantics change suppresses blanking"));
  run "breaker: fail-closed on COMMENTED-OUT breakers too" (fun tag ->
      expect
        (comment_semantics_breaker "% \\MakePercentIgnore\n")
        (tag ^ ": raw-substring scan, no comment stripping — by design"));
  run "breaker: fancyvrb/verbdef/xparse/makeother arms (pre-ship review)"
    (fun tag ->
      expect
        (comment_semantics_breaker "\\Verb!a%b!"
        && comment_semantics_breaker "\\SaveVerb{x}|a%b|"
        && comment_semantics_breaker "\\verbdef\\snip|a%b|"
        && comment_semantics_breaker
             "\\makeatletter\\@makeother\\%\\makeatother"
        && comment_semantics_breaker
             "\\NewDocumentCommand\\foo{v}{\\texttt{#1}}"
        && comment_semantics_breaker "\\DeclareDocumentCommand{\\bar}{O{} v}{x}"
        )
        (tag ^ ": every measured manufacture vector suppresses blanking"));
  run "no breaker: \\Verbatim env, plain xparse, \\@makeother non-%" (fun tag ->
      expect
        ((not
            (comment_semantics_breaker "\\begin{Verbatim}\nx\n\\end{Verbatim}"))
        && (not (comment_semantics_breaker "\\VerbatimInput{f.tex}"))
        && (not (comment_semantics_breaker "\\NewDocumentCommand\\a{m o}{x}"))
        && not (comment_semantics_breaker "\\@makeother\\_"))
        (tag ^ ": longer control words and %-free surgery stay open"));
  run "no breaker: catcode/makeother windows stop at end-of-line" (fun tag ->
      (* measured false-fire (asme2e.cls): a COMMENT on the line after a non-%
         catcode assignment fell inside the lookahead and cost a real rescue in
         the 199-sweep. *)
      expect
        ((not (comment_semantics_breaker "\\catcode`\\:12\n%   Header\n"))
        && (not (comment_semantics_breaker "\\@makeother\\_\n% c\n"))
        && comment_semantics_breaker "\\catcode`\\%=12\n")
        (tag ^ ": next-line comments never poison the window"));
  run "no breaker: ordinary verbatim/verb/catcode-@ docs" (fun tag ->
      expect
        ((not (comment_semantics_breaker "\\begin{verbatim}x\\end{verbatim}"))
        && (not (comment_semantics_breaker "\\verb|a%b| and \\verb*|c|"))
        && (not (comment_semantics_breaker "\\verbatiminput{f.txt}"))
        && (not
              (comment_semantics_breaker
                 (* moreverb/fancyvrb control words: a letter DIRECTLY after
                    \\verb is a longer control word, never a delimiter — the
                    measured frame footprint of a naive arm is 16/16 papers of
                    exactly these three names, all false-fires. *)
                 "\\verbatimwrite{f} \\verbatimindent \\verbatimfont{\\tt}"))
        && (not (comment_semantics_breaker "\\catcode`\\@=11"))
        && not (comment_semantics_breaker "plain % comment\n"))
        (tag ^ ": the gate stays open for the 34-rescue channel"));

  run "multi verdict: UNUSED custom-verb definition is NOT a breaker"
    (fun tag ->
      (* 2507.08906v1's shape: \\newtcblisting defined in a child, used nowhere
         — no verbatim body exists, blanking cannot corrupt. *)
      expect
        ((not
            (comment_blanking_breakers
               [ "x % c\n"; "\\newtcblisting{namedlisting}{}\n" ]))
        && (not
              (comment_blanking_breakers
                 [ "\\lstnewenvironment{code}{}{} only defined\n" ]))
        && comment_blanking_breakers
             [
               "\\lstnewenvironment{code}{}{}\n\\begin{code}\nx\n\\end{code}\n";
             ]
        && comment_blanking_breakers
             (* defined in one source, USED in another *)
             [
               "\\begin{code}\nx\n\\end{code}\n";
               "\\lstnewenvironment{code}{}{}\n";
             ]
        && comment_blanking_breakers
             [ "\\begin {code}\nx"; "\\newtcblisting{code}{}" ])
        (tag ^ ": liveness decides; space-form usage counts"));
  run "multi verdict: non-definition breakers stay unconditional" (fun tag ->
      expect
        (comment_blanking_breakers [ "ok\n"; "\\catcode`\\%=9\n" ]
        && comment_blanking_breakers [ "\\newminted{py}{}\n" ]
        && comment_blanking_breakers [ "\\newtcblisting\n" ] (* malformed *)
        && not (comment_blanking_breakers [ "plain % doc\n" ]))
        (tag ^ ": catcode/newminted/malformed always suppress"));

  finalise "exempt-ranges"
