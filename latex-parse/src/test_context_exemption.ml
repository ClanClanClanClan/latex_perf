(** Context-exemption regression gate (P3 token-aware variants).

    Asserts that each retrofitted pilot rule fires on a genuine deviation in
    ordinary prose, but stays SILENT when the same deviation is inside a
    protected region (inline/env verbatim, line comment, or math). This is the
    post-pilot-gate property that makes a Draft rule safe to promote to the
    default set: it enforces the project's typographic standard without
    false-positiving on code listings, comments, or math.

    Add a row to [cases] as each rule is made context-aware; the rule's needle
    must appear verbatim in each [plain]/[ctx] string. *)

open Test_helpers

(* (rule id, prose input that MUST fire, [(context label, input that MUST be
   silent)]). Each exempt input embeds the same deviation inside a protected
   region. *)
let cases =
  [
    ( "TYPO-002",
      "ordinary text a -- b here",
      [
        ("inline verbatim", "x \\verb|a -- b| y");
        ("verbatim env", "\\begin{verbatim}\na -- b\n\\end{verbatim}");
        ("line comment", "% a -- b comment\n");
        ("inline math", "$a -- b$");
      ] );
    ( "TYPO-003",
      "ordinary text a --- b here",
      [
        ("inline verbatim", "x \\verb|a --- b| y");
        ("verbatim env", "\\begin{verbatim}\na --- b\n\\end{verbatim}");
        ("line comment", "% a --- b comment\n");
        ("inline math", "$a --- b$");
      ] );
    ( "TYPO-004",
      "they said ``hello'' loudly",
      [
        ("inline verbatim", "x \\verb|``hello''| y");
        ("verbatim env", "\\begin{verbatim}\n``hello''\n\\end{verbatim}");
        ("line comment", "% ``hello'' comment\n");
        ("inline math", "$``hello''$");
      ] );
    ( "TYPO-005",
      "wait ... and see",
      [
        ("inline verbatim", "x \\verb|...| y");
        ("verbatim env", "\\begin{verbatim}\na ... b\n\\end{verbatim}");
        ("line comment", "% wait ... comment\n");
        ("inline math", "$a + ... + z$");
      ] );
    ( "TYPO-010",
      "apples , oranges here",
      [
        ("inline verbatim", "x \\verb|a , b| y");
        ("verbatim env", "\\begin{verbatim}\na , b\n\\end{verbatim}");
        ("line comment", "% a , b comment\n");
        ("inline math", "$a , b$");
      ] );
    ( "TYPO-033",
      "see Smith et.al here",
      [
        ("inline verbatim", "x \\verb|et.al| y");
        ("verbatim env", "\\begin{verbatim}\net.al\n\\end{verbatim}");
        ("line comment", "% et.al comment\n");
        ("inline math", "$et.al$");
      ] );
    ( "TYPO-037",
      "apples , oranges here",
      [
        ("inline verbatim", "x \\verb|a , b| y");
        ("verbatim env", "\\begin{verbatim}\na , b\n\\end{verbatim}");
        ("line comment", "% a , b comment\n");
        ("inline math", "$a , b$");
      ] );
    ( "TYPO-001",
      "she said \"hi\" then",
      [
        ("inline verbatim", "x \\verb|\"hi\"| y");
        ("verbatim env", "\\begin{verbatim}\n\"hi\"\n\\end{verbatim}");
        ("line comment", "% \"hi\" comment\n");
        ("inline math", "$\"x\" + \"y\"$");
      ] );
    ( "TYPO-013",
      "the `key word here",
      [
        ("inline verbatim", "x \\verb|`code| y");
        ("verbatim env", "\\begin{verbatim}\n`tick\n\\end{verbatim}");
        ("line comment", "% `tick comment\n");
        ("inline math", "$`x$");
      ] );
    ( "TYPO-015",
      "stray \\%\\% here",
      [
        ("inline verbatim", "x \\verb|\\%\\%| y");
        ("verbatim env", "\\begin{verbatim}\n\\%\\%\n\\end{verbatim}");
        ("line comment", "% \\%\\% comment\n");
        ("inline math", "$\\%\\%$");
      ] );
    ( "TYPO-022",
      "the end )",
      [
        ("inline verbatim", "x \\verb|a )| y");
        ("verbatim env", "\\begin{verbatim}\na )\n\\end{verbatim}");
        ("line comment", "% a ) comment\n");
        ("inline math", "$a )$");
      ] );
    ( "TYPO-027",
      "wow!! really",
      [
        ("inline verbatim", "x \\verb|!!| y");
        ("verbatim env", "\\begin{verbatim}\nwow!!\n\\end{verbatim}");
        ("line comment", "% wow!! comment\n");
        ("inline math", "$n!!$");
      ] );
    ( "TYPO-017",
      "caf\\'{e} menu",
      [
        ("inline verbatim", "x \\verb|\\'{e}| y");
        ("verbatim env", "\\begin{verbatim}\n\\'{e}\n\\end{verbatim}");
        ("line comment", "% \\'{e} comment\n");
        ("inline math", "math $\\'{e}$ here");
      ] );
    ( "TYPO-032",
      "see ,\\cite here",
      [
        ("inline verbatim", "x \\verb|,\\cite| y");
        ("verbatim env", "\\begin{verbatim}\n,\\cite\n\\end{verbatim}");
        ("line comment", "% ,\\cite comment\n");
        ("inline math", "$,\\cite$");
      ] );
    ( "TYPO-042",
      "what?? now",
      [
        ("inline verbatim", "x \\verb|??| y");
        ("verbatim env", "\\begin{verbatim}\nwhat??\n\\end{verbatim}");
        ("line comment", "% what?? comment\n");
        ("inline math", "$a ?? b$");
      ] );
    ( "TYPO-057",
      "heat 45\xc2\xb0C now",
      [
        ("inline verbatim", "x \\verb|45\xc2\xb0| y");
        ("verbatim env", "\\begin{verbatim}\n45\xc2\xb0\n\\end{verbatim}");
        ("line comment", "% 45\xc2\xb0 comment\n");
        ("inline math", "$45\xc2\xb0$");
      ] );
    ( "TYPO-061",
      "width 3 \xc3\x97 4 cm",
      [
        ("inline verbatim", "x \\verb|\xc3\x97| y");
        ("verbatim env", "\\begin{verbatim}\n\xc3\x97\n\\end{verbatim}");
        ("line comment", "% \xc3\x97 comment\n");
        ("inline math", "$a \xc3\x97 b$");
      ] );
    ( "TYPO-034",
      "word \\footnote{x} here",
      [
        ("inline verbatim", "x \\verb| \\footnote| y");
        ("verbatim env", "\\begin{verbatim}\na \\footnote\n\\end{verbatim}");
        ("line comment", "% a \\footnote b\n");
        ("inline math", "$a \\footnote b$");
      ] );
    ( "TYPO-038",
      "mail a@b.com today",
      [
        ("inline verbatim", "x \\verb|a@b.com| y");
        ("verbatim env", "\\begin{verbatim}\na@b.com\n\\end{verbatim}");
        ("line comment", "% a@b.com comment\n");
        ("inline math", "$a@b.com$");
      ] );
    ( "TYPO-049",
      "\xe2\x80\x9c word",
      [
        ("inline verbatim", "x \\verb|\xe2\x80\x9c | y");
        ("verbatim env", "\\begin{verbatim}\n\xe2\x80\x9c x\n\\end{verbatim}");
        ("line comment", "% \xe2\x80\x9c x\n");
        ("inline math", "$\xe2\x80\x9c x$");
      ] );
    ( "TYPO-051",
      "word\xe2\x80\x89spacing",
      [
        ("inline verbatim", "x \\verb|\xe2\x80\x89| y");
        ("verbatim env", "\\begin{verbatim}\nx\xe2\x80\x89y\n\\end{verbatim}");
        ("line comment", "% x\xe2\x80\x89y\n");
        ("inline math", "$x\xe2\x80\x89y$");
      ] );
    ( "TYPO-053",
      "a \xe2\x8b\xaf z",
      [
        ("inline verbatim", "x \\verb|\xe2\x8b\xaf| y");
        ("verbatim env", "\\begin{verbatim}\na \xe2\x8b\xaf z\n\\end{verbatim}");
        ("line comment", "% \xe2\x8b\xaf z\n");
        ("inline math", "$a \xe2\x8b\xaf z$");
      ] );
    (* TYPO-009 fires only on a `~` at the START of a line, which can only sit
       inside a protected region in a multi-line environment (verbatim env or
       display math) — inline verbatim / line comment cannot host a line-start
       `~`, so this rule uses a custom 2-context list. *)
    ( "TYPO-009",
      "~text at line start",
      [
        ("verbatim env", "\\begin{verbatim}\n~code line\n\\end{verbatim}");
        ("display math", "\\[\n~x = 1\n\\]");
      ] );
    ( "TYPO-016",
      "see \\cite{x} here",
      [
        ("inline verbatim", "x \\verb| \\cite{a}| y");
        ("verbatim env", "\\begin{verbatim}\n \\cite{a}\n\\end{verbatim}");
        ("line comment", "% see \\cite{a} here\n");
        ("inline math", "$a \\cite{x} b$");
      ] );
    ( "TYPO-018",
      "a  b here",
      [
        ("inline verbatim", "x \\verb|a  b| y");
        ("verbatim env", "\\begin{verbatim}\na  b\n\\end{verbatim}");
        ("line comment", "% a  b comment\n");
        ("inline math", "$a  b$");
      ] );
    ( "TYPO-021",
      "wait...And then",
      [
        ("inline verbatim", "x \\verb|...A| y");
        ("verbatim env", "\\begin{verbatim}\n...A\n\\end{verbatim}");
        ("line comment", "% ...A comment\n");
        ("inline math", "$...A$");
      ] );
    ( "TYPO-055",
      "a\\,\\,b here",
      [
        ("inline verbatim", "x \\verb|\\,\\,| y");
        ("verbatim env", "\\begin{verbatim}\n\\,\\,\n\\end{verbatim}");
        ("line comment", "% \\,\\, comment\n");
        ("inline math", "$\\,\\,$");
      ] );
    (* TYPO-012/028/046 are the "vcu-only" rules: math is their OPERATING domain
       (TYPO-012 fixes `5'`→`5^\prime` inside math; TYPO-028/046 rewrite the
       `$$` / `\begin{math}` delimiters themselves), so they must NOT be exempt
       in math — only in verbatim / comments / url. Hence a custom 3-context
       list with no inline-math row. *)
    ( "TYPO-012",
      "the 6' board",
      [
        ("inline verbatim", "x \\verb|6'| y");
        ("verbatim env", "\\begin{verbatim}\n6'\n\\end{verbatim}");
        ("line comment", "% 6' here\n");
      ] );
    ( "TYPO-028",
      "display $$x$$ here",
      [
        ("inline verbatim", "x \\verb|$$x$$| y");
        ("verbatim env", "\\begin{verbatim}\n$$x$$\n\\end{verbatim}");
        ("line comment", "% $$x$$ here\n");
      ] );
    ( "TYPO-046",
      "math \\begin{math}x\\end{math} here",
      [
        ("inline verbatim", "x \\verb|\\begin{math}| y");
        ( "verbatim env",
          "\\begin{verbatim}\n\\begin{math}x\\end{math}\n\\end{verbatim}" );
        ("line comment", "% \\begin{math}x\\end{math}\n");
      ] );
  ]

let () =
  (* Pilot rules are gated behind L0_VALIDATORS; enable for this suite. *)
  Unix.putenv "L0_VALIDATORS" "pilot";
  List.iter
    (fun (id, plain, exempt_cases) ->
      run (Printf.sprintf "%s fires on a prose deviation" id) (fun tag ->
          expect (fires id plain) (tag ^ ": " ^ id ^ " should fire on prose"));
      List.iter
        (fun (ctx, src) ->
          run (Printf.sprintf "%s is exempt inside %s" id ctx) (fun tag ->
              expect (does_not_fire id src)
                (tag ^ ": " ^ id ^ " must not fire inside " ^ ctx)))
        exempt_cases)
    cases;
  Unix.putenv "L0_VALIDATORS" "";
  finalise "context-exemption"
