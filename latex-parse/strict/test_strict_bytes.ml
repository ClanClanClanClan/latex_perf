(* Unit tests of the EXTRACTED decision on bytes (proofs/Strict/DecideBytes.v),
   on files whose pdflatex outcome was MEASURED under the pinned oracle while
   the reader was built (2026-09-28; the verdict, the first error and its l.N
   are in each comment). The byte-level evidence
   (corpora/strict_s0/bytes_probes.json, bytes_differential.json) is the broad
   check; these tests pin the extracted code to measured behaviour.

   The lexical contract here is a TEST copy of the catcode table
   gen_strict_lexical.py dumped at body start of [article] (committed as
   corpora/contracts/strict/article-s0-lexical.json, which the driver loads):
   the backslash is the escape character; braces group; the dollar sign is math
   shift; the ampersand aligns; byte 13 ends a line; the hash sign is the
   parameter character; caret and underscore are the scripts; space and tab are
   spacers; A-Z and a-z are letters; the percent sign starts a comment; bytes 0
   and 127 are invalid; the tilde and bytes 1-8, 11, 12, 14-31 and 128-255 are
   active; every other byte is other. The kernel contract is phase 1's test
   contract (three names). *)

module B = Strict_bytes_extracted

let chars s = List.init (String.length s) (String.get s)

let str l =
  let b = Buffer.create 16 in
  List.iter (Buffer.add_char b) l;
  Buffer.contents b

let cat c =
  match c with
  | '\\' -> B.CEscape
  | '{' -> B.CBgroup
  | '}' -> B.CEgroup
  | '$' -> B.CMath
  | '&' -> B.CAlign
  | '\r' -> B.CEol
  | '#' -> B.CParam
  | '^' -> B.CSup
  | '_' -> B.CSub
  | ' ' | '\t' -> B.CSpacer
  | 'a' .. 'z' | 'A' .. 'Z' -> B.CLetter
  | '%' -> B.CComment
  | '\000' | '\127' -> B.CInvalid
  | '~' -> B.CActive
  | c when Char.code c >= 128 -> B.CActive
  | c when Char.code c < 32 && c <> '\n' -> B.CActive
  | _ -> B.COther

let lexcon =
  {
    B.lx_cat = cat;
    B.lx_endline = Some '\r';
    B.lx_par = chars "par";
    B.lx_end = chars "end";
    B.lx_begin = chars "begin";
    B.lx_docclass = chars "documentclass";
    B.lx_class = chars "article";
    B.lx_docenv = chars "document";
    B.lx_mopen_inline = '(';
    B.lx_mclose_inline = ')';
    B.lx_mopen_display = '[';
    B.lx_mclose_display = ']';
  }

let kernel =
  let sigs =
    [
      ("alpha", { B.sig_text = B.TxFatal B.E3; B.sig_math = B.MxNoad });
      ("LaTeX", { B.sig_text = B.TxMaterial; B.sig_math = B.MxFatal B.E3 });
      ("relax", { B.sig_text = B.TxNoop; B.sig_math = B.MxNoop });
    ]
  in
  {
    B.c_defined =
      (fun n ->
        List.mem_assoc (str n) sigs
        || List.mem (str n) [ "end"; "par"; "begin"; "documentclass" ]);
    B.c_sig = (fun n -> List.assoc_opt (str n) sigs);
  }

let contract = { B.bc_kernel = kernel; B.bc_lex = lexcon }

let show = function
  | B.ProvenReady -> "ready"
  | B.NotStrict -> "not_strict"
  | B.ProvenNotReady (r, l) ->
      let r =
        match r with
        | B.E0 -> "E0"
        | B.E1 -> "E1"
        | B.E3 -> "E3"
        | B.E4 -> "E4"
        | B.E5 -> "E5"
        | B.E6 -> "E6"
      in
      Printf.sprintf "%s l.%d" r l

let failures = ref 0

let check name file want =
  let got = show (B.decide_bytes contract (chars file)) in
  if got <> want then (
    incr failures;
    Printf.printf "FAIL %s: want %s, got %s\n" name want got)

let h = "\\documentclass{article}\n\\begin{document}\n"
let e = "\\end{document}"

let () =
  (* nothing after \end{document} is read: rc 0 *)
  check "after end" (h ^ "x\n" ^ e ^ "\\zzundef\n") "ready";
  check "after end, any bytes"
    (h ^ "x\n" ^ e ^ "\n\000\255^^~#\\end{\n")
    "ready";
  (* \end{document} split over lines, in math: "Missing $ inserted." at l.5, the
     line of its closing brace *)
  check "end split" (h ^ "$x\n\\end{docu%\nment}\n") "E5 l.5";
  check "end then line end" (h ^ "$x\n\\end\n{document}\n") "E5 l.5";
  (* a display $ whose follower is on the next line: "Display math should end
     with $$." on the follower's line (C-84 shape, bytes level) *)
  check "display follower next line" (h ^ "$$x$%\n" ^ e ^ "\n") "E5 l.4";
  check "display follower split" (h ^ "$$x$%\n\\end%\n{document}\n") "E5 l.5";
  (* the front matter: blank lines before, a line end after \documentclass *)
  check "leading blank lines"
    ("\n\n  \n\\documentclass{article}\n\\begin{document}\n\\zzundef\n" ^ e)
    "E1 l.6";
  check "documentclass then line end"
    ("\\documentclass\n{article}\\begin{document}\\zzundef\n" ^ e)
    "E1 l.2";
  (* CR ends a line; CR CR is a blank line *)
  check "CR line end" (h ^ "x\r\\zzundef\n" ^ e) "E1 l.4";
  check "CR CR blank line" (h ^ "$x\r\ry$\n" ^ e) "E6 l.4";
  check "CRLF blank line" (h ^ "$x\r\n\r\ny$\n" ^ e) "E6 l.4";
  (* a trailing tab and a leading tab: rc 0 *)
  check "tabs" (h ^ "$x\t\n\ty$\n" ^ e) "ready";
  (* the end-of-line space is the display follower: l.3 *)
  check "display at eof" (h ^ "$$x$\n") "E5 l.3";
  (* no \end{document}: "Emergency stop.", no l.N *)
  check "no end" (h ^ "x") "E5 l.0";
  (* a space, a line end, a comment after ^: skipped by TeX's math scanner *)
  check "script spaces" (h ^ "$x^ \n 2$ $x^%c\n{y}_ 1$\n" ^ e) "ready";
  check "double superscript" (h ^ "$x^2^3$\n" ^ e) "E4 l.3";
  check "par word in math" (h ^ "$x\\par$\n" ^ e) "E6 l.3";
  check "alpha in text" (h ^ "x \\alpha\n" ^ e) "E3 l.3";
  (* outside the fragment *)
  check "active ~" (h ^ "x ~ y\n" ^ e) "not_strict";
  check "^^" (h ^ "$x^^41$\n" ^ e) "not_strict";
  check "ends with $" (h ^ "$$x$%") "not_strict";
  check "blank line after documentclass"
    ("\\documentclass\n\n{article}\\begin{document}x\n" ^ e)
    "not_strict";
  check "end without document" (h ^ "\\end x\n" ^ e) "not_strict";
  check "control space" (h ^ "x\\ y\n" ^ e) "not_strict";
  check "utf-8" (h ^ "caf\xc3\xa9\n" ^ e) "not_strict";
  check "long line" (h ^ String.make 10001 'x' ^ "\n" ^ e) "not_strict";
  (* TeX Live's first-line directive (C-89): %&latex loads the DVI format, rc 0
     and no PDF; a space before it disables it *)
  check "first line %&latex" ("%&latex\n" ^ h ^ "x\n" ^ e) "not_strict";
  check "first line  %&latex" (" %&latex\n" ^ h ^ "x\n" ^ e) "ready";
  check "line at the bound" (h ^ String.make 10000 'x' ^ "\n" ^ e) "ready";
  (* explain: the first offending byte of an outside file *)
  (match B.explain contract (chars (h ^ "x ~ y\n" ^ e)) with
  | Some (off, B.WLexBad B.BadCat) when off = String.length h + 2 -> ()
  | _ ->
      incr failures;
      print_endline "FAIL explain: ~ not reported at its offset");
  (match B.explain contract (chars (h ^ "x\n" ^ e)) with
  | None -> ()
  | Some _ ->
      incr failures;
      print_endline "FAIL explain: a decided file explained as outside");
  if !failures > 0 then exit 1 else print_endline "test_strict_bytes: OK"
