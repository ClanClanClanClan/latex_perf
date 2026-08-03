(** Unit tests for the fix guard ({!Latex_parse_lib.Fix_guard}).

    The guard is a SUBTRACTIVE filter over fix edits: it withholds any edit that
    would rewrite bytes TeX reads as syntax. Its error polarity is inverted from
    the usual one in this repo — an over-wide protected range only withholds a
    fix, while a narrow or misplaced one lets a producer corrupt a document. So
    these cases pin two things per region: that a load-bearing byte IS blocked,
    and that ordinary prose next to it is NOT (the guard must not turn into a
    blanket refusal, which the round-trip and coverage gates would then read as
    a healthy fixer that simply never fixes anything).

    The fixture-level proof lives in corpora/apply_fixes/ and the round-trip
    gate; these are the fast deterministic sentinels for the range algebra
    itself. *)

open Latex_parse_lib
open Test_helpers

(* Byte offset of the first occurrence of [sub] in [s]. *)
let find_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i =
    if i + m > n then failwith ("test bug: substring not found: " ^ sub)
    else if String.sub s i m = sub then i
    else go (i + 1)
  in
  go 0

(* Would a fix from [rule_id] rewriting the first occurrence of [sub] survive
   the guard? [false] = withheld. *)
let survives ?(rule_id = "TYPO-002") src sub =
  let i = find_sub src sub in
  let e =
    Cst_edit.replace ~start_offset:i
      ~end_offset:(i + String.length sub)
      "\xe2\x80\x93"
  in
  Fix_guard.filter ~src ~rule_id [ e ] <> []

(* Would a pure insertion at [at] survive? *)
let insertion_survives ?(rule_id = "PKG-011") src at =
  Fix_guard.filter ~src ~rule_id [ Cst_edit.insert ~at "x" ] <> []

let () =
  (* ── Region 3a: filename arguments ──────────────────────────────────── *)
  run "double hyphen inside an include filename is withheld" (fun tag ->
      expect
        (not (survives "\\input{adv--child}\n" "--"))
        (tag ^ ": the measured adv_input_filename corruption"));

  run "the same double hyphen in prose is still fixed" (fun tag ->
      expect
        (survives "\\input{child}\n\nan em -- dash\n" "-- dash")
        (tag ^ ": the guard must not become a blanket refusal"));

  List.iter
    (fun cmd ->
      run
        ("filename argument of " ^ cmd ^ " is protected")
        (fun tag ->
          expect
            (not (survives ("\\" ^ cmd ^ "{a--b}\n") "--"))
            (tag ^ ": " ^ cmd)))
    [
      "input";
      "include";
      "includegraphics";
      "subfile";
      "bibliography";
      "addbibresource";
      "bibliographystyle";
      "lstinputlisting";
    ];

  run "optional argument is consumed before the braced one" (fun tag ->
      expect
        (not (survives "\\includegraphics[width=2cm]{fig--1}\n" "--"))
        (tag ^ ": the [..] group must not stop the scan"));

  run "starred form is consumed" (fun tag ->
      expect
        (not (survives "\\includegraphics*{fig--1}\n" "--"))
        (tag ^ ": the star must not stop the scan"));

  run "whitespace between command and argument is skipped" (fun tag ->
      expect
        (not (survives "\\input  {adv--child}\n" "--"))
        (tag ^ ": TeX allows the space"));

  run "bare plain-TeX form of \\input is protected" (fun tag ->
      expect
        (not (survives "\\input adv--child\n" "--"))
        (tag ^ ": no braces, filename ends at whitespace"));

  run "bare form stops at whitespace" (fun tag ->
      expect
        (survives "\\input child\n\ntext -- here\n" "-- here")
        (tag ^ ": prose after the filename stays live"));

  run "bare form does not swallow a following control sequence" (fun tag ->
      expect
        (survives "\\input \\fname\n\ntext -- here\n" "-- here")
        (tag ^ ": a macro is not a filename"));

  run "nested braces inside a filename argument are balanced" (fun tag ->
      expect
        (not (survives "\\graphicspath{{img--a/}{img--b/}}\n" "--"))
        (tag ^ ": the whole outer group is one argument"));

  run "an unclosed argument protects to end of file" (fun tag ->
      expect
        (not (survives "\\input{adv\n\ntext -- here\n" "-- here"))
        (tag ^ ": TeX reads the unclosed group to EOF; over-wide is safe"));

  run "whole-name match: \\include does not match inside \\includegraphics"
    (fun tag ->
      (* If the scanner matched a prefix, it would stop the range after
         [graphics] and leave the real filename exposed. *)
      expect
        (not (survives "\\includegraphics{fig--1}\n" "--"))
        (tag ^ ": prefix matching would misplace the range"));

  run "a command that is not in the set is not protected" (fun tag ->
      expect
        (survives "\\emph{a -- b}\n" "--")
        (tag ^ ": only include-family commands take filenames"));

  (* ── SHORT-range regressions found by audit against the first draft ─────
     Each of these ended the protected range BEFORE the filename, which is the
     one failure direction this module must not have. They are the exact shapes
     region 3 exists for, so they are pinned here as well as in the corpus. *)
  run "right bracket inside a braced option value does not close the group"
    (fun tag ->
      expect
        (not (survives "\\usepackage[Ligatures={x]y}]{fontspec--local}\n" "--"))
        (tag ^ ": closes only at an unescaped ] at brace depth 0"));

  run "same, for a filename command" (fun tag ->
      expect
        (not (survives "\\includegraphics[caption={a]b}]{fig--1}\n" "--"))
        (tag ^ ": region 3a must not end before the filename"));

  run "option group wrapping across lines still reaches the argument"
    (fun tag ->
      (* The case that ISOLATES the depth-aware bracket scan. On one line the
         end-of-line fallback already rescues a mis-closed group, so the
         single-line version of this test would pass even with a naive scan. *)
      expect
        (not
           (survives
              "\\usepackage[Ligatures={x]y},\n\
              \            Numbers=OldStyle]{adv--sty}\n"
              "--"))
        (tag ^ ": the argument is on the line AFTER the mis-close"));

  run "escaped right bracket does not close the option group" (fun tag ->
      expect
        (not (survives "\\includegraphics[alt=a\\]b]{fig--1}\n" "--"))
        (tag ^ ": an escaped bracket is a character"));

  run "comment between command and argument is skipped" (fun tag ->
      expect
        (not (survives "\\includegraphics%c\n{fig--1}\n" "--"))
        (tag ^ ": TeX swallows the comment before the argument"));

  run "unmodelled token before the argument extends to end of line" (fun tag ->
      expect
        (not (survives "\\includegraphics\\relax{fig--1}\n" "--"))
        (tag ^ ": short range would expose the filename"));

  run "that end-of-line fallback does not cross the newline" (fun tag ->
      expect
        (survives "\\includegraphics\\relax\n\ntext -- here\n" "-- here")
        (tag ^ ": bounded at the newline, not the whole document"));

  (* ── Whole-span testing (not just the start offset) ──────────────────── *)
  run "an edit starting before the range and ending inside it is withheld"
    (fun tag ->
      let src = "x \\input{adv--child}\n" in
      let e =
        Cst_edit.replace ~start_offset:0 ~end_offset:(find_sub src "--" + 2) "y"
      in
      expect
        (Fix_guard.filter ~src ~rule_id:"TYPO-002" [ e ] = [])
        (tag ^ ": straddling edits must not slip through"));

  (* ── Region 3b: package specifications ───────────────────────────────── *)
  run "double hyphen in a package name is withheld" (fun tag ->
      expect
        (not (survives "\\usepackage{adv--sty}\n" "--"))
        (tag ^ ": a local .sty is a filename too"));

  run "double hyphen in a class option is withheld" (fun tag ->
      expect
        (not (survives "\\documentclass[a--b]{article}\n" "--"))
        (tag ^ ": options are consumed as part of the spec"));

  run "a load-order rule is exempt from the package region" (fun tag ->
      expect
        (survives ~rule_id:"PKG-002" "\\usepackage{a--b}\n" "--")
        (tag ^ ": reordering whole \\usepackage lines is its contract"));

  run "a load-order rule is still blocked inside a filename" (fun tag ->
      expect
        (not (survives ~rule_id:"PKG-002" "\\input{a--b}\n" "--"))
        (tag ^ ": the exemption is per region, never global"));

  run "a control-symbol-aware rule is still blocked inside a filename"
    (fun tag ->
      expect
        (not (survives ~rule_id:"TYPO-017" "\\input{a--b}\n" "--"))
        (tag ^ ": region 1 exemption does not carry to region 3"));

  run "insertion just past the closing brace survives" (fun tag ->
      let src = "\\documentclass{article}\n\\begin{document}\n" in
      let at = find_sub src "\n" in
      expect
        (insertion_survives src at)
        (tag ^ ": package inserters must keep working"));

  run "insertion inside the braced argument is withheld" (fun tag ->
      let src = "\\documentclass{article}\n" in
      expect
        (not (insertion_survives src (find_sub src "article")))
        (tag ^ ": a point strictly inside the range is blocked"));

  (* ── Region 5: tabular / array column preamble ───────────────────────────
     The measured case: TYPO-052 rewriting `>` to \textgreater{} inside a
     preamble yields "! Illegal pream-token" and pdflatex 0 -> 1, while
     --compile-check says READY both sides. *)
  run "column preamble of tabular is protected" (fun tag ->
      expect
        (not (survives "\\begin{tabular}{>{\\bfseries}l r}\na -- b\n" ">"))
        (tag ^ ": the measured good_longtable_free corruption"));

  run "preamble of array is protected" (fun tag ->
      expect
        (not (survives "\\begin{array}{>{x}c}\n" ">"))
        (tag ^ ": array takes the same shape as tabular"));

  run "optional [pos] before the preamble is skipped" (fun tag ->
      expect
        (not (survives "\\begin{tabular}[t]{>{\\bfseries}l}\n" ">"))
        (tag ^ ": [pos] must not be mistaken for the preamble"));

  run "tabular* takes the SECOND brace group as its preamble" (fun tag ->
      (* Arity is the whole risk here: treating the width as the preamble would
         end the range before the real one and expose it. *)
      expect
        (not (survives "\\begin{tabular*}{5cm}{>{\\bfseries}l r}\n" ">"))
        (tag ^ ": width first, preamble second"));

  run "tabular* with [pos] between width and preamble" (fun tag ->
      expect
        (not (survives "\\begin{tabularx}{5cm}[t]{>{x}l}\n" ">"))
        (tag ^ ": optional group between the two mandatory ones"));

  run "prose after the tabular is still fixed" (fun tag ->
      expect
        (survives
           "\\begin{tabular}{ll}\na & b\n\\end{tabular}\n\nprose -- here\n"
           "-- here")
        (tag ^ ": region 5 must not become a blanket refusal"));

  run "table BODY is not protected, only the preamble" (fun tag ->
      (* Over-wide is safe, but protecting the whole environment would withhold
         every legitimate fix inside a table, which is a real functional
         loss. *)
      expect
        (survives
           "\\begin{tabular}{ll}\ncell -- dash & b \\\\\n\\end{tabular}\n"
           "-- dash")
        (tag ^ ": the range ends at the preamble's closing brace"));

  run "a missing mandatory group protects NOTHING rather than guessing"
    (fun tag ->
      (* No end-of-line fallback here, unlike region 3: a partial range could
         end BEFORE the preamble and expose it. Declining is today's
         behaviour. *)
      expect
        (survives "\\begin{tabular}\n\nprose -- here\n" "-- here")
        (tag ^ ": scan_preamble_stop returns None, so no range is emitted"));

  run "an unclosed preamble group protects nothing" (fun tag ->
      expect
        (survives "\\begin{tabular}{ll\n\nprose -- here\n" "-- here")
        (tag ^ ": unbalanced group yields None, not a short range"));

  (* ── Regions 1 and 2 still hold (guard against a refactor regression) ── *)
  run "control symbol argument is still protected" (fun tag ->
      let src = "\\`a and -- here\n" in
      let e = Cst_edit.replace ~start_offset:0 ~end_offset:2 "x" in
      expect
        (Fix_guard.filter ~src ~rule_id:"TYPO-013" [ e ] = [])
        (tag ^ ": region 1 unchanged"));

  run "TikZ path operator is still protected" (fun tag ->
      expect
        (not
           (survives
              "\\begin{tikzpicture}\\draw (0,0) -- (1,1);\\end{tikzpicture}\n"
              "--"))
        (tag ^ ": region 2 unchanged"));

  (* ── Memoisation ────────────────────────────────────────────────────── *)
  run "equal content in a distinct buffer gets the same answer" (fun tag ->
      (* The memo is keyed on physical identity, so a fresh string with the same
         bytes must MISS and recompute rather than reuse a neighbour's ranges.
         String.init defeats any sharing the compiler might do on literals. *)
      let a = "\\input{adv--child}\n" in
      let b = String.init (String.length a) (fun i -> a.[i]) in
      let c =
        String.init (String.length a) (fun i -> if i = 8 then 'x' else a.[i])
      in
      expect
        ((not (survives a "--"))
        && (not (survives b "--"))
        && Fix_guard.protected_ranges b = Fix_guard.protected_ranges a
        && Fix_guard.protected_ranges c <> [])
        (tag ^ ": a stale entry may only cause a miss, never a wrong answer"));

  finalise "fix-guard"
