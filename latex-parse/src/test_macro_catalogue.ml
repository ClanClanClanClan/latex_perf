(** Unit tests for Macro_catalogue (L1 macro expander). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[macro-cat] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

(* ── Catalogue paths (relative to project root, where dune runs) ──── *)

let v25r2_path = "../data/macro_catalogue.v25r2.json"
let argsafe_path = "../data/macro_catalogue.argsafe.v25r1.json"
let cat = lazy (Macro_catalogue.load ~v25r2_path ~argsafe_path)

let () =
  (* 1. Load v25r2 catalogue — 441 entries (383 original + 58 expansion) *)
  run "symbol count = 441" (fun tag ->
      let c = Lazy.force cat in
      let n = Macro_catalogue.symbol_count c in
      expect (n = 441) (tag ^ Printf.sprintf ": got %d" n));

  (* 2. Load argsafe catalogue — 62 entries (23 original + 39 expansion) *)
  run "argsafe count = 62" (fun tag ->
      let c = Lazy.force cat in
      let n = Macro_catalogue.argsafe_count c in
      expect (n = 62) (tag ^ Printf.sprintf ": got %d" n));

  (* 3. Lookup alpha → Symbol with TText "α" *)
  run "lookup alpha" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "alpha" with
      | Some (Symbol e) -> (
          match e.expansion with
          | [ Macro_catalogue.TText s ] ->
              expect (s = "\xCE\xB1") (tag ^ ": expansion = " ^ s)
          | _ -> expect false (tag ^ ": unexpected expansion"))
      | _ -> expect false (tag ^ ": not found"));

  (* 4. Lookup textbf → Argsafe with positional=1 *)
  run "lookup textbf" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "textbf" with
      | Some (Argsafe e) -> expect (e.positional = 1) (tag ^ ": positional")
      | _ -> expect false (tag ^ ": not found or wrong type"));

  (* 5. Lookup nonexistent → None *)
  run "lookup nonexistent" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "nonexistent_macro_xyz" with
      | None -> ()
      | Some _ -> expect false (tag ^ ": should be None"));

  (* 6. Expand \alpha → α (symbol expansion) *)
  run "expand \\alpha" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\alpha$" in
      (* \alpha is math mode, so wrap in $ to enable expansion *)
      expect (result = "$\xCE\xB1$") (tag ^ ": got " ^ String.escaped result));

  (* 7. Expand \leq → ≤ (operator) *)
  run "expand \\leq" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\leq$" in
      expect (result = "$\xE2\x89\xA4$") (tag ^ ": got " ^ String.escaped result));

  (* 8. Expand \langle → ⟨ (delimiter, mode=any) *)
  run "expand \\langle" (fun tag ->
      let c = Lazy.force cat in
      (* mode=any should expand even in text context *)
      let result = Macro_catalogue.expand c "\\langle" in
      expect (result = "\xE2\x9F\xA8") (tag ^ ": got " ^ String.escaped result));

  (* 9. Expand \textbf{hello} → {\bfseries hello} (argsafe inline) *)
  run "expand \\textbf{hello}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\textbf{hello}" in
      expect
        (result = "{\\bfseries hello}")
        (tag ^ ": got " ^ String.escaped result));

  (* 10. Expand \emph{world} → {\itshape world} *)
  run "expand \\emph{world}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\emph{world}" in
      expect
        (result = "{\\itshape world}")
        (tag ^ ": got " ^ String.escaped result));

  (* 11. Expand nested: \textbf{\emph{nested}} *)
  run "expand nested" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\textbf{\\emph{nested}}" in
      expect
        (result = "{\\bfseries {\\itshape nested}}")
        (tag ^ ": got " ^ String.escaped result));

  (* 12. Unknown macro passes through unchanged *)
  run "unknown passthrough" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\foobar" in
      expect (result = "\\foobar") (tag ^ ": got " ^ String.escaped result));

  (* 13. Math-only macro in text context → unchanged *)
  run "math-only in text" (fun tag ->
      let c = Lazy.force cat in
      (* \alpha is mode=math; outside $ it should not expand *)
      let result = Macro_catalogue.expand c "\\alpha in text" in
      expect
        (result = "\\alpha in text")
        (tag ^ ": got " ^ String.escaped result));

  (* 14. Text-only macro in math context → unchanged *)
  run "text-only in math" (fun tag ->
      let c = Lazy.force cat in
      (* \texteuro is mode=text; inside $ it should not expand *)
      let result = Macro_catalogue.expand c "$\\texteuro$" in
      expect (result = "$\\texteuro$") (tag ^ ": got " ^ String.escaped result));

  (* 15. Mode=any expands in both contexts *)
  run "any-mode in math" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\langle$" in
      expect
        (String.length result > 0 && result <> "$\\langle$")
        (tag ^ ": got " ^ String.escaped result));

  (* 16. Empty string → empty string *)
  run "empty input" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "" in
      expect (result = "") (tag ^ ": got " ^ String.escaped result));

  (* 17. No macros → unchanged *)
  run "no macros" (fun tag ->
      let c = Lazy.force cat in
      let input = "Hello, world! This has no macros." in
      let result = Macro_catalogue.expand c input in
      expect (result = input) (tag ^ ": got " ^ String.escaped result));

  (* 18. token_to_string coverage *)
  run "token_to_string" (fun tag ->
      expect
        (Macro_catalogue.token_to_string (TText "abc") = "abc")
        (tag ^ ": TText");
      expect (Macro_catalogue.token_to_string (TOp "+") = "+") (tag ^ ": TOp");
      expect
        (Macro_catalogue.token_to_string (TDelim "(") = "(")
        (tag ^ ": TDelim"));

  (* 19. Max expansion bound — doesn't hang *)
  run "termination" (fun tag ->
      let c = Lazy.force cat in
      (* Feed a long string with many macros — should terminate *)
      let buf = Buffer.create 10000 in
      for _ = 1 to 1000 do
        Buffer.add_string buf "$\\alpha$ "
      done;
      let input = Buffer.contents buf in
      let result = Macro_catalogue.expand c input in
      expect (String.length result > 0) (tag ^ ": non-empty result"));

  (* 20. Math context: $\alpha + \beta$ *)
  run "math context full" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\alpha + \\beta$" in
      (* α = \xCE\xB1, β = \xCE\xB2 *)
      expect
        (result = "$\xCE\xB1 + \xCE\xB2$")
        (tag ^ ": got " ^ String.escaped result));

  (* 21. expand_and_tokenize returns tokens *)
  run "expand_and_tokenize" (fun tag ->
      let c = Lazy.force cat in
      let expanded, toks =
        Macro_catalogue.expand_and_tokenize c "\\textbf{ok}"
      in
      expect (expanded = "{\\bfseries ok}") (tag ^ ": expanded");
      expect (List.length toks > 0) (tag ^ ": has tokens"));

  (* 22. Display math \[...\] context *)
  run "display math \\[...\\]" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\[\\alpha\\]" in
      expect (result = "\\[\xCE\xB1\\]") (tag ^ ": got " ^ String.escaped result));

  (* 23. Inline math \(...\) context *)
  run "inline math \\(...\\)" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\(\\alpha\\)" in
      expect (result = "\\(\xCE\xB1\\)") (tag ^ ": got " ^ String.escaped result));

  (* 24. validate_epsilon on inline template *)
  run "epsilon validation" (fun tag ->
      let e : Macro_catalogue.argsafe_entry =
        {
          name = "test";
          mode = Text;
          category = "style";
          positional = 1;
          kinds = [ "text" ];
          template = Inline "{\\bfseries $1}";
        }
      in
      let ok, _ = Macro_catalogue.validate_epsilon e in
      expect ok (tag ^ ": should pass"));

  (* 25. validate_epsilon rejects bad template *)
  run "epsilon reject" (fun tag ->
      let e : Macro_catalogue.argsafe_entry =
        {
          name = "bad";
          mode = Text;
          category = "style";
          positional = 1;
          kinds = [ "text" ];
          template = Inline "\\input{$1}";
        }
      in
      let ok, _ = Macro_catalogue.validate_epsilon e in
      expect (not ok) (tag ^ ": should fail"));

  (* ══════════════════════════════════════════════════════════════════════ NEW
     MACRO EXPANSION TESTS (v25r2 expansion)
     ══════════════════════════════════════════════════════════════════════ *)

  (* 26. Spacing: \quad → em space *)
  run "expand \\quad" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "a\\quad b" in
      expect
        (result = "a\xe2\x80\x83 b")
        (tag ^ ": got " ^ String.escaped result));

  (* 27. Spacing: \qquad → two em spaces *)
  run "expand \\qquad" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "a\\qquad b" in
      expect
        (result = "a\xe2\x80\x83\xe2\x80\x83 b")
        (tag ^ ": got " ^ String.escaped result));

  (* 28. Spacing: \thinspace → thin space *)
  run "expand \\thinspace" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "a\\thinspace b" in
      expect
        (result = "a\xe2\x80\x89 b")
        (tag ^ ": got " ^ String.escaped result));

  (* 29. Font size: \small → empty (no-op for linting) *)
  run "expand \\small" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\small text" in
      expect (result = " text") (tag ^ ": got " ^ String.escaped result));

  (* 30. Font size: \Large → empty *)
  run "expand \\Large" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\Large text" in
      expect (result = " text") (tag ^ ": got " ^ String.escaped result));

  (* 31. Named math operator: \sin in math mode *)
  run "expand \\sin in math" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\sin x$" in
      expect (result = "$sin x$") (tag ^ ": got " ^ String.escaped result));

  (* 32. Named math operator: \lim in math mode *)
  run "expand \\lim in math" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\lim_{n}$" in
      expect (result = "$lim_{n}$") (tag ^ ": got " ^ String.escaped result));

  (* 33. Named math operator: \max in math mode *)
  run "expand \\max in math" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\max(a,b)$" in
      expect (result = "$max(a,b)$") (tag ^ ": got " ^ String.escaped result));

  (* 34. Named math operators don't expand in text mode *)
  run "\\sin in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\sin outside math" in
      expect
        (result = "\\sin outside math")
        (tag ^ ": got " ^ String.escaped result));

  (* 35. Multiple math operators in one expression *)
  run "multiple operators" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\sin^2 + \\cos^2 = 1$" in
      expect
        (result = "$sin^2 + cos^2 = 1$")
        (tag ^ ": got " ^ String.escaped result));

  (* 36. \noindent → empty (no-op) *)
  run "expand \\noindent" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\noindent Hello" in
      expect (result = " Hello") (tag ^ ": got " ^ String.escaped result));

  (* 37. \newline → newline char *)
  run "expand \\newline" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "line1\\newline line2" in
      expect (result = "line1\n line2") (tag ^ ": got " ^ String.escaped result));

  (* 38. Alignment: \centering → empty *)
  run "expand \\centering" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\centering text" in
      expect (result = " text") (tag ^ ": got " ^ String.escaped result));

  (* ══════════════════════════════════════════════════════════════════════ NEW
     ARGSAFE EXPANSION TESTS
     ══════════════════════════════════════════════════════════════════════ *)

  (* 39. Lookup mathbb → Argsafe with positional=1 *)
  run "lookup mathbb" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "mathbb" with
      | Some (Argsafe e) -> expect (e.positional = 1) (tag ^ ": positional")
      | _ -> expect false (tag ^ ": not found or wrong type"));

  (* 40. Expand \mathbb{R} in math mode → passthrough content *)
  run "expand \\mathbb{R}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathbb{R}$" in
      expect (result = "$R$") (tag ^ ": got " ^ String.escaped result));

  (* 41. Expand \mathcal{O} in math mode → passthrough content *)
  run "expand \\mathcal{O}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathcal{O}$" in
      expect (result = "$O$") (tag ^ ": got " ^ String.escaped result));

  (* 42. Expand \hat{x} in math mode → passthrough content *)
  run "expand \\hat{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\hat{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));

  (* 43. Expand \vec{v} in math mode → passthrough content *)
  run "expand \\vec{v}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\vec{v}$" in
      expect (result = "$v$") (tag ^ ": got " ^ String.escaped result));

  (* 44. Expand \overline{AB} in math mode → passthrough content *)
  run "expand \\overline{AB}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\overline{AB}$" in
      expect (result = "$AB$") (tag ^ ": got " ^ String.escaped result));

  (* 45. Expand \underline{text} → passthrough content *)
  run "expand \\underline{text}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\underline{important}" in
      expect (result = "important") (tag ^ ": got " ^ String.escaped result));

  (* 46. Expand \section{Title} → passthrough title *)
  run "expand \\section{Title}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\section{Introduction}" in
      expect (result = "Introduction") (tag ^ ": got " ^ String.escaped result));

  (* 47. Expand \footnote{text} → passthrough text *)
  run "expand \\footnote{text}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "see\\footnote{details here}" in
      expect
        (result = "seedetails here")
        (tag ^ ": got " ^ String.escaped result));

  (* 48. Expand \caption{text} → passthrough text *)
  run "expand \\caption{text}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\caption{Figure 1}" in
      expect (result = "Figure 1") (tag ^ ": got " ^ String.escaped result));

  (* 49. Expand \label{key} → passthrough key *)
  run "expand \\label{key}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\label{eq:main}" in
      expect (result = "eq:main") (tag ^ ": got " ^ String.escaped result));

  (* 50. Expand \ref{key} → passthrough key *)
  run "expand \\ref{key}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\ref{eq:main}" in
      expect (result = "eq:main") (tag ^ ": got " ^ String.escaped result));

  (* 51. Expand \cite{key} → passthrough key *)
  run "expand \\cite{key}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\cite{smith2024}" in
      expect (result = "smith2024") (tag ^ ": got " ^ String.escaped result));

  (* 52. Expand \url{uri} → passthrough uri *)
  run "expand \\url{uri}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\url{https://example.com}" in
      expect
        (result = "https://example.com")
        (tag ^ ": got " ^ String.escaped result));

  (* 53. Expand \boldsymbol{x} in math mode → passthrough *)
  run "expand \\boldsymbol{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\boldsymbol{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));

  (* 54. Math accents don't expand in text mode *)
  run "\\hat in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\hat{x}" in
      expect (result = "\\hat{x}") (tag ^ ": got " ^ String.escaped result));

  (* 55. Sectioning commands don't expand in math mode *)
  run "\\section in math mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\section{x}$" in
      expect (result = "$\\section{x}$") (tag ^ ": got " ^ String.escaped result));

  (* 56. Epsilon validation: new builtins pass *)
  run "epsilon validation math_accent" (fun tag ->
      let e : Macro_catalogue.argsafe_entry =
        {
          name = "hat";
          mode = Math;
          category = "math-accent";
          positional = 1;
          kinds = [ "math" ];
          template = Builtin "math_accent";
        }
      in
      let ok, _ = Macro_catalogue.validate_epsilon e in
      expect ok (tag ^ ": should pass"));

  (* 57. Epsilon validation: passthrough passes *)
  run "epsilon validation passthrough" (fun tag ->
      let e : Macro_catalogue.argsafe_entry =
        {
          name = "section";
          mode = Text;
          category = "sectioning";
          positional = 1;
          kinds = [ "text" ];
          template = Builtin "passthrough";
        }
      in
      let ok, _ = Macro_catalogue.validate_epsilon e in
      expect ok (tag ^ ": should pass"));

  (* 58. Epsilon validation: underline passes *)
  run "epsilon validation underline" (fun tag ->
      let e : Macro_catalogue.argsafe_entry =
        {
          name = "underline";
          mode = Both;
          category = "style";
          positional = 1;
          kinds = [ "text" ];
          template = Builtin "underline";
        }
      in
      let ok, _ = Macro_catalogue.validate_epsilon e in
      expect ok (tag ^ ": should pass"));

  (* 59. Epsilon validation: mathbb builtin passes *)
  run "epsilon validation mathbb builtin" (fun tag ->
      let e : Macro_catalogue.argsafe_entry =
        {
          name = "mathbb";
          mode = Math;
          category = "mathstyle";
          positional = 1;
          kinds = [ "math" ];
          template = Builtin "math_accent";
        }
      in
      let ok, _ = Macro_catalogue.validate_epsilon e in
      expect ok (tag ^ ": should pass"));

  (* 60. Combined expansion: text with multiple macro types *)
  run "combined expansion" (fun tag ->
      let c = Lazy.force cat in
      let result =
        Macro_catalogue.expand c
          "\\section{\\textbf{Results}} Show $\\alpha \\leq \\beta$."
      in
      (* section → passthrough, textbf → bfseries, alpha/leq/beta expand in
         math *)
      expect (String.length result > 0) (tag ^ ": non-empty"));

  (* 61. Lookup new spacing macro *)
  run "lookup quad" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "quad" with
      | Some (Symbol _) -> ()
      | _ -> expect false (tag ^ ": not found as symbol"));

  (* 62. Lookup new math operator *)
  run "lookup sin" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "sin" with
      | Some (Symbol _) -> ()
      | _ -> expect false (tag ^ ": not found as symbol"));

  (* 63. Lookup new sectioning command *)
  run "lookup section" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "section" with
      | Some (Argsafe e) -> expect (e.positional = 1) (tag ^ ": positional")
      | _ -> expect false (tag ^ ": not found or wrong type"));

  (* 64. Lookup new reference command *)
  run "lookup cite" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "cite" with
      | Some (Argsafe e) -> expect (e.positional = 1) (tag ^ ": positional")
      | _ -> expect false (tag ^ ": not found or wrong type"));

  (* 65. Lookup new math accent *)
  run "lookup hat" (fun tag ->
      let c = Lazy.force cat in
      match Macro_catalogue.lookup c "hat" with
      | Some (Argsafe _) -> ()
      | _ -> expect false (tag ^ ": not found as argsafe"));

  (* 66. All new builtins in catalogue pass epsilon validation *)
  run "all catalogue entries pass epsilon" (fun tag ->
      let c = Lazy.force cat in
      (* Look up each new argsafe entry and validate epsilon *)
      let new_names =
        [
          "underline";
          "mathbb";
          "mathcal";
          "mathfrak";
          "mathscr";
          "hat";
          "bar";
          "tilde";
          "vec";
          "dot";
          "ddot";
          "overline";
          "section";
          "subsection";
          "footnote";
          "caption";
          "label";
          "ref";
          "cite";
          "url";
          "boldsymbol";
        ]
      in
      List.iter
        (fun name ->
          match Macro_catalogue.lookup c name with
          | Some (Argsafe e) ->
              let ok, reason = Macro_catalogue.validate_epsilon e in
              expect ok
                (tag
                ^ ": "
                ^ name
                ^ " failed: "
                ^ Option.value ~default:"unknown" reason)
          | _ -> expect false (tag ^ ": " ^ name ^ " not found as argsafe"))
        new_names);

  (* ══════════════════════════════════════════════════════════════════════
     COMPREHENSIVE COVERAGE: every new v25r2 symbol macro
     ══════════════════════════════════════════════════════════════════════ *)

  (* 67–76. Remaining spacing macros *)
  run "expand \\medspace" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "a\\medspace b" in
      expect
        (result = "a\xe2\x81\x9f b")
        (tag ^ ": got " ^ String.escaped result));
  run "expand \\thickspace" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "a\\thickspace b" in
      expect
        (result = "a\xe2\x80\x85 b")
        (tag ^ ": got " ^ String.escaped result));
  run "expand \\enspace" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "a\\enspace b" in
      expect
        (result = "a\xe2\x80\x82 b")
        (tag ^ ": got " ^ String.escaped result));
  run "expand \\negthinspace" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "a\\negthinspace b" in
      expect (result = "a b") (tag ^ ": got " ^ String.escaped result));
  run "expand \\hfill" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "left\\hfill right" in
      expect (result = "left  right") (tag ^ ": got " ^ String.escaped result));
  run "expand \\indent" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\indent paragraph" in
      expect (result = " paragraph") (tag ^ ": got " ^ String.escaped result));

  (* 73–80. Remaining font size switches *)
  run "expand \\tiny" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\tiny text" in
      expect (result = " text") (tag ^ ": got " ^ String.escaped result));
  run "expand \\scriptsize" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\scriptsize x" in
      expect (result = " x") (tag ^ ": got " ^ String.escaped result));
  run "expand \\footnotesize" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\footnotesize y" in
      expect (result = " y") (tag ^ ": got " ^ String.escaped result));
  run "expand \\normalsize" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\normalsize z" in
      expect (result = " z") (tag ^ ": got " ^ String.escaped result));
  run "expand \\large" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\large a" in
      expect (result = " a") (tag ^ ": got " ^ String.escaped result));
  run "expand \\LARGE" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\LARGE b" in
      expect (result = " b") (tag ^ ": got " ^ String.escaped result));
  run "expand \\huge" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\huge c" in
      expect (result = " c") (tag ^ ": got " ^ String.escaped result));
  run "expand \\Huge" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\Huge d" in
      expect (result = " d") (tag ^ ": got " ^ String.escaped result));

  (* 81–84. Remaining formatting/alignment *)
  run "expand \\newpage" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "text\\newpage more" in
      expect (result = "text more") (tag ^ ": got " ^ String.escaped result));
  run "expand \\clearpage" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "text\\clearpage more" in
      expect (result = "text more") (tag ^ ": got " ^ String.escaped result));
  run "expand \\raggedright" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\raggedright text" in
      expect (result = " text") (tag ^ ": got " ^ String.escaped result));
  run "expand \\raggedleft" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\raggedleft text" in
      expect (result = " text") (tag ^ ": got " ^ String.escaped result));

  (* 85–108. Remaining named math operators (every single one) *)
  run "expand \\min" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\min(a,b)$" in
      expect (result = "$min(a,b)$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\sup" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\sup S$" in
      expect (result = "$sup S$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\inf" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\inf S$" in
      expect (result = "$inf S$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\limsup" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\limsup_{n}$" in
      expect (result = "$lim sup_{n}$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\liminf" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\liminf_{n}$" in
      expect (result = "$lim inf_{n}$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\log" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\log x$" in
      expect (result = "$log x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\ln" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\ln x$" in
      expect (result = "$ln x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\exp" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\exp(x)$" in
      expect (result = "$exp(x)$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\cos" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\cos\\theta$" in
      (* \\theta is math symbol → expands to θ *)
      let has_cos = String.length result > 4 && String.sub result 1 3 = "cos" in
      expect has_cos (tag ^ ": got " ^ String.escaped result));
  run "expand \\tan" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\tan x$" in
      expect (result = "$tan x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\arcsin" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\arcsin x$" in
      expect (result = "$arcsin x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\arccos" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\arccos x$" in
      expect (result = "$arccos x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\arctan" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\arctan x$" in
      expect (result = "$arctan x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\sinh" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\sinh x$" in
      expect (result = "$sinh x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\cosh" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\cosh x$" in
      expect (result = "$cosh x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\tanh" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\tanh x$" in
      expect (result = "$tanh x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\cot" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\cot x$" in
      expect (result = "$cot x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\csc" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\csc x$" in
      expect (result = "$csc x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\sec" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\sec x$" in
      expect (result = "$sec x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\det" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\det A$" in
      expect (result = "$det A$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\gcd" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\gcd(a,b)$" in
      expect (result = "$gcd(a,b)$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\hom" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\hom(A,B)$" in
      expect (result = "$hom(A,B)$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\ker" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\ker f$" in
      expect (result = "$ker f$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\deg" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\deg p$" in
      expect (result = "$deg p$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\Pr" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\Pr(X)$" in
      expect (result = "$Pr(X)$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\lg" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\lg n$" in
      expect (result = "$lg n$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\coth" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\coth x$" in
      expect (result = "$coth x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\dim" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\dim V$" in
      expect (result = "$dim V$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\arg" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\arg z$" in
      expect (result = "$arg z$") (tag ^ ": got " ^ String.escaped result));

  (* ══════════════════════════════════════════════════════════════════════
     COMPREHENSIVE COVERAGE: every new argsafe macro
     ══════════════════════════════════════════════════════════════════════ *)

  (* Remaining math accents *)
  run "expand \\bar{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\bar{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\tilde{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\tilde{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\dot{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\dot{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\ddot{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\ddot{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\breve{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\breve{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\acute{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\acute{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\grave{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\grave{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\check{x}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\check{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\widehat{xy}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\widehat{xy}$" in
      expect (result = "$xy$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\widetilde{ab}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\widetilde{ab}$" in
      expect (result = "$ab$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\overbrace{a+b}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\overbrace{a+b}$" in
      expect (result = "$a+b$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\underbrace{x+y}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\underbrace{x+y}$" in
      expect (result = "$x+y$") (tag ^ ": got " ^ String.escaped result));

  (* Remaining math alphabets *)
  run "expand \\mathfrak{g}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathfrak{g}$" in
      expect (result = "$g$") (tag ^ ": got " ^ String.escaped result));
  run "expand \\mathscr{L}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathscr{L}$" in
      expect (result = "$L$") (tag ^ ": got " ^ String.escaped result));

  (* Remaining sectioning commands *)
  run "expand \\part{Title}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\part{Foundations}" in
      expect (result = "Foundations") (tag ^ ": got " ^ String.escaped result));
  run "expand \\chapter{Title}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\chapter{Background}" in
      expect (result = "Background") (tag ^ ": got " ^ String.escaped result));
  run "expand \\subsection{Title}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\subsection{Methods}" in
      expect (result = "Methods") (tag ^ ": got " ^ String.escaped result));
  run "expand \\subsubsection{Title}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\subsubsection{Details}" in
      expect (result = "Details") (tag ^ ": got " ^ String.escaped result));
  run "expand \\paragraph{Title}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\paragraph{Note}" in
      expect (result = "Note") (tag ^ ": got " ^ String.escaped result));
  run "expand \\subparagraph{Title}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\subparagraph{Remark}" in
      expect (result = "Remark") (tag ^ ": got " ^ String.escaped result));

  (* Remaining document metadata *)
  run "expand \\title{text}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\title{My Paper}" in
      expect (result = "My Paper") (tag ^ ": got " ^ String.escaped result));
  run "expand \\author{text}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\author{Jane Doe}" in
      expect (result = "Jane Doe") (tag ^ ": got " ^ String.escaped result));
  run "expand \\date{text}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\date{2026}" in
      expect (result = "2026") (tag ^ ": got " ^ String.escaped result));

  (* Remaining references *)
  run "expand \\eqref{key}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\eqref{eq:euler}" in
      expect (result = "eq:euler") (tag ^ ": got " ^ String.escaped result));
  run "expand \\pageref{key}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\pageref{ch:intro}" in
      expect (result = "ch:intro") (tag ^ ": got " ^ String.escaped result));

  (* ══════════════════════════════════════════════════════════════════════
     REGRESSION: mathrm/mathbf self-reference bug fix
     ══════════════════════════════════════════════════════════════════════ *)
  run "mathrm no longer self-references" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathrm{x}$" in
      (* Before the fix, this produced ${{{...\\mathrm{x}...}}}$ with 256
         braces *)
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result);
      expect
        (String.length result < 10)
        (tag ^ ": length " ^ string_of_int (String.length result)));
  run "mathbf no longer self-references" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathbf{v}$" in
      expect (result = "$v$") (tag ^ ": got " ^ String.escaped result);
      expect (String.length result < 10) (tag ^ ": bounded length"));
  run "mathsf no longer self-references" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathsf{T}$" in
      expect (result = "$T$") (tag ^ ": got " ^ String.escaped result));
  run "mathtt no longer self-references" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathtt{code}$" in
      expect (result = "$code$") (tag ^ ": got " ^ String.escaped result));
  run "mathit no longer self-references" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathit{n}$" in
      expect (result = "$n$") (tag ^ ": got " ^ String.escaped result));
  run "mathnormal no longer self-references" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\mathnormal{x}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));

  (* ══════════════════════════════════════════════════════════════════════
     MODE-FILTERING NEGATIVE TESTS
     ══════════════════════════════════════════════════════════════════════ *)

  (* Math operators MUST NOT expand in text mode *)
  run "\\cos in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\cos is a function" in
      expect
        (result = "\\cos is a function")
        (tag ^ ": got " ^ String.escaped result));
  run "\\det in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\det of matrix" in
      expect
        (result = "\\det of matrix")
        (tag ^ ": got " ^ String.escaped result));
  run "\\log in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\log base 2" in
      expect (result = "\\log base 2") (tag ^ ": got " ^ String.escaped result));

  (* Math accents MUST NOT expand in text mode *)
  run "\\bar in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\bar{x} in text" in
      expect
        (result = "\\bar{x} in text")
        (tag ^ ": got " ^ String.escaped result));
  run "\\tilde in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\tilde{n} in text" in
      expect
        (result = "\\tilde{n} in text")
        (tag ^ ": got " ^ String.escaped result));
  run "\\mathbb in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\mathbb{R} in text" in
      expect
        (result = "\\mathbb{R} in text")
        (tag ^ ": got " ^ String.escaped result));
  run "\\boldsymbol in text mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\boldsymbol{x} in text" in
      expect
        (result = "\\boldsymbol{x} in text")
        (tag ^ ": got " ^ String.escaped result));

  (* Text-mode commands MUST NOT expand in math mode *)
  run "\\subsection in math mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\subsection{x}$" in
      expect
        (result = "$\\subsection{x}$")
        (tag ^ ": got " ^ String.escaped result));
  run "\\footnote in math mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\footnote{x}$" in
      expect
        (result = "$\\footnote{x}$")
        (tag ^ ": got " ^ String.escaped result));
  run "\\caption in math mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\caption{x}$" in
      expect (result = "$\\caption{x}$") (tag ^ ": got " ^ String.escaped result));
  run "\\label in math mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\label{x}$" in
      expect (result = "$\\label{x}$") (tag ^ ": got " ^ String.escaped result));
  run "\\centering in math mode" (fun tag ->
      let c = Lazy.force cat in
      (* centering is text-mode only; inside $ it should not expand *)
      let result = Macro_catalogue.expand c "$\\centering$" in
      expect (result = "$\\centering$") (tag ^ ": got " ^ String.escaped result));

  (* Spacing macros (mode=any) SHOULD expand in both modes *)
  run "\\quad in math mode" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$a\\quad b$" in
      expect
        (result = "$a\xe2\x80\x83 b$")
        (tag ^ ": got " ^ String.escaped result));

  (* ══════════════════════════════════════════════════════════════════════ EDGE
     CASES AND COMPLEX SCENARIOS
     ══════════════════════════════════════════════════════════════════════ *)

  (* Nested math accents *)
  run "nested accents: \\hat{\\vec{x}}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\hat{\\vec{x}}$" in
      (* hat expands first → \\vec{x}, then vec expands → x *)
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));
  run "nested accents: \\overline{\\hat{x}}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\overline{\\hat{x}}$" in
      expect (result = "$x$") (tag ^ ": got " ^ String.escaped result));

  (* Nested sectioning + formatting *)
  run "nested: \\section{\\textbf{Title}}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "\\section{\\textbf{Title}}" in
      (* section → passthrough → \\textbf{Title} → {\\bfseries Title} *)
      expect
        (result = "{\\bfseries Title}")
        (tag ^ ": got " ^ String.escaped result));

  (* Empty argument *)
  run "empty arg: \\hat{}" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\hat{}$" in
      expect (result = "$$") (tag ^ ": got " ^ String.escaped result));

  (* Macro at very end of string with no trailing content *)
  run "trailing macro: $\\sin$" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$\\sin$" in
      expect (result = "$sin$") (tag ^ ": got " ^ String.escaped result));

  (* $$...$$ display math context with new macros *)
  run "display $$ with \\sin" (fun tag ->
      let c = Lazy.force cat in
      let result = Macro_catalogue.expand c "$$\\sin x$$" in
      expect (result = "$$sin x$$") (tag ^ ": got " ^ String.escaped result));

  (* Combined expansion with precise assertion *)
  run "combined precise" (fun tag ->
      let c = Lazy.force cat in
      let result =
        Macro_catalogue.expand c
          "\\section{\\textbf{Results}} Show $\\alpha \\leq \\beta$."
      in
      (* section → passthrough "\\textbf{Results}" → "{\\bfseries Results}" Then
         " Show $α ≤ β$." *)
      expect
        (result = "{\\bfseries Results} Show $\xCE\xB1 \xE2\x89\xA4 \xCE\xB2$.")
        (tag ^ ": got " ^ String.escaped result));

  (* All 62 argsafe entries pass epsilon validation (comprehensive) *)
  run "all 62 argsafe entries pass epsilon" (fun tag ->
      let c = Lazy.force cat in
      let all_argsafe =
        [
          "acute";
          "author";
          "bar";
          "boldsymbol";
          "breve";
          "caption";
          "chapter";
          "check";
          "cite";
          "date";
          "ddot";
          "dot";
          "emph";
          "ensuremath";
          "eqref";
          "footnote";
          "grave";
          "hat";
          "label";
          "mathbb";
          "mathbf";
          "mathcal";
          "mathfrak";
          "mathit";
          "mathnormal";
          "mathrm";
          "mathscr";
          "mathsf";
          "mathtt";
          "mbox";
          "overbrace";
          "overline";
          "pageref";
          "paragraph";
          "part";
          "ref";
          "section";
          "subparagraph";
          "subsection";
          "subsubsection";
          "textbf";
          "textit";
          "textmd";
          "textnormal";
          "textrm";
          "textsc";
          "textsf";
          "textsl";
          "textsubscript";
          "textsuperscript";
          "texttt";
          "textup";
          "tilde";
          "title";
          "underbrace";
          "underline";
          "url";
          "vec";
          "verb";
          "verb*";
          "widehat";
          "widetilde";
        ]
      in
      expect
        (List.length all_argsafe = 62)
        (tag
        ^ ": list has "
        ^ string_of_int (List.length all_argsafe)
        ^ " entries, expected 62");
      List.iter
        (fun name ->
          match Macro_catalogue.lookup c name with
          | Some (Argsafe e) ->
              let ok, reason = Macro_catalogue.validate_epsilon e in
              expect ok
                (tag
                ^ ": "
                ^ name
                ^ " failed: "
                ^ Option.value ~default:"unknown" reason)
          | _ -> expect false (tag ^ ": " ^ name ^ " not found as argsafe"))
        all_argsafe);

  (* All 58 new v25r2 symbols are loadable *)
  run "all 58 new v25r2 symbols present" (fun tag ->
      let c = Lazy.force cat in
      let new_syms =
        [
          "quad";
          "qquad";
          "thinspace";
          "medspace";
          "thickspace";
          "enspace";
          "negthinspace";
          "hfill";
          "noindent";
          "indent";
          "newline";
          "newpage";
          "clearpage";
          "tiny";
          "scriptsize";
          "footnotesize";
          "small";
          "normalsize";
          "large";
          "Large";
          "LARGE";
          "huge";
          "Huge";
          "centering";
          "raggedright";
          "raggedleft";
          "lim";
          "max";
          "min";
          "sup";
          "inf";
          "limsup";
          "liminf";
          "log";
          "ln";
          "exp";
          "lg";
          "sin";
          "cos";
          "tan";
          "arcsin";
          "arccos";
          "arctan";
          "sinh";
          "cosh";
          "tanh";
          "cot";
          "csc";
          "sec";
          "coth";
          "det";
          "dim";
          "gcd";
          "hom";
          "ker";
          "deg";
          "arg";
          "Pr";
        ]
      in
      expect
        (List.length new_syms = 58)
        (tag
        ^ ": list has "
        ^ string_of_int (List.length new_syms)
        ^ " entries, expected 58");
      List.iter
        (fun name ->
          match Macro_catalogue.lookup c name with
          | Some (Symbol _) -> ()
          | _ -> expect false (tag ^ ": " ^ name ^ " not found as symbol"))
        new_syms);

  if !fails > 0 then (
    Printf.eprintf "[macro-cat] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[macro-cat] PASS %d cases\n%!" !cases
