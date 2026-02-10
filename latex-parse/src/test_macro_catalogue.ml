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
  (* 1. Load v25r2 catalogue — 383 entries *)
  run "symbol count = 383" (fun tag ->
      let c = Lazy.force cat in
      let n = Macro_catalogue.symbol_count c in
      expect (n = 383) (tag ^ Printf.sprintf ": got %d" n));

  (* 2. Load argsafe catalogue — 23 entries *)
  run "argsafe count = 23" (fun tag ->
      let c = Lazy.force cat in
      let n = Macro_catalogue.argsafe_count c in
      expect (n = 23) (tag ^ Printf.sprintf ": got %d" n));

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

  if !fails > 0 then (
    Printf.eprintf "[macro-cat] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[macro-cat] PASS %d cases\n%!" !cases
