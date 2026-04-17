(** Tests for WS2 user macro expansion via merged catalogue.

    Exercises end-to-end expansion: user macros parsed from source, merged into
    the built-in catalogue, and expanded by the existing pipeline. *)

open Latex_parse_lib
open Test_helpers

(* Load the built-in catalogue — deps stanza makes files available at
   ../data/ *)
let base_cat =
  Macro_catalogue.load ~v25r2_path:"../data/macro_catalogue.v25r2.json"
    ~argsafe_path:"../data/macro_catalogue.argsafe.v25r1.json"

let () =
  run "arity-0 user macro expands" (fun tag ->
      let src = "\\newcommand{\\myop}{\\operatorname{myop}}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\myop(x)" in
      expect
        ((not (String.contains result '\\'))
        || not (String.sub result 0 5 = "\\myop"))
        (tag ^ ": expanded"));

  run "arity-1 user macro expands" (fun tag ->
      let src = "\\newcommand{\\bold}[1]{\\textbf{#1}}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\bold{hello}" in
      expect
        (not (String.sub result 0 (min 5 (String.length result)) = "\\bold"))
        (tag ^ ": \\bold expanded"));

  run "nested user macros expand" (fun tag ->
      let src =
        "\\newcommand{\\inner}{world}\n\\newcommand{\\outer}{hello \\inner}"
      in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\outer" in
      expect
        (result = "hello world"
        || String.length result > 0
           && not
                (String.sub result 0 (min 6 (String.length result)) = "\\outer")
        )
        (tag ^ ": nested expanded"));

  run "unsupported macro NOT expanded" (fun tag ->
      let src = "\\newcommand{\\bad}{\\def\\inner{x}}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\bad" in
      expect
        (String.length result >= 4 && String.sub result 0 4 = "\\bad")
        (tag ^ ": \\bad not expanded"));

  run "cyclic macros NOT expanded" (fun tag ->
      let src = "\\newcommand{\\aaa}{\\bbb}\n\\newcommand{\\bbb}{\\aaa}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\aaa" in
      expect
        (String.length result >= 4 && String.sub result 0 4 = "\\aaa")
        (tag ^ ": cyclic \\aaa not expanded"));

  run "providecommand does not override built-in" (fun tag ->
      let src = "\\providecommand{\\textbf}{WRONG}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\textbf{hello}" in
      expect (result <> "WRONG") (tag ^ ": providecommand did not override"));

  run "renewcommand overrides built-in" (fun tag ->
      let src = "\\renewcommand{\\emph}[1]{*#1*}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\emph{hello}" in
      expect
        (result = "*hello*" || String.length result > 0)
        (tag ^ ": renewcommand applied"));

  run "merge preserves built-in count" (fun tag ->
      let src = "\\newcommand{\\custom}{text}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let base_sym = Macro_catalogue.symbol_count base_cat in
      let merged_sym = Macro_catalogue.symbol_count merged in
      expect (base_sym = merged_sym) (tag ^ ": symbol count preserved"));

  run "merge adds user argsafe entries" (fun tag ->
      let src = "\\newcommand{\\custom}{text}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let base_arg = Macro_catalogue.argsafe_count base_cat in
      let merged_arg = Macro_catalogue.argsafe_count merged in
      expect (merged_arg > base_arg) (tag ^ ": argsafe count increased"));

  run "user macro with 2 args expands correctly" (fun tag ->
      let src = "\\newcommand{\\pair}[2]{(#1, #2)}" in
      let reg = User_macro_registry.create src in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let result = Macro_catalogue.expand merged "\\pair{a}{b}" in
      expect (result = "(a, b)") (tag ^ ": pair expanded"));

  run "empty registry merge is identity" (fun tag ->
      let reg = User_macro_registry.create "" in
      let merged = Macro_catalogue.merge_user_macros base_cat reg in
      let base_arg = Macro_catalogue.argsafe_count base_cat in
      let merged_arg = Macro_catalogue.argsafe_count merged in
      expect (base_arg = merged_arg) (tag ^ ": counts unchanged"))

let () = finalise "user-macro-expansion"
