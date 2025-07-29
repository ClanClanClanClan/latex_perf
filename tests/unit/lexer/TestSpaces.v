Require Import String.
Require Import LatexLexer.
Open Scope string_scope.

(* Use lex_from_string for string inputs instead of lex which expects list ascii *)
Compute lex_from_string "  hello  ".
Compute lex_from_string "\frac {1}".
Compute lex_from_string "% this is a comment".