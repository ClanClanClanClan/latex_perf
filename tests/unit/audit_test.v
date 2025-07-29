Require Import String List.
Require Import LatexLexer.
Import ListNotations.
Open Scope string_scope.

(* Test basic functionality - use lex_from_string for string inputs *)
Compute lex_from_string "abc".
Compute lex_from_string "\abc".
Compute lex_from_string "{".
Compute lex_from_string "}".
Compute lex_from_string "$".
Compute lex_from_string "hello world".
Compute lex_from_string "\frac{1}{2}".