(* LaTeX Perfectionist v24 - Phase 1: Lexer Demo *)
(* Week 2: Testing lexer on simple LaTeX snippets *)

Require Import String List.
Require Import lexer.LatexLexer.
Import ListNotations.
Open Scope string_scope.

(* Test 1: Simple command *)
Compute lex_string "\frac".

(* Test 2: Simple group *)
Compute lex_string "{hello}".

(* Test 3: Math mode *)
Compute lex_string "$x^2$".

(* Test 4: Fraction *)
Compute lex_string "\frac{1}{2}".

(* Test 5: Begin environment *)
Compute lex_string "\begin{equation}".

(* Test 6: Starred command *)
Compute lex_string "\section*{Introduction}".

(* Test 7: Complex expression *)
Compute lex_string "$\int_0^1 f(x) dx$".

(* Test 8: Comment *)
Compute lex_string "% This is a comment".

(* Test 9: Alignment *)
Compute lex_string "a & b & c \\".

(* Test 10: Corpus example *)
Compute lex_string "\documentclass{article}\begin{document}Hello!\end{document}".