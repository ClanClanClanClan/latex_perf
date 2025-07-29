Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Import LatexLexer.
Open Scope string_scope.

(** Test to understand actual lexer behavior **)

(** Check what these actually parse to **)
Compute (lex "hello").
Compute (lex "hello world").
Compute (lex "\\LaTeX").
Compute (lex "{hello}").
Compute (lex "Hello \\LaTeX{} world").

(** Simple test that should work **)
Example test_simple_empty : 
  lex "" = [].
Proof. vm_compute. reflexivity. Qed.