Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Test using SimpleExpander which has built-in limits *)

Example test_simple_textbf :
  simple_expand [TCommand "textbf"; TBeginGroup; TText "hello"; TEndGroup] = 
  [TCommand "begingroup"; TCommand "bfseries"; TText "hello"; TCommand "endgroup"].
Proof. simpl. reflexivity. Qed.

Example test_simple_text :
  simple_expand [TText "hello"] = [TText "hello"].
Proof. simpl. reflexivity. Qed.

Example test_simple_LaTeX :
  simple_expand [TCommand "LaTeX"] = [TText "LaTeX"].
Proof. simpl. reflexivity. Qed.