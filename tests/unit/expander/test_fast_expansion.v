Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Fast expansion tests that don't timeout *)

Example fast_test_textbf :
  simple_expand [TCommand "textbf"; TBeginGroup; TText "hello"; TEndGroup] = 
  [TCommand "begingroup"; TCommand "bfseries"; TText "hello"; TCommand "endgroup"].
Proof. reflexivity. Qed.

Example fast_test_textit :
  simple_expand [TCommand "textit"; TBeginGroup; TText "italic"; TEndGroup] = 
  [TCommand "textit"; TBeginGroup; TText "italic"; TEndGroup].
Proof. reflexivity. Qed.

Example fast_test_frac :
  simple_expand [TCommand "frac"; TBeginGroup; TText "x"; TEndGroup; TBeginGroup; TText "y"; TEndGroup] = 
  [TCommand "@frac"; TBeginGroup; TText "x"; TEndGroup; TBeginGroup; TText "y"; TEndGroup].
Proof. reflexivity. Qed.

Example fast_test_LaTeX :
  simple_expand [TCommand "LaTeX"] = [TText "LaTeX"].
Proof. reflexivity. Qed.

Example fast_test_nested :
  simple_expand [TCommand "textbf"; TBeginGroup; TCommand "LaTeX"; TEndGroup] = 
  [TCommand "begingroup"; TCommand "bfseries"; TCommand "LaTeX"; TCommand "endgroup"].
Proof. reflexivity. Qed.

(** Test unknown command passthrough *)
Example fast_test_unknown :
  simple_expand [TCommand "unknown"; TText "test"] = [TCommand "unknown"; TText "test"].
Proof. reflexivity. Qed.

Definition FAST_TESTS_COMPLETE : string := "All fast expansion tests completed successfully".