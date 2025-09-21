From CoreProofs Require Import Whitespace.

Ltac solve_whitespace :=
  match goal with
  | [ H : strip_spaces ?a = strip_spaces ?b |- _ ] =>
      apply whitespace_equiv in H; try easy
  end.