From Coq Require Import List.
Require Import LexerFaithfulStep.

(* Determinism for the faithful L0 step relation. *)
Theorem lexer_step_determinism : forall s s1 s2,
  L0F.step s s1 -> L0F.step s s2 -> s1 = s2.
Proof. apply L0F.step_deterministic. Qed.
