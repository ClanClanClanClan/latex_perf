From Coq Require Import List.
Require Import LexerFaithfulStep.

(* Progress/totality-on-nonempty for the faithful L0 step relation. *)
Theorem lexer_step_total_nonempty : forall s,
  s.(L0F.inp) <> [] -> exists s', L0F.step s s'.
Proof. apply L0F.step_progress. Qed.
