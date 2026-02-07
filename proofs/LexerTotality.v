From Coq Require Import List.
From LaTeXPerfectionist Require Import LexerFaithfulStep.
Import ListNotations.

(* Progress/totality-on-nonempty for the faithful L0 step relation. *)
Theorem lexer_step_total_nonempty : forall s,
  s.(L0F.inp) <> [] ->
  Forall (fun b => b < 256) (L0F.inp s) ->
  exists s', L0F.step s s'.
Proof. apply L0F.step_progress. Qed.
