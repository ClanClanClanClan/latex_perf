From Coq Require Import Ascii String List Bool.
Import ListNotations.

(** * UTF‑8–safe regex helper lemmas (placeholder)*)

Definition quote_char : ascii := Ascii false true false false false true true false.

Definition ascii_is_quote (c : ascii) : bool :=
  if Ascii.eqb c quote_char then true else false.

Lemma quote_detect :
  forall c, ascii_is_quote c = true -> c = quote_char.
Proof.
  intros c H; unfold ascii_is_quote in H.
  destruct (Ascii.eqb c quote_char) eqn:Heq; [|discriminate].
  apply Ascii.eqb_eq in Heq; exact Heq.
Qed.