From Coq Require Import List Strings.String.
Import ListNotations.

(** * Token‑list equality after normalisation *)

Record token : Type := mkTok { t_text : string }.

Fixpoint render (ts : list token) : string :=
  match ts with
  | []          => EmptyString
  | mkTok s :: r => append s (render r)
  end.

Definition token_equiv (a b : list token) : Prop :=
  render a = render b.

Lemma token_equiv_refl : forall t, token_equiv t t.
Proof. unfold token_equiv; reflexivity. Qed.

Lemma token_equiv_sym  : forall a b, token_equiv a b -> token_equiv b a.
Proof. unfold token_equiv; intros; symmetry; assumption. Qed.

Lemma token_equiv_trans :
  forall a b c, token_equiv a b -> token_equiv b c -> token_equiv a c.
Proof. unfold token_equiv; intros a b c Hab Hbc; rewrite Hab; exact Hbc. Qed.