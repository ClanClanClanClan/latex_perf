From Coq Require Import Strings.String Strings.Ascii List.
Import ListNotations.

(** * Minimal whitespace equivalence lemma used by many fixes *)

Definition is_space (c : ascii) : bool :=
  if (c =? " ")%char then true else false.

Fixpoint strip_spaces (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if is_space c then strip_spaces rest
      else String c (strip_spaces rest)
  end.

Lemma strip_idemp : forall s, strip_spaces (strip_spaces s) = strip_spaces s.
Proof.
  induction s as [|c rest IH]; simpl.
  - reflexivity.
  - destruct (is_space c) eqn:Hspace.
    + apply IH.
    + simpl. rewrite Hspace, IH. reflexivity.
Qed.

(** Placeholder theorem—real version will reason over token lists. *)
Theorem whitespace_equiv :
  forall s t, strip_spaces s = strip_spaces t -> s <> EmptyString -> t <> EmptyString -> True.
Proof. intros; exact I. Qed.