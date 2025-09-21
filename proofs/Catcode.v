(** Coq model of the v25 catcode enumeration. Mirrors OCaml [Data.Types.Catcode]. *)
Inductive catcode : Type :=
  | Escape | BeginGrp | EndGrp | Math | AlignTab | Newline | Param
  | Superscr | Subscr | Ignored | Space | Letter | Other | Active
  | Comment | Invalid.

Definition catcode_to_nat (c : catcode) : nat :=
  match c with
  | Escape => 0 | BeginGrp => 1 | EndGrp => 2 | Math => 3
  | AlignTab => 4 | Newline => 5 | Param => 6 | Superscr => 7
  | Subscr => 8 | Ignored => 9 | Space => 10 | Letter => 11
  | Other => 12 | Active => 13 | Comment => 14 | Invalid => 15
  end.

Definition nat_to_catcode (n : nat) : option catcode :=
  match n with
  | 0 => Some Escape   | 1 => Some BeginGrp | 2 => Some EndGrp
  | 3 => Some Math     | 4 => Some AlignTab | 5 => Some Newline
  | 6 => Some Param    | 7 => Some Superscr | 8 => Some Subscr
  | 9 => Some Ignored  | 10 => Some Space   | 11 => Some Letter
  | 12 => Some Other   | 13 => Some Active  | 14 => Some Comment
  | 15 => Some Invalid | _ => None
  end.

Lemma nat_catcode_inverse : forall c,
  nat_to_catcode (catcode_to_nat c) = Some c.
Proof. destruct c; reflexivity. Qed.

Lemma catcode_eq_dec : forall (a b : catcode), {a = b} + {a <> b}.
Proof.
  intros a b; destruct a; destruct b;
    (left; reflexivity) || (right; discriminate).
Qed.

Lemma nat_to_catcode_inv : forall n c,
  nat_to_catcode n = Some c -> catcode_to_nat c = n.
Proof.
  intros n c H.
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  destruct n; simpl in H; [inversion H; reflexivity|].
  discriminate H.
Qed.

(* ASCII helper mirroring the OCaml classifier. *)
Definition classify_ascii (n : nat) : catcode :=
  match nat_to_catcode n with
  | Some c => c
  | None => Other
  end.

