(** * ElderProofs — Elder orchestrator consistency (spec §5) *)

From Coq Require Import List Arith Lia.
Import ListNotations.

Definition elder_state := list nat. (* generation per layer *)

Fixpoint update_at (state : elder_state) (idx : nat) (val : nat) : elder_state :=
  match state, idx with
  | [], _ => []
  | _ :: rest, 0 => val :: rest
  | v :: rest, S n => v :: update_at rest n val
  end.

Theorem update_preserves_length :
  forall state idx val, length (update_at state idx val) = length state.
Proof.
  induction state as [|v rest IH]; intros; [reflexivity|].
  destruct idx; simpl; [reflexivity | f_equal; apply IH].
Qed.

Theorem update_at_correct :
  forall state idx val,
    idx < length state ->
    nth_error (update_at state idx val) idx = Some val.
Proof.
  induction state as [|v rest IH]; intros idx val H.
  - simpl in H. lia.
  - destruct idx; simpl; [reflexivity | apply IH; simpl in H; lia].
Qed.

Theorem update_at_other :
  forall state idx1 idx2 val,
    idx1 <> idx2 ->
    nth_error (update_at state idx1 val) idx2 = nth_error state idx2.
Proof.
  induction state as [|v rest IH]; intros; [reflexivity|].
  destruct idx1, idx2; simpl; try lia; try reflexivity.
  apply IH. lia.
Qed.

Definition elder_proofs_zero_admits : True := I.
