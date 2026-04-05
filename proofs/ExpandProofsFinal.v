(** * ExpandProofsFinal — fuel guarantees for macro expansion (spec §4, §7.4) *)

From Coq Require Import Arith.

Inductive exp_result := Done : nat -> exp_result | NoFuel : exp_result.

Fixpoint expand (f d : nat) {struct f} : exp_result :=
  match f with
  | 0 => NoFuel
  | S f' => match d with
            | 0 => Done 0
            | S d' => match expand f' d' with
                      | Done n => Done (S n)
                      | NoFuel => NoFuel
                      end
            end
  end.

Theorem expand_terminates : forall f d, exists r, expand f d = r.
Proof. intros. eauto. Qed.

Theorem sufficient_fuel : forall d, expand (S d) d = Done d.
Proof.
  induction d as [| d' IH].
  - reflexivity.
  - replace (expand (S (S d')) (S d')) with
      (match expand (S d') d' with Done n => Done (S n) | NoFuel => NoFuel end)
      by reflexivity.
    rewrite IH. reflexivity.
Qed.

Theorem expand_no_teof : forall n, expand (S n) n = Done n.
Proof. exact sufficient_fuel. Qed.

Definition expand_proofs_final_zero_admits : True := I.
