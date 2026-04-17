(** * BuildLog — formal contract for compile-log derived facts (WS1).

    Models the log parser's fact extraction and proves monotonicity:
    a superset of log events yields a superset of derived facts. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Inductive log_event : Type :=
  | Overfull : nat -> log_event
  | Underfull : nat -> log_event
  | WidowPenalty : log_event
  | ClubPenalty : log_event
  | FloatWarning : log_event.

Definition log := list log_event.

Fixpoint has_event (e : log_event) (l : log) : bool :=
  match l with
  | [] => false
  | x :: xs =>
      match e, x with
      | WidowPenalty, WidowPenalty => true
      | ClubPenalty, ClubPenalty => true
      | FloatWarning, FloatWarning => true
      | _, _ => has_event e xs
      end
  end.

Fixpoint count_overfull (l : log) : nat :=
  match l with
  | [] => 0
  | Overfull _ :: xs => S (count_overfull xs)
  | _ :: xs => count_overfull xs
  end.

Fixpoint count_underfull (l : log) : nat :=
  match l with
  | [] => 0
  | Underfull _ :: xs => S (count_underfull xs)
  | _ :: xs => count_underfull xs
  end.

(** Monotonicity: appending events only increases counts. *)
Theorem count_overfull_app : forall l1 l2,
  count_overfull l1 <= count_overfull (l1 ++ l2).
Proof.
  induction l1 as [|e l1' IH]; simpl; intros.
  - lia.
  - destruct e; simpl; try (apply IH); apply le_n_S; apply IH.
Qed.

Theorem count_underfull_app : forall l1 l2,
  count_underfull l1 <= count_underfull (l1 ++ l2).
Proof.
  induction l1 as [|e l1' IH]; simpl; intros.
  - lia.
  - destruct e; simpl; try (apply IH); apply le_n_S; apply IH.
Qed.

(** Adding events never removes existing widow/club/float signals. *)
Theorem has_event_preserved : forall e l1 l2,
  has_event e l1 = true ->
  has_event e (l1 ++ l2) = true.
Proof.
  induction l1 as [|x l1' IH]; simpl; intros.
  - discriminate.
  - destruct e, x; simpl; auto.
Qed.

(** Zero-admit witness for this file. *)
Definition build_log_zero_admits : True := I.
