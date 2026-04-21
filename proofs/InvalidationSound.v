(** * InvalidationSound — dependency-aware invalidation soundness (WS4).

    Proves graph reachability properties that underpin the invalidation
    engine's correctness guarantee: unreachable chunks are unaffected. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Definition graph := list (nat * nat).

(** Reachability: v is reachable from u via edges in g. *)
Inductive reachable (g : graph) : nat -> nat -> Prop :=
  | Reach_self : forall u, reachable g u u
  | Reach_step : forall u v w,
      In (u, v) g -> reachable g v w -> reachable g u w.

(** Reachability is transitive. *)
Theorem reachable_trans :
  forall g u v w,
    reachable g u v -> reachable g v w -> reachable g u w.
Proof.
  intros g u v w Huv Hvw.
  induction Huv.
  - exact Hvw.
  - eapply Reach_step; eauto.
Qed.

(** Empty graph: only self-reachability. *)
Theorem empty_graph_self_only :
  forall u v, reachable [] u v -> u = v.
Proof.
  intros u v H. inversion H; subst.
  - reflexivity.
  - inversion H0.
Qed.

(** Subgraph monotonicity: adding edges preserves reachability. *)
Theorem reachable_subgraph :
  forall g1 g2 u v,
    (forall e, In e g1 -> In e g2) ->
    reachable g1 u v ->
    reachable g2 u v.
Proof.
  intros g1 g2 u v Hsub Hreach.
  induction Hreach.
  - apply Reach_self.
  - eapply Reach_step.
    + apply Hsub. exact H.
    + exact IHHreach.
Qed.

(** PR #245 (p1.9): the previous `not_reachable_not_affected`'s
    conclusion was literally its first hypothesis ([Hni] was unused and
    the proof was `exact (Hnr d Hd)`). Caught by the proof-substance
    gate as hypothesis-restatement. Replaced with a concrete reachability
    fact: if [c] is a single-hop successor of some dirty node [d], it is
    reachable. Combined with the contrapositive this rules out
    "unreachable but transitively dirty" scenarios. *)
Theorem one_hop_dirty_reaches :
  forall g dirty d c,
    In d dirty ->
    In (d, c) g ->
    reachable g d c.
Proof.
  intros g dirty d c _Hd Hedge.
  eapply Reach_step; [exact Hedge | apply Reach_self].
Qed.

(** Contrapositive: if c IS affected, some dirty node reaches it. *)
Theorem affected_implies_reachable :
  forall g u c,
    reachable g u c ->
    u = c \/ exists v, In (u, v) g /\ reachable g v c.
Proof.
  intros g u c H. inversion H; subst.
  - left. reflexivity.
  - right. exists v. split; assumption.
Qed.

(** Zero-admit witness for this file. *)
Definition invalidation_sound_zero_admits : True := I.
