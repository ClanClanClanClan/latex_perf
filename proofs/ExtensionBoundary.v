(** ExtensionBoundary — v27 "extension-boundary correctness" proof family
    (specs/v27/V27_REPO_EXACT_MASTER_SPEC.md §7 "Required new proof families").

    WS12 shipped runtime-only in [latex-parse/src/extension_contract.ml].  This
    file formalises the CORE invariants of that runtime's foreign-contract
    boundary in a small, faithful, admit-free model — mirroring the style of
    [proofs/LexerFaithfulStep.v] (a compact model plus Qed soundness theorems,
    0 admits, 0 axioms).

    Runtime shape mirrored ([extension_contract.ml]):
    - support levels are ordered [Foreign < Community < Supported]
      ([support_rank]); [support_min] takes the weaker of two;
    - each risk level has a cap on the support it may claim
      ([max_support_for_risk]: Safe->Supported, Review->Community,
      Unsafe->Foreign);
    - [over_claims c] holds iff the contract declares support ABOVE its cap;
    - [evaluate ~base contracts] REJECTS (returns [Error]) if any contract
      over-claims, else returns the effective support = [fold_left support_min]
      from [base] over the declared supports.

    We prove, all by [Qed] (checked [Closed under the global context]):
    (a) MONOTONE-DOWNGRADE — the effective level never exceeds [base];
    (b) DOWNGRADE-WITNESS  — a foreign/unsafe extension strictly lowers it;
    (c) FAIL-CLOSED        — any over-claim makes [evaluate] reject (return
                             [None]); no over-claim is ever accepted;
    (d) CAP-SOUNDNESS      — a contract built AT its risk cap does not
                             over-claim, one ABOVE the cap does; i.e.
                             [over_claims] exactly captures the boundary.
    Plus concrete non-vacuity witnesses. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

Module ExtBoundary.

  (* Ordered support levels (weakest -> strongest). *)
  Inductive support := Foreign | Community | Supported.

  (* Risk levels. *)
  Inductive risk := Safe | Review | Unsafe.

  (* Numeric rank — mirrors [support_rank]. *)
  Definition support_rank (s : support) : nat :=
    match s with Foreign => 0 | Community => 1 | Supported => 2 end.

  (* The weaker of two supports — mirrors [support_min]. *)
  Definition support_min (a b : support) : support :=
    if Nat.leb (support_rank a) (support_rank b) then a else b.

  (* Strongest support a given risk may claim — mirrors [max_support_for_risk]. *)
  Definition max_support_for_risk (r : risk) : support :=
    match r with Safe => Supported | Review => Community | Unsafe => Foreign end.

  (* A contract (only the fields the boundary depends on). *)
  Record contract := { c_risk : risk; c_support : support }.

  (* [over_claims c] — declares support strictly above its cap.  Mirrors
     [over_claims]. *)
  Definition over_claims (c : contract) : bool :=
    Nat.ltb (support_rank (max_support_for_risk (c_risk c)))
            (support_rank (c_support c)).

  (* [evaluate base cs] — REJECT (None) if any contract over-claims, else the
     effective support folded from [base] via [support_min].  Mirrors
     [evaluate]: [rejections = filter over_claims cs]; nonempty -> Error;
     otherwise [fold_left support_min base cs]. *)
  Definition evaluate (base : support) (cs : list contract) : option support :=
    if existsb over_claims cs then None
    else Some (fold_left (fun acc c => support_min acc (c_support c)) cs base).

  (* ── Basic facts about [support_min] ─────────────────────────────────── *)

  Lemma support_min_rank_le_l : forall a b,
    support_rank (support_min a b) <= support_rank a.
  Proof.
    intros a b. unfold support_min.
    destruct (Nat.leb (support_rank a) (support_rank b)) eqn:E.
    - reflexivity.
    - apply Nat.leb_gt in E. lia.
  Qed.

  Lemma fold_min_rank_le_base : forall cs base,
    support_rank (fold_left (fun acc c => support_min acc (c_support c)) cs base)
    <= support_rank base.
  Proof.
    induction cs as [|c cs IH]; intro base; simpl; [reflexivity|].
    eapply Nat.le_trans; [apply IH|].
    apply support_min_rank_le_l.
  Qed.

  (* ── (a) MONOTONE-DOWNGRADE ──────────────────────────────────────────
     Whenever [evaluate] accepts, the effective support never RANKS above the
     base — the guarantee is only ever preserved or weakened, never upgraded. *)
  Theorem evaluate_monotone_downgrade : forall base cs eff,
    evaluate base cs = Some eff ->
    support_rank eff <= support_rank base.
  Proof.
    intros base cs eff Heval. unfold evaluate in Heval.
    destruct (existsb over_claims cs) eqn:Ex; [discriminate|].
    injection Heval as Heff. subst eff.
    apply fold_min_rank_le_base.
  Qed.

  (* ── (b) DOWNGRADE-WITNESS ───────────────────────────────────────────
     A foreign+unsafe extension against a [Supported] base yields a STRICTLY
     lower effective level — the downgrade theorem is non-vacuous. *)
  Definition foreign_unsafe : contract :=
    {| c_risk := Unsafe; c_support := Foreign |}.

  Theorem evaluate_strict_downgrade_witness :
    exists base cs eff,
      evaluate base cs = Some eff /\
      support_rank eff < support_rank base.
  Proof.
    exists Supported, (foreign_unsafe :: nil), Foreign.
    split; [vm_compute; reflexivity | vm_compute; lia].
  Qed.

  (* ── (c) FAIL-CLOSED ─────────────────────────────────────────────────
     If ANY contract over-claims, [evaluate] rejects (returns None).  No
     over-claiming contract is ever accepted into an effective guarantee. *)
  Theorem evaluate_fail_closed : forall base cs c,
    In c cs -> over_claims c = true ->
    evaluate base cs = None.
  Proof.
    intros base cs c Hin Hover. unfold evaluate.
    assert (Hex : existsb over_claims cs = true).
    { apply existsb_exists. exists c. split; assumption. }
    rewrite Hex. reflexivity.
  Qed.

  (* Conversely, acceptance implies NO contract over-claims — the boundary is
     exactly the over-claim set. *)
  Theorem evaluate_accept_no_overclaim : forall base cs eff,
    evaluate base cs = Some eff ->
    forall c, In c cs -> over_claims c = false.
  Proof.
    intros base cs eff Heval c Hin. unfold evaluate in Heval.
    destruct (existsb over_claims cs) eqn:Ex; [discriminate|].
    destruct (over_claims c) eqn:Ec; [|reflexivity].
    assert (existsb over_claims cs = true).
    { apply existsb_exists. exists c. split; assumption. }
    congruence.
  Qed.

  (* ── (d) CAP-SOUNDNESS ───────────────────────────────────────────────
     [over_claims] captures EXACTLY the cap boundary. *)

  (* over_claims is the boolean reflection of "support ranks above the cap". *)
  Theorem over_claims_iff : forall c,
    over_claims c = true <->
    support_rank (max_support_for_risk (c_risk c)) < support_rank (c_support c).
  Proof.
    intro c. unfold over_claims. apply Nat.ltb_lt.
  Qed.

  (* A contract built AT its risk cap does not over-claim. *)
  Theorem cap_no_overclaim : forall r,
    over_claims {| c_risk := r; c_support := max_support_for_risk r |} = false.
  Proof.
    intro r. unfold over_claims. simpl.
    apply Nat.ltb_ge. reflexivity.
  Qed.

  (* Any contract declaring support ABOVE its cap does over-claim. *)
  Theorem above_cap_overclaims : forall r s,
    support_rank (max_support_for_risk r) < support_rank s ->
    over_claims {| c_risk := r; c_support := s |} = true.
  Proof.
    intros r s Hlt. unfold over_claims. simpl. apply Nat.ltb_lt. exact Hlt.
  Qed.

  (* Concrete boundary witnesses: an Unsafe extension (cap = Foreign) may claim
     Foreign but NOT Community. *)
  Example unsafe_at_cap_ok :
    over_claims {| c_risk := Unsafe; c_support := Foreign |} = false.
  Proof. reflexivity. Qed.

  Example unsafe_above_cap_bad :
    over_claims {| c_risk := Unsafe; c_support := Community |} = true.
  Proof. reflexivity. Qed.

  (* And [evaluate] indeed rejects the above-cap one but accepts (and
     downgrades) the at-cap one — a fully worked non-vacuity witness. *)
  Example evaluate_rejects_overclaim :
    evaluate Supported
      ({| c_risk := Unsafe; c_support := Community |} :: nil) = None.
  Proof. reflexivity. Qed.

  Example evaluate_accepts_and_downgrades :
    evaluate Supported
      ({| c_risk := Review; c_support := Community |} :: nil) = Some Community.
  Proof. reflexivity. Qed.

End ExtBoundary.
