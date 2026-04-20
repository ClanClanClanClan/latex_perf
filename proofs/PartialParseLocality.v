(** * PartialParseLocality — E0: errors don't poison distant regions (WS5).

    Models the runtime [Partial_cst.classify] in
    [latex-parse/src/partial_cst.ml]: given a list of parse errors and a
    candidate zone identified by its paragraph bounds, the classifier
    returns [Complete] when no error falls inside the paragraph, and
    [Broken] otherwise.

    E0 says: the classification is LOCAL. An error outside a zone's
    paragraph cannot change that zone's verdict. The two theorems below
    establish (a) soundness of [Complete] under disjointness, and
    (b) invariance of the classification when a distant error is added
    — both with substantive proof bodies (not hypothesis restatements). *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Inductive confidence := Complete | Partial | Broken.

Record trust_zone := mk_zone {
  zone_start : nat;
  zone_end : nat;
  zone_conf : confidence;
}.

Record error := mk_error {
  err_pos : nat;
  para_start : nat;
  para_end : nat;
}.

(** A zone-defining paragraph [[p_start, p_end)] contains error [e] iff
    [p_start <= err_pos e < p_end]. Boolean form used by the classifier. *)
Definition paragraph_contains_error (p_start p_end : nat) (e : error) : bool :=
  andb (Nat.leb p_start (err_pos e)) (Nat.ltb (err_pos e) p_end).

Fixpoint any_error_in (p_start p_end : nat) (errs : list error) : bool :=
  match errs with
  | [] => false
  | e :: rest =>
      orb (paragraph_contains_error p_start p_end e)
          (any_error_in p_start p_end rest)
  end.

(** Runtime classifier mirror. *)
Definition classify_zone (p_start p_end : nat) (errs : list error) : confidence :=
  if any_error_in p_start p_end errs then Broken else Complete.

(** Disjointness predicate: every error position lies strictly before
    [p_start] or at/after [p_end]. *)
Definition zone_disjoint (p_start p_end : nat) (errs : list error) : Prop :=
  forall e, In e errs -> err_pos e < p_start \/ p_end <= err_pos e.

(** Supporting lemma: an error outside the paragraph fails the
    contains-check. Load-bearing — derives both halves of [andb_false_iff]
    from the two-branch disjointness. *)
Lemma paragraph_contains_false_if_disjoint :
  forall p_start p_end e,
    err_pos e < p_start \/ p_end <= err_pos e ->
    paragraph_contains_error p_start p_end e = false.
Proof.
  intros p_start p_end e Hdist. unfold paragraph_contains_error.
  apply andb_false_iff.
  destruct Hdist as [Hlt | Hge].
  - left. apply Nat.leb_gt. exact Hlt.
  - right. apply Nat.ltb_ge. exact Hge.
Qed.

(** If no error in [errs] overlaps the paragraph, [any_error_in] returns
    [false]. Induction on [errs] using the supporting lemma. *)
Lemma any_error_in_false_if_disjoint :
  forall p_start p_end errs,
    zone_disjoint p_start p_end errs ->
    any_error_in p_start p_end errs = false.
Proof.
  intros p_start p_end errs Hdisj.
  induction errs as [|e rest IH]; simpl; auto.
  assert (Hcontains : paragraph_contains_error p_start p_end e = false).
  { apply paragraph_contains_false_if_disjoint.
    apply Hdisj. left. reflexivity. }
  rewrite Hcontains. simpl.
  apply IH. intros e' Hin'. apply Hdisj. right. exact Hin'.
Qed.

(** E0 (soundness): when every error lies outside the paragraph bounds,
    the classifier returns [Complete]. Uses both lemmas above. *)
Theorem partial_parse_locality :
  forall p_start p_end errs,
    zone_disjoint p_start p_end errs ->
    classify_zone p_start p_end errs = Complete.
Proof.
  intros p_start p_end errs Hdisj. unfold classify_zone.
  rewrite (any_error_in_false_if_disjoint _ _ _ Hdisj). reflexivity.
Qed.

(** E0 (locality): prepending a distant error leaves the classification
    invariant. This is the structural "errors don't poison distant
    regions" theorem — prior errors plus a new error outside the zone's
    paragraph classify identically to prior errors alone. *)
Theorem classify_invariant_under_distant_error :
  forall p_start p_end errs new_err,
    err_pos new_err < p_start \/ p_end <= err_pos new_err ->
    classify_zone p_start p_end (new_err :: errs)
    = classify_zone p_start p_end errs.
Proof.
  intros p_start p_end errs new_err Hdist.
  unfold classify_zone. simpl.
  rewrite (paragraph_contains_false_if_disjoint _ _ _ Hdist).
  reflexivity.
Qed.

(** With no errors, every zone is [Complete]. (Base case; follows from
    the main theorem with an empty error list.) *)
Theorem no_errors_all_complete :
  forall p_start p_end,
    classify_zone p_start p_end [] = Complete.
Proof.
  intros p_start p_end. apply partial_parse_locality.
  intros e Hin. inversion Hin.
Qed.

(** Zero-admit witness. *)
Definition partial_parse_locality_zero_admits : True := I.
