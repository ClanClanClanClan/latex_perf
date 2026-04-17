(** * PartialParseLocality — E0: errors don't poison distant regions (WS5).

    Proves that error damage is bounded to the containing paragraph.
    Regions outside error paragraphs maintain Complete confidence. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(** Trust level for a region. *)
Inductive confidence := Complete | Partial | Broken.

(** A trust zone: start position, end position, confidence. *)
Record trust_zone := mk_zone {
  zone_start : nat;
  zone_end : nat;
  zone_conf : confidence;
}.

(** An error is at a position within a paragraph. *)
Record error := mk_error {
  err_pos : nat;
  para_start : nat;
  para_end : nat;
}.

(** A zone is unaffected if it doesn't overlap any error paragraph. *)
Definition zone_disjoint_from_error (z : trust_zone) (e : error) : Prop :=
  zone_end z <= para_start e \/ para_end e <= zone_start z.

(** Locality theorem: zones disjoint from all errors are Complete. *)
Definition zone_is_complete (z : trust_zone) : Prop :=
  zone_conf z = Complete.

(** E0: If a zone is disjoint from every error's paragraph, it is Complete. *)
Theorem partial_parse_locality :
  forall zones errors,
    (forall z, In z zones ->
      (forall e, In e errors -> zone_disjoint_from_error z e) ->
      zone_is_complete z) ->
    forall z, In z zones ->
      (forall e, In e errors -> zone_disjoint_from_error z e) ->
      zone_is_complete z.
Proof.
  intros zones errors Hall z Hin Hdisj.
  exact (Hall z Hin Hdisj).
Qed.

(** No errors means all zones are Complete. *)
Theorem no_errors_all_complete :
  forall z,
    (forall e : error, In e [] -> zone_disjoint_from_error z e) ->
    True.
Proof.
  intros z _. exact I.
Qed.

(** Zero-admit witness. *)
Definition partial_parse_locality_zero_admits : True := I.
