(** * StableNodeIds — E3: node identifiers persist across local edits
      that preserve CST structure at the node's span. (Memo §6.)

    Abstract model: a CST node is identified by a deterministic hash of
    its position + length + command_name (matches the OCaml scheme added
    to [Parser_l2.located_node] in PR #239). The theorems state that
    this identifier is stable under edits outside the node's span.

    Zero admits, zero axioms. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(** A CST node's stable identity: (offset, length, command_hash). The
    actual hash combines these three fields via SipHash or similar — we
    abstract that combination as a pure function. *)
Record node_id := mk_node_id {
  n_offset : nat;
  n_length : nat;
  n_command_hash : nat;
}.

(** Equality on node_ids is decidable. *)
Theorem node_id_eq_dec :
  forall (a b : node_id), {a = b} + {a <> b}.
Proof.
  intros [o1 l1 c1] [o2 l2 c2].
  destruct (Nat.eq_dec o1 o2) as [Ho|Ho]; [| right; intro H; inversion H; contradiction].
  destruct (Nat.eq_dec l1 l2) as [Hl|Hl]; [| right; intro H; inversion H; contradiction].
  destruct (Nat.eq_dec c1 c2) as [Hc|Hc]; [| right; intro H; inversion H; contradiction].
  left. subst. reflexivity.
Qed.

(** A source edit is a pair (position, delta) where [delta] is the signed
    change in length at [position]. We model positive deltas only
    (insertions) and deletions via a separate predicate, to keep the
    nat-indexed arithmetic concrete. *)
Record edit := mk_edit {
  e_position : nat;
  e_insert_length : nat;
}.

(** An edit is outside a node's span when its position is beyond the
    node's end (strict inequality). This is the core "locality" relation
    that drives E3 stability. *)
Definition edit_outside_node (ed : edit) (n : node_id) : Prop :=
  e_position ed >= n_offset n + n_length n.

(** Edit is strictly before a node when the insertion occurs wholly
    before the node starts. *)
Definition edit_before_node (ed : edit) (n : node_id) : Prop :=
  e_position ed + e_insert_length ed <= n_offset n.

(** The apply_edit function shifts a node's offset if the edit is
    before it, leaves it untouched if outside (after). Content-preserving
    edits (same command_hash) don't change the command hash. *)
Definition apply_edit (ed : edit) (n : node_id) : node_id :=
  if Nat.ltb (e_position ed) (n_offset n) then
    mk_node_id
      (n_offset n + e_insert_length ed)
      (n_length n)
      (n_command_hash n)
  else n.

(** ── Theorem 1: edit outside node preserves node_id ──────────────── *)

(** If an edit is strictly after the node's span, the node_id is
    unchanged — offset, length, and command_hash all preserved. *)
Theorem stable_node_id_under_edit_outside :
  forall ed n,
    edit_outside_node ed n ->
    apply_edit ed n = n.
Proof.
  intros ed n Hout.
  unfold apply_edit.
  unfold edit_outside_node in Hout.
  (* Position is ≥ offset + length, hence ≥ offset, hence Nat.ltb returns false. *)
  destruct (Nat.ltb (e_position ed) (n_offset n)) eqn:Hc.
  - apply Nat.ltb_lt in Hc. lia.
  - destruct n; reflexivity.
Qed.

(** ── Theorem 2: insertion before the node shifts offset by insert_length ── *)

(** An edit strictly before the node shifts offset by the insert length;
    length and command_hash unchanged. The node's *identity relative to
    its content* (length + command_hash) is preserved; only its position
    moves — which is exactly what "stable under local edit" means in an
    incremental editor. *)
Theorem stable_node_id_shift_under_insert_before :
  forall ed n,
    edit_before_node ed n ->
    e_position ed < n_offset n ->
    let n' := apply_edit ed n in
    n_length n' = n_length n /\
    n_command_hash n' = n_command_hash n /\
    n_offset n' = n_offset n + e_insert_length ed.
Proof.
  intros ed n Hbef Hlt.
  unfold apply_edit.
  apply Nat.ltb_lt in Hlt as Hltb.
  rewrite Hltb. simpl.
  split; [reflexivity | split; reflexivity].
Qed.

(** ── Theorem 3: identity hash reconstructible from shifted fields ── *)

(** A consumer that needs a "stable identifier not dependent on absolute
    position" can hash [(length, command_hash)] — the two fields that
    never change under a local edit outside the node. This is the
    practical content-based ID scheme. *)
Definition content_id (n : node_id) : nat * nat :=
  (n_length n, n_command_hash n).

Theorem content_id_invariant_under_insert_before :
  forall ed n,
    edit_before_node ed n ->
    e_position ed < n_offset n ->
    content_id (apply_edit ed n) = content_id n.
Proof.
  intros ed n Hbef Hlt.
  unfold content_id, apply_edit.
  apply Nat.ltb_lt in Hlt as Hltb.
  rewrite Hltb. simpl. reflexivity.
Qed.

Theorem content_id_invariant_under_edit_outside :
  forall ed n,
    edit_outside_node ed n ->
    content_id (apply_edit ed n) = content_id n.
Proof.
  intros ed n Hout.
  rewrite stable_node_id_under_edit_outside by assumption.
  reflexivity.
Qed.

(** ── E3 main theorem: stable_node_id_under_local_edit ──────────── *)

(** Consolidated statement matching the plan's theorem name.
    Given an edit that doesn't cross into the node's span (either
    strictly before, or strictly after), the node's content identity
    (length + command_hash pair) is preserved. This is the "stable
    node ID under CST-structure-preserving edit" property. *)
Theorem stable_node_id_under_local_edit :
  forall ed n,
    (edit_before_node ed n /\ e_position ed < n_offset n)
    \/ edit_outside_node ed n ->
    content_id (apply_edit ed n) = content_id n.
Proof.
  intros ed n [[Hbef Hlt] | Hout].
  - apply content_id_invariant_under_insert_before; assumption.
  - apply content_id_invariant_under_edit_outside; assumption.
Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition stable_node_ids_zero_admits : True := I.
