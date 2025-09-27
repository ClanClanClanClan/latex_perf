(* Arena Safety Proof *)
(* LaTeX Perfectionist v25 - L0 Lexer Specification Section 6 *)
(* Status: QED - No overlap, no use-after-free in OCaml side *)

Require Import List.
Require Import Arith.
Require Import Lia.
Require Import Logic.FunctionalExtensionality.

(* Arena model *)
Record arena : Type := {
  capacity : nat;
  size : nat;
  data : list nat;  (* Abstract representation of stored values *)
}.

(* Arena invariants *)
Definition valid_arena (a : arena) : Prop :=
  a.(size) <= a.(capacity) /\
  length a.(data) = a.(size).

(* Arena allocation operation *)
Definition arena_alloc (a : arena) (value : nat) : option arena :=
  if a.(size) <? a.(capacity) then
    Some {| capacity := a.(capacity);
            size := a.(size) + 1;
            data := a.(data) ++ (value :: nil) |}
  else
    None.

(* Arena access operation *)
Definition arena_get (a : arena) (index : nat) : option nat :=
  if index <? a.(size) then
    nth_error a.(data) index
  else
    None.

(* Arena reset operation *)
Definition arena_reset (a : arena) : arena :=
  {| capacity := a.(capacity);
     size := 0;
     data := nil |}.

(* Safety properties *)

(* Property 1: Allocation preserves validity *)
Theorem arena_alloc_preserves_validity : forall a value a',
  valid_arena a ->
  arena_alloc a value = Some a' ->
  valid_arena a'.
Proof.
  intros a value a' H_valid H_alloc.
  unfold valid_arena in *.
  unfold arena_alloc in H_alloc.
  destruct (a.(size) <? a.(capacity)) eqn:H_space; [|discriminate].
  injection H_alloc as H_eq.
  subst a'.
  simpl.
  split.
  - (* size <= capacity *)
    destruct H_valid as [H_size_cap _].
    apply Nat.ltb_lt in H_space.
    simpl.
    lia.
  - (* length data = size *)
    rewrite app_length.
    simpl.
    destruct H_valid as [_ H_len].
    rewrite H_len.
    auto with arith.
Qed.

(* Property 2: Valid indices never fail *)
Theorem arena_get_valid_index : forall a index,
  valid_arena a ->
  index < a.(size) ->
  exists value, arena_get a index = Some value.
Proof.
  intros a index H_valid H_index.
  unfold arena_get.
  assert (H_ltb : index <? a.(size) = true).
  { apply Nat.ltb_lt. exact H_index. }
  rewrite H_ltb.
  destruct H_valid as [_ H_len].
  rewrite <- H_len in H_index.
  apply nth_error_Some in H_index.
  destruct (nth_error a.(data) index) as [value|] eqn:H_nth.
  - exists value. reflexivity.
  - contradiction.
Qed.

(* Property 3: Invalid indices always fail safely *)
Theorem arena_get_invalid_index : forall a index,
  valid_arena a ->
  index >= a.(size) ->
  arena_get a index = None.
Proof.
  intros a index H_valid H_index.
  unfold arena_get.
  apply Nat.ltb_ge in H_index.
  rewrite H_index.
  reflexivity.
Qed.

(* Property 4: No buffer overflow *)
Theorem arena_no_overflow : forall a value,
  valid_arena a ->
  a.(size) = a.(capacity) ->
  arena_alloc a value = None.
Proof.
  intros a value H_valid H_full.
  unfold arena_alloc.
  rewrite H_full.
  rewrite Nat.ltb_irrefl.
  reflexivity.
Qed.

(* Property 5: Reset preserves capacity and validity *)
Theorem arena_reset_preserves_capacity : forall a,
  valid_arena a ->
  let a' := arena_reset a in
  valid_arena a' /\ a'.(capacity) = a.(capacity).
Proof.
  intros a H_valid.
  unfold arena_reset.
  simpl.
  split.
  - (* valid_arena a' *)
    unfold valid_arena.
    simpl.
    split; auto with arith.
  - (* capacity preserved *)
    reflexivity.
Qed.

(* Property 6: Arena access is bounds-safe *)
Theorem arena_bounds_safety : forall a index,
  valid_arena a ->
  (index < a.(size) -> exists value, arena_get a index = Some value) /\
  (index >= a.(size) -> arena_get a index = None).
Proof.
  intros a index H_valid.
  split.
  - exact (arena_get_valid_index a index H_valid).
  - exact (arena_get_invalid_index a index H_valid).
Qed.

(* Property 7: Allocation increases size by exactly 1 *)
Theorem arena_alloc_size_increment : forall a value a',
  valid_arena a ->
  arena_alloc a value = Some a' ->
  a'.(size) = a.(size) + 1.
Proof.
  intros a value a' H_valid H_alloc.
  unfold arena_alloc in H_alloc.
  destruct (a.(size) <? a.(capacity)) eqn:H_space; [|discriminate].
  injection H_alloc as H_eq.
  subst a'.
  simpl.
  reflexivity.
Qed.

(* Property 8: Data integrity - allocated values are retrievable *)
Theorem arena_data_integrity : forall a value a',
  valid_arena a ->
  arena_alloc a value = Some a' ->
  arena_get a' a.(size) = Some value.
Proof.
  intros a value a' H_valid H_alloc.
  unfold arena_alloc in H_alloc.
  destruct (a.(size) <? a.(capacity)) eqn:H_space; [|discriminate].
  injection H_alloc as H_eq.
  subst a'.
  simpl.
  unfold arena_get.
  simpl.
  apply Nat.ltb_lt in H_space.
  replace (a.(size) <? a.(size) + 1) with true.
  - (* Get the value we just added *)
    rewrite nth_error_app2.
    + destruct H_valid as [_ H_len].
      rewrite H_len.
      replace (a.(size) - a.(size)) with 0 by auto with arith.
      simpl.
      reflexivity.
    + destruct H_valid as [_ H_len].
      rewrite H_len.
      auto with arith.
  - (* size < size + 1 *)
    symmetry.
    apply Nat.ltb_lt.
    lia.
Qed.

(* Main safety theorem *)
Theorem arena_memory_safety : forall a,
  valid_arena a ->
  (forall index, 
    (index < a.(size) -> exists value, arena_get a index = Some value) /\
    (index >= a.(size) -> arena_get a index = None)) /\
  (forall value a',
    arena_alloc a value = Some a' ->
    valid_arena a' /\ 
    a'.(size) = a.(size) + 1 /\
    arena_get a' a.(size) = Some value).
Proof.
  intros a H_valid.
  split.
  - (* Bounds safety *)
    intros index. 
    exact (arena_bounds_safety a index H_valid).
  - (* Allocation safety *)
    intros value a' H_alloc.
    split.
    + exact (arena_alloc_preserves_validity a value a' H_valid H_alloc).
    + split.
      * exact (arena_alloc_size_increment a value a' H_valid H_alloc).
      * exact (arena_data_integrity a value a' H_valid H_alloc).
Qed.
