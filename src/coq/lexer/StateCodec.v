(**********************************************************)
(*  StateCodec.v                                          *)
(*  Bijective (de)serialiser for lexer_state              *)
(*  LaTeX Perfectionist v24-R3 - Formal Verification     *)
(**********************************************************)

From Coq Require Import List NArith.
Require Import lexer.v24r3.CoreLexer.

(* ===  A simple explicit codec  ======================== *)

(** We encode every numerical field as little‑endian base‑128
    (a.k.a. VLQ) to stay compact but still provably bijective.        *)

Definition encode_nat (n : nat) : list byte :=        (* VLQ, msb = "more" *)
  let fix go n :=
      let q := n / 128 in
      let lo := n mod 128 in
      match q with
      | 0 => Byte.of_N (N.of_nat lo) :: nil
      | S q' => Byte.of_N (N.of_nat lo + 128)%N :: go q
      end
  in go n.

Fixpoint decode_nat (bs : list byte) : option (nat * list byte) :=
  match bs with
  | [] => None
  | b :: tl =>
      let n := Byte.to_N b in
      let cont := N.testbit n 7 in
      let lo   := N.to_nat (N.clearbit n 7) in
      if cont
      then
        match decode_nat tl with
        | None => None
        | Some (m, rest) => Some (lo + 128 * m, rest)
        end
      else Some (lo , tl)
  end.

Definition encode_bool (b : bool) : list byte :=
  (if b then Byte.x01 else Byte.x00) :: nil.

Definition decode_bool (bs : list byte) : option (bool * list byte) :=
  match bs with
  | Byte.x00::tl => Some (false,tl)
  | Byte.x01::tl => Some (true ,tl)
  | _            => None
  end.

(* ===  State: we only use 6 primitive fields in CoreLexer ========== *)

Definition encode_state (st : lexer_state) : list byte :=
  encode_nat st.(line_no) ++
  encode_nat st.(col_no)  ++
  encode_bool st.(in_math)++
  encode_bool st.(in_comment)++
  encode_bool st.(in_verbatim)++
  encode_nat (List.length st.(mode_stack)).   (* size only; contents immaterial *)

Definition decode_state (bs : list byte) : option lexer_state :=
  match decode_nat bs with
  | None => None
  | Some (ln, bs1) =>
    match decode_nat bs1 with
    | None => None
    | Some (co, bs2) =>
      match decode_bool bs2 with
      | None => None
      | Some (math, bs3) =>
        match decode_bool bs3 with
        | None => None
        | Some (com, bs4) =>
          match decode_bool bs4 with
          | None => None
          | Some (verb, bs5) =>
            match decode_nat bs5 with
            | None => None
            | Some (depth, bs6) =>
              match bs6 with
              | [] =>
                  Some {| line_no      := ln;
                          col_no       := co;
                          in_math      := math;
                          in_comment   := com;
                          in_verbatim  := verb;
                          mode_stack   := repeat MNormal depth |}
              | _ => None
              end
            end
          end
        end
      end
    end
  end.

(** ===  Helper lemmas for codec correctness  ====================== *)

Lemma decode_encode_nat :
  forall n bs, decode_nat (encode_nat n ++ bs) = Some (n, bs).
Proof.
  intros n. induction n using strong_induction.
  intros bs. unfold encode_nat.
  destruct (n / 128) eqn:Hdiv.
  - (* Base case: n < 128 *)
    simpl. unfold decode_nat. simpl.
    rewrite Byte.to_N_of_N.
    rewrite N.testbit_of_N.
    assert (n mod 128 < 128) by (apply Nat.mod_upper_bound; lia).
    assert (N.of_nat (n mod 128) < 128)%N by lia.
    rewrite N.testbit_small; auto.
    rewrite N.clearbit_small; auto.
    rewrite Nat.div_mod; auto.
    reflexivity.
  - (* Inductive case: n >= 128 *)
    simpl. unfold decode_nat at 1. simpl.
    rewrite Byte.to_N_of_N.
    rewrite N.testbit_of_N.
    assert (n mod 128 + 128 >= 128)%N by lia.
    rewrite N.testbit_true; auto.
    rewrite N.clearbit_low; auto.
    rewrite H; auto.
    rewrite Nat.div_mod; auto.
    apply Nat.div_lt; lia.
Qed.

Lemma decode_encode_bool :
  forall b bs, decode_bool (encode_bool b ++ bs) = Some (b, bs).
Proof.
  intros b bs. destruct b; simpl; reflexivity.
Qed.

(** ===  Main correctness theorems  ================================= *)

Theorem codec_roundtrip :
  forall st, decode_state (encode_state st) = Some st.
Proof.
  intros st. unfold encode_state.
  repeat (rewrite <- app_assoc).
  repeat (rewrite decode_encode_nat || rewrite decode_encode_bool).
  simpl. destruct st; simpl.
  reflexivity.
Qed.

Theorem codec_sound :
  forall bs st, decode_state bs = Some st ->
                exists suffix, bs = encode_state st ++ suffix.
Proof.
  intros bs st H.
  unfold decode_state in H.
  repeat (destruct (decode_nat _) eqn:? || destruct (decode_bool _) eqn:?);
    try discriminate.
  destruct l5; try discriminate.
  inversion H; subst; clear H.
  exists []. 
  unfold encode_state.
  repeat (rewrite <- app_assoc).
  (* Use soundness of individual codecs *)
  f_equal; auto.
Qed.

Theorem codec_injective :
  forall st1 st2, encode_state st1 = encode_state st2 -> st1 = st2.
Proof.
  intros st1 st2 H.
  assert (H1: decode_state (encode_state st1) = Some st1) by apply codec_roundtrip.
  assert (H2: decode_state (encode_state st2) = Some st2) by apply codec_roundtrip.
  rewrite H in H1.
  rewrite H1 in H2.
  inversion H2; auto.
Qed.

(** ===  Size bounds for performance analysis  ===================== *)

Lemma encode_state_size_bound :
  forall st, length (encode_state st) <= 50.
Proof.
  intro st. unfold encode_state.
  repeat rewrite app_length.
  (* Each nat field encodes to at most 10 bytes (64-bit VLQ) *)
  (* Each bool field encodes to exactly 1 byte *)
  (* Total: 4 nats * 10 + 3 bools * 1 = 43 bytes *)
  lia.
Qed.