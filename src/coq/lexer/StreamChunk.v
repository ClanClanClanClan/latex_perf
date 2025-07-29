(**********************************************************)
(*  StreamChunk.v                                         *)
(*  Primitive "lex a single chunk" layer                  *)
(*  LaTeX Perfectionist v24-R3 - Formal Verification     *)
(**********************************************************)

From Coq Require Import List String.
Import ListNotations.
Require Import lexer.v24r3.CoreLexer.   (* <- existing batch lexer *)

Record chunk : Type :=
  { c_state  : lexer_state;          (* starting state  *)
    c_bytes  : list byte             (* UTF‑8 bytes     *)
  }.

(* Run the reference lexer on one chunk. *)
Definition lex_chunk (ck : chunk) : list token * lexer_state :=
  lex_bytes ck.(c_state) ck.(c_bytes).

(* ===  Fundamental property: determinism  ========================== *)

Lemma lex_chunk_det :
  forall ck ts1 st1 ts2 st2,
    lex_chunk ck = (ts1,st1) ->
    lex_chunk ck = (ts2,st2) ->
    ts1 = ts2 /\ st1 = st2.
Proof.
  intros ck ts1 st1 ts2 st2 H1 H2.
  unfold lex_chunk in *.
  (* CoreLexer already provides a lemma for lex_bytes. *)
  eapply lex_bytes_det in H1; eauto.
Qed.

(* ===  Additional properties for incremental processing  =========== *)

Lemma lex_chunk_preserves_invariants :
  forall ck ts st,
    lex_chunk ck = (ts, st) ->
    valid_lexer_state ck.(c_state) ->
    valid_lexer_state st.
Proof.
  intros ck ts st H Hvalid.
  unfold lex_chunk in H.
  eapply lex_bytes_preserves_invariants; eauto.
Qed.

Lemma lex_chunk_tokens_well_formed :
  forall ck ts st,
    lex_chunk ck = (ts, st) ->
    Forall well_formed_token ts.
Proof.
  intros ck ts st H.
  unfold lex_chunk in H.
  eapply lex_bytes_tokens_well_formed; eauto.
Qed.

(* ===  Performance guarantees  ===================================== *)

Lemma lex_chunk_complexity_bound :
  forall ck ts st,
    lex_chunk ck = (ts, st) ->
    length ts <= 2 * length ck.(c_bytes).
Proof.
  intros ck ts st H.
  unfold lex_chunk in H.
  eapply lex_bytes_linear_bound; eauto.
Qed.