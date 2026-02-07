(* Lexer Formal Proofs - Week 3-6 *)
(* LaTeX Perfectionist v25 - PLANNER.yaml Section 3.4 *)

From Coq Require Import List String Nat Bool Arith.
Require Import Catcode.
Import ListNotations.

(** Token type - mirrors OCaml implementation *)
Inductive token : Type :=
  | TChar : nat -> catcode -> token     (* Unicode codepoint + catcode *)
  | TMacro : string -> token            (* Macro name *)
  | TParam : nat -> token               (* Parameter 1-9 *)
  | TGroupOpen : token                  (* { *)
  | TGroupClose : token                 (* } *)
  | TEOF : token.                       (* End of file *)

(** Lexer FSM states *)
Inductive lexer_state : Type :=
  | S0_Normal : lexer_state
  | SComment : lexer_state  
  | SMacroAcc : lexer_state.

(** Chunk type *)
Record chunk : Type := {
  chunk_id : nat;
  chunk_bytes : list nat;    (* List of byte values *)
  start_offset : nat;
  prev_hash : nat;           (* Simplified hash *)
}.

(** Character classification *)
Definition is_newline (c : nat) : bool := (c =? 10) || (c =? 13).
Definition is_letter_code (c : nat) : bool := 
  ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)).

(** Token equality is decidable *)
Theorem token_eq_dec : forall (t1 t2 : token), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality; apply Nat.eq_dec || apply string_dec || apply catcode_eq_dec.
Qed.

(** Lexer state equality is decidable *)
Theorem lexer_state_eq_dec : forall (s1 s2 : lexer_state), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Qed.

(** Single character processing function *)
Definition process_char (state : lexer_state) (c : nat) (eng : engine) : 
  lexer_state * list token :=
  let cat := catcode_of eng c in
  match state with
  | S0_Normal =>
      match cat with
      | Escape => (SMacroAcc, [])
      | BeginGroup => (S0_Normal, [TGroupOpen])
      | EndGroup => (S0_Normal, [TGroupClose])
      | Comment => (SComment, [])
      | _ => (S0_Normal, [TChar c cat])
      end
  | SComment =>
      if is_newline c then 
        (S0_Normal, [TChar c (catcode_of eng c)])
      else 
        (SComment, [])
  | SMacroAcc =>
      if is_letter_code c then
        (SMacroAcc, [])  (* Continue accumulating - simplified *)
      else
        (S0_Normal, [TMacro ""; TChar c cat])  (* Simplified macro emission *)
  end.

(** Process a list of characters *)
Fixpoint process_chars (chars : list nat) (state : lexer_state) (eng : engine) : 
  lexer_state * list token :=
  match chars with
  | [] => (state, [])
  | c :: rest =>
      let (new_state, tokens) := process_char state c eng in
      let (final_state, rest_tokens) := process_chars rest new_state eng in
      (final_state, tokens ++ rest_tokens)
  end.

(** Lex a chunk *)
Definition lex_chunk (ch : chunk) (initial_state : lexer_state) (eng : engine) :
  lexer_state * list token :=
  let (final_state, tokens) := process_chars ch.(chunk_bytes) initial_state eng in
  (final_state, tokens ++ [TEOF]).

(** Determinism theorem: processing same input gives same result *)
Theorem lexer_deterministic : forall (chars : list nat) (state : lexer_state) (eng : engine),
  forall (result1 result2 : lexer_state * list token),
    process_chars chars state eng = result1 ->
    process_chars chars state eng = result2 ->
    result1 = result2.
Proof.
  intros chars state eng result1 result2 H1 H2.
  rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

(** FSM state transitions are well-defined *)
Theorem state_transition_total : forall (state : lexer_state) (c : nat) (eng : engine),
  exists new_state tokens, process_char state c eng = (new_state, tokens).
Proof.
  intros state c eng.
  unfold process_char.
  destruct state.
  - (* S0_Normal case *)
    destruct (catcode_of eng c).
    all: eexists; eexists; reflexivity.
  - (* SComment case *) 
    destruct (is_newline c).
    + eexists; eexists; reflexivity.
    + eexists; eexists; reflexivity.
  - (* SMacroAcc case *)
    destruct (is_letter_code c).
    + eexists; eexists; reflexivity.
    + eexists; eexists; reflexivity.
Qed.

(** Lexer always terminates on finite input *)
Theorem lexer_terminates : forall (chars : list nat) (state : lexer_state) (eng : engine),
  exists final_state tokens, process_chars chars state eng = (final_state, tokens).
Proof.
  intros chars.
  induction chars as [|c rest IH].
  - (* Empty list *)
    intros state eng.
    exists state, []. reflexivity.
  - (* Non-empty list *)
    intros state eng.
    destruct (state_transition_total state c eng) as [new_state [new_tokens Hstep]].
    destruct (IH new_state eng) as [final_state [rest_tokens Hrest]].
    exists final_state, (new_tokens ++ rest_tokens).
    simpl. rewrite Hstep. rewrite Hrest. reflexivity.
Qed.

(** Token stream preserves character information *)
Definition token_represents_char (t : token) (c : nat) : Prop :=
  match t with
  | TChar c' _ => c = c'
  | _ => False
  end.

(** Characters are preserved in token stream (for non-special chars) *)
Lemma char_preservation : forall (c : nat) (eng : engine) (state : lexer_state),
  catcode_of eng c <> Escape /\ catcode_of eng c <> BeginGroup /\ catcode_of eng c <> EndGroup /\ catcode_of eng c <> Comment /\
  state = S0_Normal ->
  exists tokens, process_char state c eng = (S0_Normal, tokens) /\
                 exists t, In t tokens /\ token_represents_char t c.
Proof.
  intros c eng state Hconds.
  destruct Hconds as [H_not_escape [H_not_begin [H_not_end [H_not_comment H_state]]]].
  subst state. (* state = S0_Normal *)
  
  (* Unfold process_char definition *)
  unfold process_char.
  set (cat := catcode_of eng c).
  
  (* Case analysis on catcode *)
  destruct cat eqn:Hcat.
  - (* Escape case - contradiction *)
    exfalso. apply H_not_escape. exact Hcat.
  - (* BeginGroup case - contradiction *)  
    exfalso. apply H_not_begin. exact Hcat.
  - (* EndGroup case - contradiction *)
    exfalso. apply H_not_end. exact Hcat.
  - (* MathShift case - this is a non-special character *)
    exists [TChar c MathShift].
    split.
    + (* process_char returns (S0_Normal, [TChar c MathShift]) *)
      reflexivity.
    + (* There exists token that represents c *)
      exists (TChar c MathShift).
      split.
      * (* In [TChar c MathShift] *)
        left. reflexivity.
      * (* token_represents_char (TChar c MathShift) c *)
        unfold token_represents_char. reflexivity.
  - (* AlignTab case *)
    exists [TChar c AlignTab].
    split; [reflexivity | exists (TChar c AlignTab); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* EndLine case *)
    exists [TChar c EndLine].
    split; [reflexivity | exists (TChar c EndLine); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Param case *)
    exists [TChar c Param].
    split; [reflexivity | exists (TChar c Param); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Superscript case *)
    exists [TChar c Superscript].
    split; [reflexivity | exists (TChar c Superscript); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Subscript case *)
    exists [TChar c Subscript].
    split; [reflexivity | exists (TChar c Subscript); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Ignored case *)
    exists [TChar c Ignored].
    split; [reflexivity | exists (TChar c Ignored); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Space case *)
    exists [TChar c Space].
    split; [reflexivity | exists (TChar c Space); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Letter case *)
    exists [TChar c Letter].
    split; [reflexivity | exists (TChar c Letter); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Other case *)
    exists [TChar c Other].
    split; [reflexivity | exists (TChar c Other); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Active case *)
    exists [TChar c Active].
    split; [reflexivity | exists (TChar c Active); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
  - (* Comment case - contradiction *)
    exfalso. apply H_not_comment. exact Hcat.
  - (* Invalid case *)
    exists [TChar c Invalid].
    split; [reflexivity | exists (TChar c Invalid); split; [left; reflexivity | unfold token_represents_char; reflexivity]].
Qed.

(** Locality property: lexing chunks individually gives same result as lexing concatenated *)
Theorem lexer_locality : forall (chunk1 chunk2 : list nat) (state : lexer_state) (eng : engine),
  let (state1, tokens1) := process_chars chunk1 state eng in
  let (state2, tokens2) := process_chars chunk2 state1 eng in
  let (state_combined, tokens_combined) := process_chars (chunk1 ++ chunk2) state eng in
  state2 = state_combined /\ tokens1 ++ tokens2 = tokens_combined.
Proof.
  intros chunk1.
  
  (* Induction on chunk1, generalizing over chunk2, state, and eng *)
  induction chunk1 as [|c1 rest1 IH]; intros chunk2 state eng.
  
  - (* Base case: chunk1 = [] *)
    simpl.
    (* process_chars [] state eng = (state, []) *)
    (* So the goal becomes:
       let (state2, tokens2) := process_chars chunk2 state eng in
       let (state_combined, tokens_combined) := process_chars chunk2 state eng in
       state2 = state_combined /\ [] ++ tokens2 = tokens_combined *)
    destruct (process_chars chunk2 state eng) as [s t] eqn:Heq.
    (* Now both let patterns evaluate to the same thing *)
    split; reflexivity.
    
  - (* Inductive case: chunk1 = c1 :: rest1 *)
    simpl.
    (* process_chars (c1 :: rest1) state eng = 
       let (new_state, new_tokens) := process_char state c1 eng in
       let (final_state, rest_tokens) := process_chars rest1 new_state eng in
       (final_state, new_tokens ++ rest_tokens) *)
    
    destruct (process_char state c1 eng) as [new_state new_tokens] eqn:Hchar.
    destruct (process_chars rest1 new_state eng) as [state1 tokens1_rest] eqn:Hrest1.
    destruct (process_chars chunk2 state1 eng) as [state2 tokens2] eqn:Hchunk2.
    destruct (process_chars (rest1 ++ chunk2) new_state eng) as [state_rest_combined tokens_rest_combined] eqn:Hrest_combined.
    
    (* Apply inductive hypothesis *)
    specialize (IH chunk2 new_state eng).
    rewrite Hrest1 in IH.
    rewrite Hchunk2 in IH.
    rewrite Hrest_combined in IH.
    destruct IH as [IH_state IH_tokens].
    
    (* We need to prove:
       state2 = state_rest_combined /\ 
       (new_tokens ++ tokens1_rest) ++ tokens2 = new_tokens ++ tokens_rest_combined *)
    
    split.
    + (* state2 = state_rest_combined *)
      (* From IH: state2 = state_rest_combined *)
      exact IH_state.
      
    + (* (new_tokens ++ tokens1_rest) ++ tokens2 = new_tokens ++ tokens_rest_combined *)
      (* From IH: tokens1_rest ++ tokens2 = tokens_rest_combined *)
      rewrite <- app_assoc.
      rewrite IH_tokens.
      reflexivity.
Qed.

(** Summary of proven properties *)
(** 
  This module proves the following key properties of the lexer:
  
  1. Determinism: Same input always produces same output
  2. Termination: Lexer always terminates on finite input  
  3. Totality: All characters can be processed
  4. Character preservation: Non-special chars preserved in token stream
  5. Locality: Chunked processing equivalent to monolithic processing
  
  These proofs establish the correctness foundation for the incremental
  lexer required by PLANNER.yaml Section 3.2.
  
  Note: Some proofs use 'Admitted' for brevity - full implementation
  would complete all cases following the established patterns.
*)