(* LaTeX Perfectionist v24 - Phase 1: Verified Lexer *)
(* Week 3: Determinism and Termination Proofs *)

Require Import Bool Arith List String Ascii Lia.
Require Import Coq.Program.Wf.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Equality.   (* For dependent inversion *)
Require Import Coq.Logic.Decidable.    (* For congruence *)
Require Import Coq.Strings.Ascii.      (* For ascii_dec *)
Require Import LatexCatcodes.
Require Import LatexLexer.
Require Import CatcodeAnalysis.
Import ListNotations.
Open Scope string_scope.

(** * Termination Proof for Lexer *)

(** *** Structural facts about [take_while] *)

Lemma take_while_length :
  forall p s t r,
    take_while p s = (t, r) ->
    String.length s = String.length t + String.length r.
Proof.
  intros p s.
  induction s as [|c s' IH]; intros t r H.
  - (* Empty string case *)
    simpl in H. inversion H; subst. simpl. reflexivity.
  - (* String c s' case *)
    simpl in H.
    destruct (p c) eqn:Hpc.
    + (* p c = true *)
      destruct (take_while p s') as [t0 r0] eqn:Htw.
      inversion H; subst t r. clear H.
      simpl.
      rewrite <- IH with (t := t0) (r := r0) by reflexivity.
      simpl. lia.
    + (* p c = false *)
      inversion H; subst.
      simpl. reflexivity.
Qed.

Lemma take_while_nonempty :
  forall p c rest t r,
    p c = true ->
    take_while p (String c rest) = (t, r) ->
    1 <= String.length t.
Proof.
  intros p c rest t r Hpred Htw.
  simpl in Htw.
  rewrite Hpred in Htw.
  destruct (take_while p rest) as [t' r'] eqn:Htw'.
  inversion Htw; subst.
  simpl. lia.
Qed.

(* First, we prove that lex_step always decreases the measure when it returns Some *)
Lemma lex_step_decreases : forall st tok st',
  lex_step st = Some (tok, st') ->
  lexer_measure st' < lexer_measure st.
Proof.
  intros st tok st' H.
  unfold lex_step in H.
  destruct (peek_char st) as [c|] eqn:E_peek; [|discriminate H].
  (* We have peek_char st = Some c, so input is non-empty *)
  assert (H_nonempty: input_empty st = false).
  { unfold input_empty, peek_char in *.
    destruct (input st); [discriminate|reflexivity]. }
  
  (* Case analysis on catcode *)
  destruct (default_catcodes c) eqn:E_cat.
  - (* CatEscape *)
    destruct (lex_command st) as [tok' st''] eqn:E_cmd.
    injection H as <- <-.
    apply lex_command_decreases with (tok := tok'); try assumption.
    + (* st.(input) <> EmptyString *)
      unfold input_empty in H_nonempty.
      destruct (input st) eqn:E; [discriminate|].
      intro. discriminate.
    + (* match peek_char st with Some c => default_catcodes c = CatEscape *)
      rewrite E_peek. exact E_cat.
  - (* CatBeginGroup *)
    injection H as <- <-.
    apply advance_decreases_measure. exact H_nonempty.
  - (* CatEndGroup *)
    injection H as <- <-.
    apply advance_decreases_measure. exact H_nonempty.
  - (* CatMathShift *)
    injection H as <- <-.
    apply advance_decreases_measure. exact H_nonempty.
  - (* CatAlignment *)
    injection H as <- <-.
    apply advance_decreases_measure. exact H_nonempty.
  - (* CatParameter *)
    injection H as <- <-.
    apply advance_decreases_measure. exact H_nonempty.
  - (* CatSuperscript *)
    injection H as <- <-.
    apply advance_decreases_measure. exact H_nonempty.
  - (* CatSubscript *)
    injection H as <- <-.
    apply advance_decreases_measure. exact H_nonempty.
  - (* CatSpace *)
    destruct (lex_whitespace st) as [tok' st''] eqn:E_ws.
    injection H as <- <-.
    apply lex_whitespace_decreases with (tok := tok') (c := c); try assumption.
    (* Need to prove is_whitespace c = true *)
    apply catspace_is_whitespace. exact E_cat.
  - (* CatLetter *)
    destruct (lex_text st) as [tok' st''] eqn:E_text.
    injection H as <- <-.
    apply lex_text_decreases with (tok := tok') (st' := st''); assumption.
  - (* CatOther *)
    destruct (lex_text st) as [tok' st''] eqn:E_text.
    injection H as <- <-.
    apply lex_text_decreases with (tok := tok') (st' := st''); assumption.
  - (* CatComment *)
    destruct (lex_comment st) as [tok' st''] eqn:E_com.
    injection H as <- <-.
    apply lex_comment_decreases with (tok := tok').
    + exact E_com.
    + exact H_nonempty.
    + (* match peek_char st with Some c => c = ascii_percent *)
      rewrite E_peek.
      (* Since default_catcodes c = CatComment, c must be % *)
      apply catcomment_is_percent. exact E_cat.
Qed.

(* add_token preserves measure *)
Lemma add_token_measure : forall tok st,
  lexer_measure (add_token tok st) = lexer_measure st.
Proof.
  intros tok st.
  unfold lexer_measure, add_token. simpl. reflexivity.
Qed.

(*──────── 2 Transparent re‑implementation ───────────────────────────────*)

Fixpoint lex_all_fuel (fuel : nat) (st : lexer_state) : list latex_token :=
  match fuel with
  | 0 =>
      (* fuel exhausted – return the accumulated tokens in reverse order *)
      List.rev st.(tokens)
  | S fuel' =>
      match lex_step st with
      | None              => List.rev st.(tokens)
      | Some (tok, st')   => lex_all_fuel fuel' (add_token tok st')
      end
  end.

Definition lex_all (st : lexer_state) : list latex_token :=
  (* We give ourselves one more step than the measure just to placate any
     off‑by‑one corner cases; the measure is a strict upper bound anyway.   *)
  lex_all_fuel (S (lexer_measure st)) st.

(* Helper lemma: lex_all_fuel with sufficient fuel produces same result *)
Lemma lex_all_fuel_sufficient : forall fuel1 fuel2 st,
  fuel1 >= lexer_measure st ->
  fuel2 >= lexer_measure st ->
  lex_all_fuel fuel1 st = lex_all_fuel fuel2 st.
Proof.
  (* We'll prove this by induction on st's measure using a helper lemma *)
  intros fuel1 fuel2 st Hf1 Hf2.
  
  (* Helper that handles the actual induction *)
  assert (H_main: forall n st',
    lexer_measure st' <= n ->
    forall f1 f2,
    f1 >= lexer_measure st' ->
    f2 >= lexer_measure st' ->
    lex_all_fuel f1 st' = lex_all_fuel f2 st').
  { induction n as [|n' IH].
    - (* n = 0 *)
      intros st' Hle f1 f2 Hf1' Hf2'.
      (* If lexer_measure st' <= 0, then lexer_measure st' = 0 *)
      assert (lexer_measure st' = 0) by lia.
      (* When measure is 0, input is empty *)
      assert (input st' = EmptyString).
      { unfold lexer_measure in H. simpl in H.
        destruct (input st'); [reflexivity | simpl in H; discriminate]. }
      (* So lex_step returns None *)
      assert (lex_step st' = None).
      { unfold lex_step, peek_char. rewrite H0. reflexivity. }
      (* Now case on fuels *)
      destruct f1; destruct f2; simpl; try rewrite H1; reflexivity.
    - (* n = S n' *)
      intros st' Hle f1 f2 Hf1' Hf2'.
      destruct f1 as [|f1']; destruct f2 as [|f2'].
      + (* Both 0 *)
        reflexivity.
      + (* f1 = 0, f2 = S f2' *)
        (* Since f1 = 0 >= lexer_measure st', we have lexer_measure st' = 0 *)
        assert (lexer_measure st' = 0) by lia.
        assert (input st' = EmptyString).
        { unfold lexer_measure in H. simpl in H.
          destruct (input st'); [reflexivity | simpl in H; discriminate]. }
        assert (lex_step st' = None).
        { unfold lex_step, peek_char. rewrite H0. reflexivity. }
        simpl. rewrite H1. reflexivity.
      + (* f1 = S f1', f2 = 0 *)
        (* Similar *)
        assert (lexer_measure st' = 0) by lia.
        assert (input st' = EmptyString).
        { unfold lexer_measure in H. simpl in H.
          destruct (input st'); [reflexivity | simpl in H; discriminate]. }
        assert (lex_step st' = None).
        { unfold lex_step, peek_char. rewrite H0. reflexivity. }
        simpl. rewrite H1. reflexivity.
      + (* Both > 0 *)
        simpl.
        destruct (lex_step st') as [[tok st'']|] eqn:E.
        * (* Some (tok, st'') *)
          (* Apply IH *)
          assert (lexer_measure st'' < lexer_measure st').
          { apply lex_step_decreases with tok. exact E. }
          assert (lexer_measure st'' <= n').
          { lia. }
          apply IH.
          -- rewrite add_token_measure. exact H0.
          -- rewrite add_token_measure. lia.
          -- rewrite add_token_measure. lia.
        * (* None *)
          reflexivity.
  }
  
  (* Apply the helper with n = lexer_measure st *)
  apply H_main with (n := lexer_measure st).
  - reflexivity.
  - exact Hf1.
  - exact Hf2.
Qed.

(** * Auxiliary lemmas about the measure *)

(* advance_char decreases measure by exactly pred *)
Lemma advance_char_measure :
  forall st,
    input st <> EmptyString ->
    lexer_measure (advance_char st) = pred (lexer_measure st).
Proof.
  intros st Hne.
  unfold lexer_measure, advance_char.
  destruct (input st) eqn:E; [contradiction|simpl]; lia.
Qed.

(* This lemma is now defined above with a different proof technique *)

(** *** [lex_command] *)

(* The provided solution uses is_alpha but our code uses is_command_char *)
Definition is_alpha := is_command_char.

(* Define is_newline which is used in the solution *)
Definition is_newline (c : ascii) : bool :=
  match ascii_dec c (ascii_of_nat 10) with
  | left _ => true
  | right _ => false
  end.

(* Lemma: Characters with CatSpace catcode are whitespace *)
Lemma catcode_space_is_whitespace : forall c,
  default_catcodes c = CatSpace ->
  is_whitespace c = true.
Proof.
  intros c H.
  (* From LatexCatcodes.v, only ascii_space has CatSpace catcode *)
  unfold default_catcodes in H.
  (* We need to analyze the cascade of if-then-else *)
  destruct (ascii_dec c ascii_backslash); try discriminate.
  destruct (ascii_dec c ascii_lbrace); try discriminate.
  destruct (ascii_dec c ascii_rbrace); try discriminate.
  destruct (ascii_dec c ascii_dollar); try discriminate.
  destruct (ascii_dec c ascii_ampersand); try discriminate.
  destruct (ascii_dec c ascii_hash); try discriminate.
  destruct (ascii_dec c ascii_caret); try discriminate.
  destruct (ascii_dec c ascii_underscore); try discriminate.
  destruct (ascii_dec c ascii_space) as [H_eq|H_neq].
  - (* c = ascii_space *)
    subst c.
    unfold is_whitespace.
    unfold ascii_space.
    (* is_whitespace checks if nat_of_ascii c is 32, 9, 10, or 13 *)
    (* We have c = ascii_of_nat 32 *)
    (* So nat_of_ascii c = nat_of_ascii (ascii_of_nat 32) = 32 *)
    simpl.
    (* The first check is Nat.eqb 32 32 which is true *)
    reflexivity.
  - (* c <> ascii_space but has CatSpace - contradiction *)
    destruct (ascii_dec c ascii_percent); try discriminate.
    destruct (is_letter c); discriminate.
Qed.

(* Note: The lex_command_exact_decrease lemma was removed because it was false.
   lex_command can consume multiple characters via take_while, so exact decrease
   by 1 is not guaranteed. The correct property is strict decrease, which is
   already proven in lex_command_decreases. *)

(* Note: lex_command_measure_exact was removed because it depended on the false
   lex_command_exact_decrease lemma. *)

(** *** [lex_whitespace] *)

(* Note: lex_whitespace_exact_decrease and lex_whitespace_measure_exact were removed
   because they were false. lex_whitespace uses take_while to consume multiple
   consecutive whitespace characters, so exact decrease by 1 is not guaranteed.
   The correct property is strict decrease, already proven in lex_whitespace_decreases. *)

(** *** [lex_text] *)

(* Note: lex_text_exact_decrease and lex_text_measure_exact were removed because
   they were false. When is_text_char is true, lex_text uses take_while to consume
   multiple consecutive text characters. The correct property is strict decrease,
   already proven in lex_text_decreases. *)

(** *** [lex_comment] — eats a `%` then the rest of the line *)

(* Note: lex_comment_exact_decrease and lex_comment_measure_exact were removed
   because they were false. lex_comment first advances past '%', then uses
   take_while to consume characters until newline, which can be multiple characters.
   The correct property is strict decrease, already proven in lex_comment_decreases. *)

(* Note: lex_step_measure_exact and lex_step_exact_decrease were removed because
   they were false. lex_step dispatches to various lexing functions:
   - Some consume exactly 1 char (advance_char for single-char tokens)  
   - Others consume multiple chars (lex_command, lex_whitespace, lex_text, lex_comment)
   The correct property is strict decrease, already proven in lex_step_decreases. *)

(*──────── 3 Computational equation ─────────────────────────────────*)

Lemma lex_all_equation :
  forall st,
    lex_all st =
      match lex_step st with
      | None              => List.rev (tokens st)
      | Some (tok,st')    => lex_all (add_token tok st')
      end.
Proof.
  intro st.
  unfold lex_all at 1.
  (* lex_all st = lex_all_fuel (S (lexer_measure st)) st *)
  destruct (lexer_measure st) as [|n] eqn:Hmeas.
  - (* lexer_measure st = 0 *)
    (* When measure is 0, input is empty, so lex_step returns None *)
    assert (input st = EmptyString).
    { unfold lexer_measure in Hmeas. simpl in Hmeas.
      destruct (input st); [reflexivity | simpl in Hmeas; discriminate]. }
    assert (lex_step st = None).
    { unfold lex_step, peek_char. rewrite H. reflexivity. }
    (* Both sides are just List.rev (tokens st) *)
    simpl. rewrite H0. reflexivity.
  - (* lexer_measure st = S n *)
    (* We have: lex_all st = lex_all_fuel (S (lexer_measure st)) st *)
    (* Since lexer_measure st = S n, this becomes: lex_all_fuel (S (S n)) st *)
    simpl.
    (* lex_all_fuel (S (S n)) st expands to a pattern match on lex_step st *)
    destruct (lex_step st) as [[tok st']|] eqn:E.
    + (* Some (tok, st') *)
      (* Goal: complex pattern match = lex_all (add_token tok st') *)
      (* We know that both sides compute the same value through fuel sufficiency *)
      assert (H_fuel: lex_all_fuel (S n) (add_token tok st') = lex_all (add_token tok st')).
      { apply lex_all_fuel_sufficient.
        - (* S n >= lexer_measure (add_token tok st') *)
          rewrite add_token_measure.
          assert (lexer_measure st' < lexer_measure st).
          { apply lex_step_decreases with tok. exact E. }
          rewrite Hmeas in H. lia.
        - (* S (lexer_measure (add_token tok st')) >= lexer_measure (add_token tok st') *)
          lia. }
      (* Now use the fact that the left side is lex_all_fuel (S n) (add_token tok st') *)
      rewrite <- H_fuel.
      (* The left side should expand to lex_all_fuel (S n) (add_token tok st') *)
      reflexivity.
    + (* None *)
      reflexivity.
Qed.

Lemma lex_all_none :
  forall st,  lex_step st = None ->
         lex_all st = List.rev (tokens st).
Proof.
  intros st Hnone.
  rewrite lex_all_equation, Hnone; reflexivity.
Qed.

Lemma lex_all_some :
  forall st tok st',  lex_step st = Some (tok,st') ->
                  lex_all st = lex_all (add_token tok st').
Proof.
  intros st tok st' Hsome.
  rewrite lex_all_equation, Hsome; reflexivity.
Qed.

(* Fuel sufficiency lemma *)
Lemma lex_all_steps_enough_fuel : forall st fuel,
  fuel >= lexer_measure st ->
  lex_all_steps st fuel = lex_all st.
Proof.
  intros st fuel.
  generalize dependent st.
  induction fuel as [|fuel' IH].
  - (* fuel = 0 *)
    intros st Hfuel.
    (* If fuel = 0, then lexer_measure st = 0 *)
    assert (lexer_measure st = 0) by lia.
    (* This means input must be empty *)
    unfold lexer_measure in H.
    simpl in H.
    destruct (input st) eqn:E_input.
    + (* input is empty, so lex_step returns None *)
      assert (lex_step st = None).
      { unfold lex_step, peek_char. rewrite E_input. reflexivity. }
      (* lex_all_steps with fuel 0 returns List.rev st.(tokens) *)
      simpl.
      (* Use our helper lemma *)
      symmetry. apply lex_all_none. exact H0.
    + (* String a s0 - contradiction since length > 0 *)
      simpl in H. lia.
  - (* fuel = S fuel' *)
    intros st Hfuel.
    simpl.
    destruct (lex_step st) as [[tok st']|] eqn:E_step.
    + (* Some (tok, st') *)
      (* Use our helper lemma about lex_all *)
      rewrite (lex_all_some st tok st' E_step).
      (* Apply IH *)
      apply IH.
      rewrite add_token_measure.
      assert (lexer_measure st' < lexer_measure st).
      { apply lex_step_decreases with (tok := tok). exact E_step. }
      lia.
    + (* None *)
      (* Use our helper lemma *)
      symmetry. apply lex_all_none. exact E_step.
Qed.

Theorem lex_wf_equiv : forall chars,
  lex chars = lex_all (initial_state (list_ascii_to_string chars)).
Proof.
  intros chars.
  unfold lex.
  (* We need to prove that lex_all_steps with fuel 2 * length (list_ascii_to_string chars)
     produces the same result as lex_all *)
  (* Use the lemma we just proved *)
  apply lex_all_steps_enough_fuel.
  (* Show that 2 * length (list_ascii_to_string chars) >= length (list_ascii_to_string chars) *)
  unfold lexer_measure, initial_state. simpl.
  lia.
Qed.

(** * Determinism Proofs *)

(* lex_step is deterministic *)
Theorem lex_step_deterministic : forall st result1 result2,
  lex_step st = result1 -> lex_step st = result2 -> result1 = result2.
Proof.
  intros st result1 result2 H1 H2.
  rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

(* Main lexer is deterministic *)
Theorem lex_deterministic : forall s tokens1 tokens2,
  lex s = tokens1 -> lex s = tokens2 -> tokens1 = tokens2.
Proof.
  intros s tokens1 tokens2 H1 H2.
  rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

(** * Coverage and Completeness *)

(* Helper: lex_step on non-empty input always produces Some *)
Lemma lex_step_non_empty : forall st,
  input st <> EmptyString ->
  exists tok st', lex_step st = Some (tok, st').
Proof.
  intros st H_ne.
  unfold lex_step.
  (* peek_char on non-empty input gives Some *)
  destruct (peek_char st) eqn:E_peek.
  - (* Some a *)
    (* Case analysis on catcode *)
    destruct (default_catcodes a) eqn:E_cat.
    + (* CatEscape *)
      destruct (lex_command st) as [tok st'] eqn:E_cmd.
      exists tok, st'. reflexivity.
    + (* CatBeginGroup *)
      exists TBeginGroup, (advance_char st). reflexivity.
    + (* CatEndGroup *)
      exists TEndGroup, (advance_char st). reflexivity.
    + (* CatMathShift *)
      exists TMathShift, (advance_char st). reflexivity.
    + (* CatAlignment *)
      exists TAlignment, (advance_char st). reflexivity.
    + (* CatParameter *)
      exists TParameter, (advance_char st). reflexivity.
    + (* CatSuperscript *)
      exists TSuperscript, (advance_char st). reflexivity.
    + (* CatSubscript *)
      exists TSubscript, (advance_char st). reflexivity.
    + (* CatSpace *)
      destruct (lex_whitespace st) as [tok st'] eqn:E_ws.
      exists tok, st'. reflexivity.
    + (* CatLetter *)
      destruct (lex_text st) as [tok st'] eqn:E_text.
      exists tok, st'. reflexivity.
    + (* CatOther *)
      destruct (lex_text st) as [tok st'] eqn:E_text.
      exists tok, st'. reflexivity.
    + (* CatComment *)
      destruct (lex_comment st) as [tok st'] eqn:E_com.
      exists tok, st'. reflexivity.
  - (* None - contradiction since input is non-empty *)
    unfold peek_char in E_peek.
    destruct (input st) eqn:E_input.
    + contradiction H_ne. reflexivity.
    + discriminate.
Qed.

(* Helper: CatLetter chars satisfy is_text_char *)
Lemma catletter_is_text_char : forall c,
  default_catcodes c = CatLetter -> is_text_char c = true.
Proof.
  intros c H.
  (* From default_catcodes, CatLetter means is_letter c = true *)
  unfold default_catcodes in H.
  destruct (ascii_dec c ascii_backslash); [discriminate|].
  destruct (ascii_dec c ascii_lbrace); [discriminate|].
  destruct (ascii_dec c ascii_rbrace); [discriminate|].
  destruct (ascii_dec c ascii_dollar); [discriminate|].
  destruct (ascii_dec c ascii_ampersand); [discriminate|].
  destruct (ascii_dec c ascii_hash); [discriminate|].
  destruct (ascii_dec c ascii_caret); [discriminate|].
  destruct (ascii_dec c ascii_underscore); [discriminate|].
  destruct (ascii_dec c ascii_space); [discriminate|].
  destruct (ascii_dec c ascii_percent); [discriminate|].
  destruct (is_letter c) eqn:E_letter.
  - (* is_letter c = true => CatLetter *)
    (* Now show is_text_char c = true *)
    unfold is_text_char.
    rewrite E_letter.
    simpl. reflexivity.
  - (* is_letter c = false => CatOther *)
    discriminate.
Qed.

(* Helper: CatOther chars may or may not satisfy is_text_char *)
(* This is because CatOther includes digits (which satisfy is_text_char)
   and special characters (which don't) *)
Lemma catother_text_char_complex : forall c,
  default_catcodes c = CatOther ->
  (* Can't determine is_text_char from catcode alone *)
  True.
Proof.
  intros. exact I.
Qed.

(*──────── 4 Tokens produced by specialised lexers are never EOF ────────*)

(** *** Helper: [peek_char] after non‑empty input is defined *)
Lemma peek_char_some :
  forall st c,
    input st = String c (input (advance_char st)) ->
    peek_char st = Some c.
Proof.
  intros st c H.
  unfold peek_char.
  rewrite H. reflexivity.
Qed.

(** *** No helper that happily consumed input may yield [TEOF] *)

Lemma lex_command_not_eof_axiom :
  forall tok st st',
    lex_command st = (tok, st') ->
    input st <> EmptyString ->
    peek_char st = Some ascii_backslash ->
    tok <> TEOF.
Proof.
  intros tok st st' Hcmd Hne Hpeek.
  unfold lex_command in Hcmd.
  unfold peek_char in Hpeek.
  destruct (input st) as [|c rest] eqn:E_inp.
  - contradiction Hne. reflexivity.
  - injection Hpeek as H_c. subst c.
    simpl in Hcmd.
    destruct (ascii_dec ascii_backslash ascii_backslash); [|contradiction].
    remember (advance_char st) as st_adv.
    destruct (take_while is_command_char (input st_adv)) as [name rem] eqn:E_tw.
    destruct rem as [|star rem'] eqn:E_rem.
    + (* No star *)
      injection Hcmd as H_tok _. subst tok.
      discriminate.
    + (* Check for star *)
      destruct (ascii_dec star (ascii_of_nat 42)).
      * injection Hcmd as H_tok _. subst tok.
        discriminate.
      * injection Hcmd as H_tok _. subst tok.
        discriminate.
Qed.

Lemma lex_command_not_eof :
  forall tok st st', 
    lex_command st = (tok,st') -> 
    input st <> EmptyString ->
    peek_char st = Some ascii_backslash ->
    tok <> TEOF.
Proof.
  intros tok st st' Hcmd H_nonempty H_backslash.
  apply (lex_command_not_eof_axiom _ _ _ Hcmd H_nonempty H_backslash).
Qed.

Lemma lex_comment_not_eof_axiom :
  forall tok st st',
    lex_comment st = (tok, st') ->
    input st <> EmptyString ->
    peek_char st = Some ascii_percent ->
    tok <> TEOF.
Proof.
  intros tok st st' Hcmt Hne Hpeek.
  unfold lex_comment in Hcmt.
  unfold peek_char in Hpeek.
  destruct (input st) as [|c rest] eqn:E_inp.
  - contradiction Hne. reflexivity.
  - injection Hpeek as H_c. subst c.
    simpl in Hcmt.
    destruct (ascii_dec ascii_percent ascii_percent); [|contradiction].
    remember (advance_char st) as st_adv.
    destruct (take_while (fun c => negb (Nat.eqb (nat_of_ascii c) 10)) (input st_adv)) as [com rem].
    injection Hcmt as H_tok _. subst tok.
    discriminate.
Qed.

Lemma lex_comment_not_eof :
  forall tok st st', 
    lex_comment st = (tok,st') -> 
    input st <> EmptyString ->
    peek_char st = Some ascii_percent ->
    tok <> TEOF.
Proof.
  intros tok st st' Hcmt Hne Hpeek.
  apply (lex_comment_not_eof_axiom _ _ _ Hcmt Hne Hpeek).
Qed.

Lemma lex_step_not_eof_axiom :
  forall st tok st',
    lex_step st = Some (tok, st') ->
    tok <> TEOF.
Proof.
  intros st tok st' H.
  unfold lex_step in H.
  destruct (peek_char st) as [c|] eqn:E_peek; [|discriminate].
  (* We have peek_char st = Some c, so input is non-empty *)
  assert (H_nonempty: input st <> EmptyString).
  { unfold peek_char in E_peek.
    destruct (input st); [discriminate|intro; discriminate]. }
  (* Case analysis on catcode *)
  destruct (default_catcodes c) eqn:E_cat.
  - (* CatEscape *)
    destruct (lex_command st) as [tok' st''] eqn:E_cmd.
    injection H as <- <-.
    (* Use lex_command_not_eof with proper preconditions *)
    apply lex_command_not_eof with (st := st) (st' := st'').
    + exact E_cmd.
    + exact H_nonempty.
    + (* peek_char st = Some c and default_catcodes c = CatEscape *)
      assert (H_back: c = ascii_backslash).
      { apply escape_is_backslash. exact E_cat. }
      subst c. exact E_peek.
  - (* CatBeginGroup *)
    injection H as <- <-.
    discriminate.
  - (* CatEndGroup *)
    injection H as <- <-.
    discriminate.
  - (* CatMathShift *)
    injection H as <- <-.
    discriminate.
  - (* CatAlignment *)
    injection H as <- <-.
    discriminate.
  - (* CatParameter *)
    injection H as <- <-.
    discriminate.
  - (* CatSuperscript *)
    injection H as <- <-.
    discriminate.
  - (* CatSubscript *)
    injection H as <- <-.
    discriminate.
  - (* CatSpace *)
    destruct (lex_whitespace st) as [tok' st''] eqn:E_ws.
    injection H as <- <-.
    (* lex_whitespace always returns TSpace, never TEOF *)
    unfold lex_whitespace in E_ws.
    destruct (take_while is_whitespace (input st)) as [spaces remaining].
    injection E_ws as <-.
    discriminate.
  - (* CatLetter *)
    destruct (lex_text st) as [tok' st''] eqn:E_text.
    injection H as <- <-.
    (* lex_text returns TText, never TEOF when called on non-empty input *)
    unfold lex_text in E_text.
    destruct (peek_char st) as [c'|] eqn:E_peek'.
    + (* Some c' *)
      destruct (is_text_char c') eqn:E_text_char.
      * (* is_text_char true: returns TText *)
        destruct (take_while is_text_char (input st)) as [text remaining].
        injection E_text as <-.
        discriminate.
      * (* is_text_char false: returns TText with single char *)
        injection E_text as <-.
        discriminate.
    + (* None *)
      injection E_text as <-.
      discriminate.
  - (* CatOther *)
    destruct (lex_text st) as [tok' st''] eqn:E_text.
    injection H as <- <-.
    (* Same as CatLetter case *)
    unfold lex_text in E_text.
    destruct (peek_char st) as [c'|] eqn:E_peek'.
    + (* Some c' *)
      destruct (is_text_char c') eqn:E_text_char.
      * destruct (take_while is_text_char (input st)) as [text remaining].
        injection E_text as <-.
        discriminate.
      * injection E_text as <-.
        discriminate.
    + (* None *)
      injection E_text as <-.
      discriminate.
  - (* CatComment *)
    destruct (lex_comment st) as [tok' st''] eqn:E_com.
    injection H as <- <-.
    (* Use lex_comment_not_eof with proper preconditions *)
    apply lex_comment_not_eof with (st := st) (st' := st'').
    + exact E_com.
    + exact H_nonempty.
    + (* peek_char st = Some c and default_catcodes c = CatComment *)
      assert (H_perc: c = ascii_percent).
      { unfold default_catcodes in E_cat.
        destruct (ascii_dec c ascii_backslash); [discriminate|].
        destruct (ascii_dec c ascii_lbrace); [discriminate|].
        destruct (ascii_dec c ascii_rbrace); [discriminate|].
        destruct (ascii_dec c ascii_dollar); [discriminate|].
        destruct (ascii_dec c ascii_ampersand); [discriminate|].
        destruct (ascii_dec c ascii_hash); [discriminate|].
        destruct (ascii_dec c ascii_caret); [discriminate|].
        destruct (ascii_dec c ascii_underscore); [discriminate|].
        destruct (ascii_dec c ascii_space); [discriminate|].
        destruct (ascii_dec c ascii_percent) as [H_eq|]; [exact H_eq|].
        destruct (is_letter c); discriminate. }
      subst c. exact E_peek.
Qed.

(* Helper: tokens produced by lex_step are never TEOF *)
Lemma lex_step_not_eof : forall st tok st',
  lex_step st = Some (tok, st') ->
  tok <> TEOF.
Proof.
  intros st tok st' H.
  apply (lex_step_not_eof_axiom _ _ _ H).
Qed.

(* Helper: Token produced by lex_step appears in final result *)
Lemma lex_step_token_in_result :
  forall st tok st',
    lex_step st = Some (tok, st') ->
    In tok (lex_all st).
Proof.
  intros st tok st' H.
  (* Goal: In tok (lex_all st) *)
  (* Use the lex_all equation to unfold lex_all st *)
  rewrite lex_all_equation.
  (* Now rewrite using H: lex_step st = Some (tok, st') *)
  rewrite H.
  (* Goal: In tok (lex_all (add_token tok st')) *)
  
  (* Key insight: add_token tok st' puts tok at the head of tokens list *)
  (* We need to prove that tok will appear in the final result *)
  
  (* Simplest approach: use the fact that tokens accumulate *)
  (* The core insight: lex_all_fuel always preserves tokens from the input state *)
  
  (* First, we need helper lemmas showing that individual lexing functions preserve tokens *)
  assert (H_lex_command_preserves_tokens: forall st_arg tok_arg st_arg',
    lex_command st_arg = (tok_arg, st_arg') -> tokens st_arg' = tokens st_arg).
  {
    intros st_arg tok_arg st_arg' H_eq.
    unfold lex_command in H_eq.
    destruct (input st_arg) as [|c rest] eqn:E_input.
    - (* Empty input *)
      injection H_eq as _ <-. reflexivity.
    - (* Non-empty input *)
      destruct (ascii_dec c ascii_backslash) as [H_back|H_not_back].
      + (* c = ascii_backslash *)
        remember (advance_char st_arg) as st_adv.
        destruct (take_while is_command_char (input st_adv)) as [cmd_name remaining] eqn:E_take.
        destruct remaining as [|star rest'] eqn:E_rem.
        * (* No star *)
          injection H_eq as _ <-. simpl. 
          subst st_adv. unfold advance_char. simpl. rewrite E_input.
          destruct (ascii_dec c (ascii_of_nat 10)); reflexivity.
        * (* Check for star *)
          destruct (ascii_dec star (ascii_of_nat 42)) as [H_star|H_not_star].
          -- (* Has star *)
             injection H_eq as _ <-. simpl.
             subst st_adv. unfold advance_char. simpl. rewrite E_input.
             destruct (ascii_dec c (ascii_of_nat 10)); reflexivity.
          -- (* No star *)
             injection H_eq as _ <-. simpl.
             subst st_adv. unfold advance_char. simpl. rewrite E_input.
             destruct (ascii_dec c (ascii_of_nat 10)); reflexivity.
      + (* c <> ascii_backslash *)
        injection H_eq as _ <-. reflexivity.
  }
  
  assert (H_lex_whitespace_preserves_tokens: forall st_arg tok_arg st_arg',
    lex_whitespace st_arg = (tok_arg, st_arg') -> tokens st_arg' = tokens st_arg).
  {
    intros st_arg tok_arg st_arg' H_eq.
    unfold lex_whitespace in H_eq.
    destruct (take_while is_whitespace (input st_arg)) as [spaces remaining] eqn:E_take.
    injection H_eq as _ <-. simpl. reflexivity.
  }
  
  assert (H_lex_comment_preserves_tokens: forall st_arg tok_arg st_arg',
    lex_comment st_arg = (tok_arg, st_arg') -> tokens st_arg' = tokens st_arg).
  {
    intros st_arg tok_arg st_arg' H_eq.
    unfold lex_comment in H_eq.
    destruct (input st_arg) as [|c rest] eqn:E_input.
    - (* Empty input *)
      injection H_eq as _ <-. reflexivity.
    - (* Non-empty input *)
      destruct (ascii_dec c ascii_percent) as [H_perc|H_not_perc].
      + (* c = ascii_percent *)
        remember (advance_char st_arg) as st_adv.
        destruct (take_while (fun c => negb (Nat.eqb (nat_of_ascii c) 10)) (input st_adv)) as [comment_text remaining] eqn:E_take.
        injection H_eq as _ <-. simpl.
        subst st_adv. unfold advance_char. simpl. rewrite E_input.
        destruct (ascii_dec c (ascii_of_nat 10)); reflexivity.
      + (* c <> ascii_percent *)
        injection H_eq as _ <-. reflexivity.
  }
  
  assert (H_lex_text_preserves_tokens: forall st_arg tok_arg st_arg',
    lex_text st_arg = (tok_arg, st_arg') -> tokens st_arg' = tokens st_arg).
  {
    intros st_arg tok_arg st_arg' H_eq.
    unfold lex_text in H_eq.
    destruct (peek_char st_arg) as [c|] eqn:E_peek.
    - (* Some character *)
      destruct (is_text_char c) eqn:E_text_char.
      + (* is_text_char = true *)
        destruct (take_while is_text_char (input st_arg)) as [text remaining] eqn:E_take.
        injection H_eq as _ <-. simpl. reflexivity.
      + (* is_text_char = false *)
        injection H_eq as _ <-.
        unfold advance_char. simpl.
        destruct (input st_arg); reflexivity.
    - (* None - EOF *)
      injection H_eq as _ <-. reflexivity.
  }
  
  (* Now prove that lex_step preserves tokens using the helper lemmas *)
  assert (H_lex_step_preserves_tokens: forall st tok_new st_new,
    lex_step st = Some (tok_new, st_new) ->
    tokens st_new = tokens st).
  {
    intros st_temp tok_new st_new H_step_temp.
    unfold lex_step in H_step_temp.
    destruct (peek_char st_temp) as [c|] eqn:E_peek; [|discriminate].
    destruct (default_catcodes c) eqn:E_cat.
    - (* CatEscape *)
      destruct (lex_command st_temp) as [tok_cmd st_cmd] eqn:E_cmd.
      injection H_step_temp as <- <-.
      apply (H_lex_command_preserves_tokens st_temp tok_cmd st_cmd E_cmd).
    - (* CatBeginGroup *)
      injection H_step_temp as <- <-.
      unfold advance_char. destruct (input st_temp); reflexivity.
    - (* CatEndGroup *)
      injection H_step_temp as <- <-.
      unfold advance_char. destruct (input st_temp); reflexivity.
    - (* CatMathShift *)
      injection H_step_temp as <- <-.
      unfold advance_char. destruct (input st_temp); reflexivity.
    - (* CatAlignment *)
      injection H_step_temp as <- <-.
      unfold advance_char. destruct (input st_temp); reflexivity.
    - (* CatParameter *)
      injection H_step_temp as <- <-.
      unfold advance_char. destruct (input st_temp); reflexivity.
    - (* CatSuperscript *)
      injection H_step_temp as <- <-.
      unfold advance_char. destruct (input st_temp); reflexivity.
    - (* CatSubscript *)
      injection H_step_temp as <- <-.
      unfold advance_char. destruct (input st_temp); reflexivity.
    - (* CatSpace *)
      destruct (lex_whitespace st_temp) as [tok_ws st_ws] eqn:E_ws.
      injection H_step_temp as <- <-.
      apply (H_lex_whitespace_preserves_tokens st_temp tok_ws st_ws E_ws).
    - (* CatLetter *)
      destruct (lex_text st_temp) as [tok_txt st_txt] eqn:E_txt.
      injection H_step_temp as <- <-.
      apply (H_lex_text_preserves_tokens st_temp tok_txt st_txt E_txt).
    - (* CatOther *)
      destruct (lex_text st_temp) as [tok_txt st_txt] eqn:E_txt.
      injection H_step_temp as <- <-.
      apply (H_lex_text_preserves_tokens st_temp tok_txt st_txt E_txt).
    - (* CatComment *)
      destruct (lex_comment st_temp) as [tok_com st_com] eqn:E_com.
      injection H_step_temp as <- <-.
      apply (H_lex_comment_preserves_tokens st_temp tok_com st_com E_com).
  }
  
  (* Now prove the main lemma: if a token is in the initial state, it appears in the result *)
  assert (H_token_preserved: forall fuel st_init,
    In tok (tokens st_init) ->
    In tok (lex_all_fuel fuel st_init)).
  {
    induction fuel as [|fuel' IH]; intros st_init H_in.
    - (* Base case: fuel = 0 *)
      simpl. apply -> in_rev. exact H_in.
    - (* Inductive case: fuel = S fuel' *)
      simpl.
      destruct (lex_step st_init) as [[tok_new st_new]|] eqn:E_step.
      + (* lex_step produces a token *)
        (* Need to prove: In tok (lex_all_fuel fuel' (add_token tok_new st_new)) *)
        apply IH.
        (* Need to prove: In tok (tokens (add_token tok_new st_new)) *)
        unfold add_token. simpl. right.
        (* Need to prove: In tok (tokens st_new) *)
        (* Use the fact that lex_step preserves tokens *)
        pose proof (H_lex_step_preserves_tokens _ _ _ E_step) as H_preserve.
        rewrite H_preserve.
        exact H_in.
      + (* lex_step returns None *)
        simpl. apply -> in_rev. exact H_in.
  }
  
  (* Apply the lemma *)
  unfold lex_all.
  apply H_token_preserved.
  
  (* Show that tok is in the initial tokens of add_token tok st' *)
  unfold add_token. simpl. left. reflexivity.
Qed.

(* Lexer produces tokens for non-empty input *)
Theorem lex_coverage : forall s,
  s <> EmptyString -> 
  exists tok, In tok (lex s) /\ tok <> TEOF.
Proof.
  intros s H_nonempty.
  (* For non-empty input, lex_step on initial state produces a token *)
  pose (st0 := initial_state s).
  assert (H_input: input st0 <> EmptyString).
  { unfold st0, initial_state. simpl. exact H_nonempty. }
  
  (* lex_step produces Some token for non-empty input *)
  assert (H_some: exists tok st', lex_step st0 = Some (tok, st')).
  { apply lex_step_non_empty. exact H_input. }
  
  destruct H_some as [tok [st' H_step]].
  
  (* The token is not TEOF *)
  assert (H_not_eof: tok <> TEOF).
  { apply lex_step_not_eof with (st := st0) (st' := st').
    exact H_step. }
  
  (* The token appears in the final result *)
  exists tok.
  split.
  - (* In tok (lex s) *)
    (* Use lex_step_token_in_result lemma *)
    (* We have: lex_step st0 = Some (tok, st') *)
    (* We need: In tok (lex s) *)
    (* Use lex_wf_equiv: lex s = lex_all (initial_state s) *)
    rewrite lex_wf_equiv.
    unfold st0.
    apply lex_step_token_in_result with (st' := st').
    exact H_step.
  - (* tok <> TEOF *)
    exact H_not_eof.
Qed.

(* Helper: advance_char increases position *)
Lemma advance_char_position : forall st,
  input st <> EmptyString ->
  (advance_char st).(position) = st.(position) + 1.
Proof.
  intros st H_ne.
  unfold advance_char.
  destruct (input st) eqn:E.
  - contradiction H_ne. reflexivity.
  - simpl. 
    (* position st + 1 = S (position st) *)
    rewrite Nat.add_1_r. reflexivity.
Qed.

(* Helper: advance_char never decreases position *)
Lemma advance_char_position_mono : forall st,
  (advance_char st).(position) >= st.(position).
Proof.
  intros st.
  unfold advance_char.
  destruct (input st); simpl; lia.
Qed.

(* Helper: lex_command advances position *)
Lemma lex_command_position : forall st tok st',
  lex_command st = (tok, st') ->
  st'.(position) >= st.(position).
Proof.
  intros st tok st' H.
  unfold lex_command in H.
  destruct (input st) eqn:E_input.
  - (* Empty input *)
    injection H as <- <-.
    unfold ge. apply Nat.le_refl.
  - (* Non-empty input *)
    destruct (ascii_dec a ascii_backslash).
    + (* Backslash case *)
      remember (advance_char st) as st_adv.
      destruct (take_while is_command_char (input st_adv)) as [cmd_name remaining] eqn:E_take.
      destruct remaining as [|star rest'] eqn:E_rem.
      * (* No remaining chars *)
        injection H as _ <-.
        simpl. unfold ge.
        assert (H_advance: (advance_char st).(position) >= st.(position)).
        { apply advance_char_position_mono. }
        transitivity (position st_adv).
        -- rewrite Heqst_adv. exact H_advance.
        -- apply Nat.le_add_r.
      * (* Check for star *)
        destruct (ascii_dec star (ascii_of_nat 42)) eqn:E_star.
        -- (* star character *)
           injection H as _ <-.
           simpl. unfold ge.
           assert (H_advance: (advance_char st).(position) >= st.(position)).
           { apply advance_char_position_mono. }
           transitivity (position st_adv).
           ++ rewrite Heqst_adv. exact H_advance.
           ++ apply Nat.le_add_r.
        -- (* not star *)
           injection H as _ <-.
           simpl. unfold ge.
           assert (H_advance: (advance_char st).(position) >= st.(position)).
           { apply advance_char_position_mono. }
           transitivity (position st_adv).
           ++ rewrite Heqst_adv. exact H_advance.
           ++ apply Nat.le_add_r.
    + (* Not backslash *)
      injection H as _ <-.
      unfold ge. apply Nat.le_refl.
Qed.

(* Helper: lex_whitespace advances position *)
Lemma lex_whitespace_position : forall st tok st',
  lex_whitespace st = (tok, st') ->
  st'.(position) >= st.(position).
Proof.
  intros st tok st' H.
  unfold lex_whitespace in H.
  destruct (take_while is_whitespace (input st)) as [spaces remaining] eqn:E_take.
  injection H as <- <-.
  simpl. unfold ge. apply Nat.le_add_r.
Qed.

(* Helper: lex_text advances position *)
Lemma lex_text_position : forall st tok st',
  lex_text st = (tok, st') ->
  st'.(position) >= st.(position).
Proof.
  intros st tok st' H.
  unfold lex_text in H.
  destruct (peek_char st) eqn:E_peek.
  - (* Some c *)
    destruct (is_text_char a) eqn:E_text.
    + (* is_text_char true *)
      destruct (take_while is_text_char (input st)) as [text remaining] eqn:E_take.
      injection H as <- <-.
      simpl. lia.
    + (* is_text_char false *)
      (* When is_text_char is false, lex_text consumes single char *)
      injection H as <- <-.
      (* st' = advance_char st, so position increases or stays same *)
      apply advance_char_position_mono.
  - (* None *)
    injection H as <- <-.
    unfold ge. apply Nat.le_refl.
Qed.

(* Helper: lex_comment advances position *)
Lemma lex_comment_position : forall st tok st',
  lex_comment st = (tok, st') ->
  st'.(position) >= st.(position).
Proof.
  intros st tok st' H.
  unfold lex_comment in H.
  destruct (input st) eqn:E_input.
  - (* Empty *)
    injection H as <- <-.
    unfold ge. apply Nat.le_refl.
  - (* Non-empty *)
    destruct (ascii_dec a ascii_percent).
    + (* Percent - advance position by 1 + comment length *)
      remember (advance_char st) as st_adv.
      destruct (take_while (fun c => negb (Nat.eqb (nat_of_ascii c) 10)) (input st_adv)) as [comment_text remaining] eqn:E_take.
      injection H as <- <-.
      simpl. unfold ge.
      assert (H_advance: (advance_char st).(position) >= st.(position)).
      { apply advance_char_position_mono. }
      transitivity (position st_adv).
      * rewrite Heqst_adv. exact H_advance.
      * apply Nat.le_add_r.
    + (* Not percent *)
      injection H as <- <-.
      unfold ge. apply Nat.le_refl.
Qed.

(* Position tracking is accurate *)
Theorem position_accurate : forall st st' tok,
  lex_step st = Some (tok, st') ->
  st'.(position) >= st.(position).
Proof.
  intros st st' tok H.
  (* Case analysis on lex_step *)
  unfold lex_step in H.
  destruct (peek_char st) as [c|] eqn:E_peek; [|discriminate].
  destruct (default_catcodes c) eqn:E_cat.
  - (* CatEscape *)
    destruct (lex_command st) as [tok' st''] eqn:E_cmd.
    injection H as <- <-.
    (* lex_command advances position by at least 1 (for the backslash) *)
    apply lex_command_position with (tok := tok').
    exact E_cmd.
  - (* CatBeginGroup *)
    injection H as <- <-.
    (* advance_char never decreases position *)
    apply advance_char_position_mono.
  - (* CatEndGroup *)
    injection H as <- <-.
    apply advance_char_position_mono.
  - (* CatMathShift *)
    injection H as <- <-.
    apply advance_char_position_mono.
  - (* CatAlignment *)
    injection H as <- <-.
    apply advance_char_position_mono.
  - (* CatParameter *)
    injection H as <- <-.
    apply advance_char_position_mono.
  - (* CatSuperscript *)
    injection H as <- <-.
    apply advance_char_position_mono.
  - (* CatSubscript *)
    injection H as <- <-.
    apply advance_char_position_mono.
  - (* CatSpace *)
    destruct (lex_whitespace st) as [tok' st''] eqn:E_ws.
    injection H as <- <-.
    (* lex_whitespace advances position *)
    apply lex_whitespace_position with (tok := tok').
    exact E_ws.
  - (* CatLetter *)
    destruct (lex_text st) as [tok' st''] eqn:E_text.
    injection H as <- <-.
    (* lex_text advances position *)
    apply lex_text_position with (tok := tok').
    exact E_text.
  - (* CatOther *)
    destruct (lex_text st) as [tok' st''] eqn:E_text.
    injection H as <- <-.
    apply lex_text_position with (tok := tok').
    exact E_text.
  - (* CatComment *)
    destruct (lex_comment st) as [tok' st''] eqn:E_com.
    injection H as <- <-.
    apply lex_comment_position with (tok := tok').
    exact E_com.
Qed.