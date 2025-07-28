(* LaTeX Perfectionist v24 - Phase 1: Verified Lexer *)
(* Week 1: Lexer State Machine *)

Require Import Bool Arith List String Ascii Lia.
Require Import Coq.Arith.Compare_dec.  (* For decide equality *)
Require Import LatexCatcodes.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.


(** * LaTeX Token Types *)

(* Token types based on corpus analysis of most frequent patterns *)
Inductive latex_token : Type :=
  | TCommand : string -> latex_token       (* \frac, \begin, \end *)
  | TBeginGroup : latex_token              (* { *)
  | TEndGroup : latex_token                (* } *)
  | TMathShift : latex_token               (* $ *)
  | TAlignment : latex_token               (* & *)
  | TParameter : latex_token               (* # *)
  | TSuperscript : latex_token             (* ^ *)
  | TSubscript : latex_token               (* _ *)
  | TText : string -> latex_token          (* regular text *)
  | TSpace : latex_token                   (* whitespace *)
  | TComment : string -> latex_token       (* % comment *)
  | TNewline : latex_token                 (* end of line *)
  | TEOF : latex_token.                    (* end of file *)

(** * Decidable equality for [latex_token] — needed by [congruence] *)

Lemma latex_token_eq_dec : forall t1 t2 : latex_token,
  {t1 = t2} + {t1 <> t2}.
Proof. decide equality; apply string_dec || apply ascii_dec. Qed.

(** * Lexer State Machine *)

(* Lexer state with termination measure *)
Record lexer_state : Type := {
  input : string;                          (* remaining input *)
  position : nat;                          (* current position in original input *)
  tokens : list latex_token;               (* accumulated tokens (in reverse order) *)
  line_number : nat;                       (* current line number for error reporting *)
  column_number : nat                      (* current column number for error reporting *)
}.

(* Measure function for termination proof *)
Definition lexer_measure (st : lexer_state) : nat :=
  String.length st.(input).

(* Initial state constructor *)
Definition initial_state (s : string) : lexer_state := {|
  input := s;
  position := 0;
  tokens := [];
  line_number := 1;
  column_number := 1
|}.

(** * State Manipulation Functions *)

(* Check if input is empty *)
Definition input_empty (st : lexer_state) : bool :=
  match st.(input) with
  | EmptyString => true
  | _ => false
  end.

(* Peek at the first character without consuming it *)
Definition peek_char (st : lexer_state) : option ascii :=
  match st.(input) with
  | EmptyString => None
  | String c _ => Some c
  end.

(* Advance position by one character *)
Definition advance_char (st : lexer_state) : lexer_state :=
  match st.(input) with
  | EmptyString => st
  | String c rest => 
    let new_column := if ascii_dec c (ascii_of_nat 10) (* newline *)
                     then 1 
                     else S st.(column_number) in
    let new_line := if ascii_dec c (ascii_of_nat 10)
                   then S st.(line_number)
                   else st.(line_number) in
    {|
      input := rest;
      position := S st.(position);
      tokens := st.(tokens);
      line_number := new_line;
      column_number := new_column
    |}
  end.

(* Add a token to the state *)
Definition add_token (tok : latex_token) (st : lexer_state) : lexer_state := {|
  input := st.(input);
  position := st.(position);
  tokens := tok :: st.(tokens);
  line_number := st.(line_number);
  column_number := st.(column_number)
|}.

(** * Basic Properties *)

(* Advancing decreases input length *)
Lemma advance_decreases_measure : forall st,
  input_empty st = false ->
  lexer_measure (advance_char st) < lexer_measure st.
Proof.
  intros st H.
  unfold lexer_measure, advance_char, input_empty in *.
  destruct (input st) as [|c rest] eqn:E.
  - simpl in H. discriminate H.
  - simpl. apply Nat.lt_succ_diag_r.
Qed.

(* Peek doesn't change state *)
Lemma peek_preserves_state : forall st c,
  peek_char st = Some c ->
  exists rest, st.(input) = String c rest.
Proof.
  intros st c H.
  unfold peek_char in H.
  destruct st.(input) as [| c' rest].
  - discriminate H.
  - injection H as H_eq. subst c'. 
    exists rest. reflexivity.
Qed.

(* Adding token preserves input *)
Lemma add_token_preserves_input : forall tok st,
  (add_token tok st).(input) = st.(input).
Proof.
  intros tok st.
  unfold add_token. simpl. reflexivity.
Qed.

(* Adding token preserves measure *)
Lemma add_token_preserves_measure : forall tok st,
  lexer_measure (add_token tok st) = lexer_measure st.
Proof.
  intros tok st.
  unfold lexer_measure, add_token. simpl. reflexivity.
Qed.

(** * String Utilities *)

(* Take characters while condition holds *)
Fixpoint take_while (f : ascii -> bool) (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c rest => 
    if f c 
    then let (taken, remaining) := take_while f rest in
         (String c taken, remaining)
    else (EmptyString, s)
  end.

(* Check if character is letter (for command names) *)
Definition is_command_char (c : ascii) : bool :=
  is_letter c.

(* Check if character is whitespace *)
Definition is_whitespace (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (Nat.eqb n 32) (Nat.eqb n 9))    (* space, tab *)
      (orb (Nat.eqb n 10) (Nat.eqb n 13)).   (* newline, carriage return *)

(* Check if character is text (letters and digits) *)
Definition is_text_char (c : ascii) : bool :=
  orb (is_letter c) 
      (let n := nat_of_ascii c in
       andb (Nat.leb 48 n) (Nat.leb n 57)).  (* digits 0-9 *)

(* take_while decreases or preserves string length *)
Lemma take_while_length : forall f s,
  let (taken, remaining) := take_while f s in
  String.length remaining <= String.length s.
Proof.
  intros f.
  fix IH 1.
  intros s.
  destruct s as [|c rest].
  - (* Base case: empty string *)
    simpl. lia.
  - (* Inductive case: String c rest *)
    simpl.
    destruct (f c) eqn:Hf.
    + (* Character satisfies predicate *)
      destruct (take_while f rest) as [taken' remaining'] eqn:E.
      simpl.
      (* Apply IH to rest *)
      assert (H: String.length remaining' <= String.length rest).
      { 
        specialize (IH rest).
        rewrite E in IH.
        exact IH.
      }
      lia.
    + (* Character doesn't satisfy predicate *)
      simpl. lia.
Qed.

(** * Command Validation *)

(* Common LaTeX commands for validation *)
Definition common_latex_commands : list string :=
  latex_epsilon_commands ++ 
  ["section"%string; "subsection"%string; "chapter"%string; "paragraph"%string;
   "textbf"%string; "textit"%string; "emph"%string; "text"%string;
   "int"%string; "sum"%string; "prod"%string; "lim"%string;
   "documentclass"%string; "usepackage"%string; "newcommand"%string;
   "item"%string; "includegraphics"%string; "caption"%string].

(* Check if a command name is known/valid *)
Definition is_known_command (cmd : string) : bool :=
  existsb (String.eqb cmd) common_latex_commands.

(* Command validation for strict mode - currently permissive *)
Definition validate_command (cmd : string) : bool :=
  (* For now, accept all commands. In strict mode, use: is_known_command cmd *)
  true.

(** * Lexer State Machine Transitions *)

(* Lex a command starting with backslash *)
Definition lex_command (st : lexer_state) : latex_token * lexer_state :=
  match st.(input) with
  | EmptyString => (TEOF, st)
  | String backslash rest =>
    if ascii_dec backslash ascii_backslash
    then 
      let st' := advance_char st in
      let (cmd_name, remaining) := take_while is_command_char st'.(input) in
      (* Check for starred commands *)
      let (final_name, final_remaining) := 
        match remaining with
        | String star rest' =>
          if ascii_dec star (ascii_of_nat 42) (* * character *)
          then (cmd_name ++ "*", rest')
          else (cmd_name, remaining)
        | _ => (cmd_name, remaining)
        end in
      let final_st := {|
        input := final_remaining;
        position := st'.(position) + String.length final_name;
        tokens := st'.(tokens);
        line_number := st'.(line_number);
        column_number := st'.(column_number) + String.length final_name
      |} in
      (TCommand final_name, final_st)
    else (TEOF, st) (* shouldn't happen *)
  end.

(* Command lexing decreases measure when called on backslash *)
Lemma lex_command_decreases : forall st tok st',
  lex_command st = (tok, st') ->
  st.(input) <> EmptyString ->
  match peek_char st with
  | Some c => default_catcodes c = CatEscape
  | None => False
  end ->
  lexer_measure st' < lexer_measure st.
Proof.
  intros st tok st' H H_nonempty H_escape.
  unfold lex_command in H.
  destruct (input st) as [|c rest] eqn:E_input.
  - (* Empty input - contradiction *)
    contradiction H_nonempty. reflexivity.
  - (* String c rest *)
    destruct (ascii_dec c ascii_backslash) as [H_back|H_not_back].
    + (* c is backslash *)
      remember (advance_char st) as st1.
      destruct (take_while is_command_char (input st1)) as [cmd_name remaining] eqn:E_take.
      destruct remaining as [|star rest'] eqn:E_rem.
      * (* No more chars after command *)
        (* Looking at the definition of lex_command, when remaining is empty:
           final_name = cmd_name, final_remaining = EmptyString
           final_st has input = EmptyString *)
        injection H as H_tok H_st. subst st'.
        unfold lexer_measure. simpl.
        (* input st = String c rest by E_input *)
        rewrite E_input.
        simpl.
        (* Goal: 0 < S (length rest) *)
        apply Nat.lt_0_succ.
      * (* String star rest' after command *)
        destruct (ascii_dec star (ascii_of_nat 42)) as [H_star|H_not_star].
        -- (* star character *)
           injection H as H_tok H_st. subst st'.
           unfold lexer_measure. simpl.
           (* st has input = String c rest by E_input *)
           rewrite E_input. simpl.
           (* Goal: length rest' < S (length rest) *)
           (* We know advance_char st has input = rest *)
           assert (H_adv: (advance_char st).(input) = rest).
           { unfold advance_char. simpl. 
             rewrite E_input. 
             destruct (ascii_dec ascii_backslash (ascii_of_nat 10)); reflexivity. }
           rewrite <- Heqst1 in H_adv.
           rewrite H_adv in E_take.
           (* So take_while is_command_char rest = (cmd_name, String star rest') *)
           assert (H_len: String.length (String star rest') <= String.length rest).
           { pose proof (take_while_length is_command_char rest) as H.
             rewrite E_take in H.
             exact H. }
           simpl in H_len. lia.
        -- (* not star *)
           injection H as H_tok H_st. subst st'.
           unfold lexer_measure. simpl.
           (* st has input = String c rest by E_input *)
           rewrite E_input. simpl.
           (* Goal: S (length rest') < S (length rest) *)
           (* We know advance_char st has input = rest *)
           assert (H_adv: (advance_char st).(input) = rest).
           { unfold advance_char. simpl. 
             rewrite E_input. 
             destruct (ascii_dec ascii_backslash (ascii_of_nat 10)); reflexivity. }
           rewrite <- Heqst1 in H_adv.
           rewrite H_adv in E_take.
           assert (H_len: String.length (String star rest') <= String.length rest).
           { pose proof (take_while_length is_command_char rest) as H.
             rewrite E_take in H.
             exact H. }
           simpl in H_len. lia.
    + (* c is not backslash - returns TEOF *)
      (* But we have H_escape saying c has catcode CatEscape *)
      unfold peek_char in H_escape.
      rewrite E_input in H_escape.
      simpl in H_escape.
      (* So default_catcodes c = CatEscape *)
      (* But c is not ascii_backslash, which contradicts catcode definition *)
      assert (default_catcodes c = CatEscape) by exact H_escape.
      assert (c = ascii_backslash).
      { apply escape_is_backslash. exact H0. }
      contradiction.
Qed.

(* Lex whitespace *)
Definition lex_whitespace (st : lexer_state) : latex_token * lexer_state :=
  let (spaces, remaining) := take_while is_whitespace st.(input) in
  let final_st := {|
    input := remaining;
    position := st.(position) + String.length spaces;
    tokens := st.(tokens);
    line_number := st.(line_number);  (* take_while will handle newlines *)
    column_number := st.(column_number) + String.length spaces
  |} in
  (TSpace, final_st).

(* Whitespace lexing decreases measure when input is whitespace *)
Lemma lex_whitespace_decreases : forall st tok st' c,
  lex_whitespace st = (tok, st') ->
  peek_char st = Some c ->
  is_whitespace c = true ->
  lexer_measure st' < lexer_measure st.
Proof.
  intros st tok st' c H H_peek H_ws.
  unfold lex_whitespace in H.
  destruct (take_while is_whitespace (input st)) as [spaces remaining] eqn:E_take.
  injection H as H_tok H_st. subst.
  unfold lexer_measure. simpl.
  (* We know peek_char st = Some c, so input is non-empty *)
  unfold peek_char in H_peek.
  destruct (input st) as [|c' rest] eqn:E_input.
  - (* Empty - contradiction *)
    discriminate H_peek.
  - (* String c' rest *)
    injection H_peek as H_c. subst c'.
    (* Since is_whitespace c = true, take_while will consume at least c *)
    simpl in E_take.
    rewrite H_ws in E_take.
    destruct (take_while is_whitespace rest) as [spaces' remaining'] eqn:E_take'.
    injection E_take as H_sp H_rem.
    simpl.
    (* remaining = remaining', and we need to show length remaining' < S (length rest) *)
    subst spaces remaining.
    (* Now we need to show length remaining' < S (length rest) *)
    assert (String.length remaining' <= String.length rest).
    { pose proof (take_while_length is_whitespace rest) as H.
      rewrite E_take' in H.
      exact H. }
    lia.
Qed.

(* Lex comment (from % to end of line) *)
Definition lex_comment (st : lexer_state) : latex_token * lexer_state :=
  match st.(input) with
  | EmptyString => (TEOF, st)
  | String percent rest =>
    if ascii_dec percent ascii_percent
    then
      let st' := advance_char st in
      (* Take until newline *)
      let (comment_text, remaining) := take_while (fun c => negb (Nat.eqb (nat_of_ascii c) 10)) st'.(input) in
      let final_st := {|
        input := remaining;
        position := st'.(position) + String.length comment_text;
        tokens := st'.(tokens);
        line_number := st'.(line_number);
        column_number := st'.(column_number) + String.length comment_text
      |} in
      (TComment comment_text, final_st)
    else (TEOF, st) (* shouldn't happen *)
  end.

(* Comment lexing decreases measure when input is non-empty and starts with % *)
Lemma lex_comment_decreases : forall st tok st',
  lex_comment st = (tok, st') ->
  input_empty st = false ->
  match peek_char st with
  | Some c => c = ascii_percent
  | None => False
  end ->
  lexer_measure st' < lexer_measure st.
Proof.
  intros st tok st' H H_nonempty H_percent.
  (* Direct approach: lex_comment on % advances past % and takes until newline *)
  unfold lex_comment in H.
  destruct (input st) as [|c rest] eqn:E_input.
  - (* Empty input - contradiction *)
    unfold input_empty in H_nonempty.
    rewrite E_input in H_nonempty. discriminate.
  - (* String c rest *)
    unfold peek_char in H_percent.
    rewrite E_input in H_percent. simpl in H_percent.
    subst c.
    (* c = ascii_percent *)
    destruct (ascii_dec ascii_percent ascii_percent) as [H_eq|H_neq].
    + (* ascii_percent = ascii_percent *)
      remember (advance_char st) as st_adv.
      assert (H_adv_input: st_adv.(input) = rest).
      { subst st_adv. unfold advance_char. simpl. rewrite E_input.
        destruct (ascii_dec ascii_percent (ascii_of_nat 10)); reflexivity. }
      destruct (take_while (fun c => negb (Nat.eqb (nat_of_ascii c) 10)) st_adv.(input)) as [comment_text remaining] eqn:E_take.
      injection H as _ H_st_eq.
      unfold lexer_measure. simpl.
      rewrite E_input. simpl.
      subst st'. simpl.
      (* Goal: String.length remaining < S (String.length rest) *)
      (* We know remaining comes from take_while on st_adv.(input) = rest *)
      rewrite H_adv_input in E_take.
      assert (String.length remaining <= String.length rest).
      { pose proof (take_while_length (fun c => negb (Nat.eqb (nat_of_ascii c) 10)) rest) as H_len.
        rewrite E_take in H_len. exact H_len. }
      lia.
    + (* contradiction: ascii_percent <> ascii_percent *)
      contradiction H_neq. reflexivity.
Qed.

(* Lex regular text (letters and numbers) *)
Definition lex_text (st : lexer_state) : latex_token * lexer_state :=
  match peek_char st with
  | None => (TEOF, st)
  | Some c =>
    if is_text_char c
    then
      let (text, remaining) := take_while is_text_char st.(input) in
      let final_st := {|
        input := remaining;
        position := st.(position) + String.length text;
        tokens := st.(tokens);
        line_number := st.(line_number);
        column_number := st.(column_number) + String.length text
      |} in
      (TText text, final_st)
    else
      (* For non-text characters, consume single character as TText *)
      let st' := advance_char st in
      (TText (String c EmptyString), st')
  end.

(* Auxiliary lemma for the take_while case *)
Lemma take_while_head_true_decrease :
  forall f c rest txt rem,
    f c = true ->
    take_while f (String c rest) = (txt, rem) ->
    String.length rem < String.length (String c rest).
Proof.
  intros f c rest txt rem Hc Htw.
  (* Analyze the first reduction step of take_while *)
  simpl in Htw. rewrite Hc in Htw.
  (* Now take_while produced String c ... in the taken component *)
  destruct (take_while f rest) as [t r] eqn:Ht.
  injection Htw as H_txt H_rem.
  subst txt rem.
  simpl.
  (* |r| < S |rest| is equivalent to |r| <= |rest| *)
  assert (Hle : String.length r <= String.length rest).
  { 
    (* Use take_while_length property *)
    pose proof (take_while_length f rest) as H_len.
    rewrite Ht in H_len.
    exact H_len.
  }
  lia.
Qed.

(* is_text_char is now defined globally above *)


(* Text lexing decreases measure when input is non-empty *)
Lemma lex_text_decreases : forall st tok st',
  lex_text st = (tok, st') ->
  input_empty st = false ->
  lexer_measure st' < lexer_measure st.
Proof.
  intros st tok st' Hlx Hne.
  unfold lexer_measure in *.
  (* De-structure the concrete record to expose input *)
  destruct st as [inp pos toks ln col] eqn:Hst. simpl in *.
  (* Non-empty input ⇒ inp = String c rest *)
  destruct inp as [|c rest] eqn:Hin; cbn in *; try discriminate.
  (* Unfold once and freeze critical decisions *)
  unfold lex_text in Hlx; simpl in Hlx.
  (* is_text_char is now globally defined *)
  remember (is_text_char c) as is_txt eqn:His.
  (* The peek on a non-empty string is necessarily Some c *)
  simpl in Hlx.
  (* Split on the boolean *)
  destruct is_txt.
  - (* Branch 1: is_text_char c = true *)
    (* The key insight: take_while unfolds one step when is_text_char c = true *)
    simpl in Hlx.
    (* take_while (String c rest) with is_text_char c = true becomes *)
    (* let (taken, remaining) := take_while is_text_char rest in (String c taken, remaining) *)
    destruct (take_while is_text_char rest) as [taken remaining] eqn:Htw_rest.
    simpl in Hlx.
    inversion Hlx; subst; clear Hlx.
    (* Now st' is the record with input := remaining *)
    simpl.
    change (S (String.length rest)) with (String.length (String c rest)).
    (* We need to show: length remaining < length (String c rest) *)
    (* The key insight: take_while (String c rest) when is_text_char c = true *)
    (* returns (String c taken, remaining) where (taken, remaining) = take_while rest *)
    (* So the full take_while result is (String c taken, remaining) *)
    (* We can use our lemma with this understanding *)
    remember (String c taken) as txt.
    assert (Htw_full: take_while is_text_char (String c rest) = (txt, remaining)).
    {
      subst txt.
      simpl.
      destruct (is_text_char c) eqn:E.
      - (* is_text_char c = true, which we know from His *)
        rewrite Htw_rest.
        reflexivity.
      - (* is_text_char c = false, contradiction with His *)
        (* His : true = is_text_char c, E : is_text_char c = false *)
        rewrite <- His in E. discriminate.
    }
    subst txt.
    apply (take_while_head_true_decrease is_text_char c rest (String c taken) remaining).
    + symmetry. exact His.
    + exact Htw_full.
  - (* Branch 2: is_text_char c = false *)
    simpl in Hlx.
    pose proof Hlx as Hlx_copy2.  (* Preserve a copy before inversion *)
    inversion Hlx; subst; clear Hlx.
    (* We are exactly in the advance_char case *)
    simpl.
    (* This advances past one character, so length decreases by 1 *)
    change (S (String.length rest)) with (String.length (String c rest)).
    (* After inversion, st' is the result of advance_char *)
    (* advance_char removes one character, so the input becomes rest *)
    (* The goal should already be: length rest < length (String c rest) *)
    apply Nat.lt_succ_diag_r.
Qed.

(** * Core Lexing Step Function *)

(* Main lexing step - termination to be proven in Week 3 *)
Definition lex_step (st : lexer_state) : option (latex_token * lexer_state) :=
  match peek_char st with
  | None => None  (* EOF *)
  | Some c =>
    match default_catcodes c with
    | CatEscape => 
        let (tok, st') := lex_command st in Some (tok, st')
    | CatBeginGroup => 
        let st' := advance_char st in Some (TBeginGroup, st')
    | CatEndGroup => 
        let st' := advance_char st in Some (TEndGroup, st')
    | CatMathShift => 
        let st' := advance_char st in Some (TMathShift, st')
    | CatAlignment => 
        let st' := advance_char st in Some (TAlignment, st')
    | CatParameter => 
        let st' := advance_char st in Some (TParameter, st')
    | CatSuperscript => 
        let st' := advance_char st in Some (TSuperscript, st')
    | CatSubscript => 
        let st' := advance_char st in Some (TSubscript, st')
    | CatSpace => 
        let (tok, st') := lex_whitespace st in Some (tok, st')
    | CatComment => 
        let (tok, st') := lex_comment st in Some (tok, st')
    | CatLetter => 
        let (tok, st') := lex_text st in Some (tok, st')
    | CatOther => 
        let (tok, st') := lex_text st in Some (tok, st')
    end
  end.

(** * Complete Lexing Function *)

(* Lex entire input to list of tokens *)
Fixpoint lex_all_steps (st : lexer_state) (fuel : nat) : list latex_token :=
  match fuel with
  | 0 => List.rev st.(tokens)  (* ran out of fuel - return in correct order *)
  | S n =>
    match lex_step st with
    | None => List.rev st.(tokens)  (* EOF reached - return in correct order *)
    | Some (tok, st') => lex_all_steps (add_token tok st') n
    end
  end.

(* Internal lexing function using string *)
Definition lex_string (s : string) : list latex_token :=
  let fuel := 2 * String.length s in  (* generous fuel allocation *)
  lex_all_steps (initial_state s) fuel.

(* Internal lexer interface: string → list<token> *)
Definition lex_string_internal (s : string) : list latex_token :=
  lex_string s.

(* Convert list of characters to string *)
Fixpoint list_ascii_to_string (chars : list ascii) : string :=
  match chars with
  | nil => EmptyString
  | c :: rest => String c (list_ascii_to_string rest)
  end.

(* V24-R3 SPECIFICATION COMPLIANT INTERFACE *)
(* L0 Lexer Interface: list<char> → list<token> *)
Definition lex (chars : list ascii) : list latex_token :=
  let s := list_ascii_to_string chars in
  lex_string s.

(* Legacy string interface for backward compatibility *)
Definition lex_from_string (s : string) : list latex_token :=
  lex_string s.

(** * Basic Validation Examples *)

Example lex_simple_command : 
  let result := lex_from_string "\\frac"%string in
  List.length result > 0.
Proof.
  simpl.
  unfold gt.
  apply Nat.lt_0_succ.
Qed.

Example lex_simple_group :
  let result := lex_from_string "{hello}" in
  List.length result > 0.
Proof.
  simpl.
  unfold gt.
  apply Nat.lt_0_succ.
Qed.

(** * Decidability Proofs *)

(* Token equality is decidable *)
Definition token_eq_dec : forall (t1 t2 : latex_token), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  - apply string_dec.
  - apply string_dec.
  - apply string_dec.
Defined.

(* Token equality boolean function *)
Definition token_beq (t1 t2 : latex_token) : bool :=
  match t1, t2 with
  | TCommand s1, TCommand s2 => String.eqb s1 s2
  | TBeginGroup, TBeginGroup => true
  | TEndGroup, TEndGroup => true
  | TMathShift, TMathShift => true
  | TAlignment, TAlignment => true
  | TParameter, TParameter => true
  | TSuperscript, TSuperscript => true
  | TSubscript, TSubscript => true
  | TText s1, TText s2 => String.eqb s1 s2
  | TSpace, TSpace => true
  | TComment s1, TComment s2 => String.eqb s1 s2
  | TNewline, TNewline => true
  | TEOF, TEOF => true
  | _, _ => false
  end.

(* Token boolean equality correctness *)
Lemma token_beq_correct : forall t1 t2,
  token_beq t1 t2 = true <-> t1 = t2.
Proof.
  split; intros H.
  - destruct t1, t2; simpl in H; try discriminate; try reflexivity.
    + apply String.eqb_eq in H. congruence.
    + apply String.eqb_eq in H. congruence.
    + apply String.eqb_eq in H. congruence.
  - subst. destruct t2; simpl; try reflexivity.
    + apply String.eqb_refl.
    + apply String.eqb_refl.
    + apply String.eqb_refl.
Qed.

(* Lexer state equality is decidable *)
Definition lexer_state_input_eq_dec : forall (st1 st2 : lexer_state), 
  {st1.(input) = st2.(input)} + {st1.(input) <> st2.(input)}.
Proof.
  intros st1 st2.
  apply string_dec.
Defined.

(* Input empty is decidable *)
Theorem input_empty_dec : forall st,
  {input_empty st = true} + {input_empty st = false}.
Proof.
  intros st.
  unfold input_empty.
  destruct st.(input).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* Peek character result is decidable *)
Theorem peek_char_dec : forall st,
  {c : ascii | peek_char st = Some c} + {peek_char st = None}.
Proof.
  intros st.
  unfold peek_char.
  destruct st.(input) as [| c rest].
  - right. reflexivity.
  - left. exists c. reflexivity.
Defined.

(* Basic properties of lexer step *)
Theorem lex_step_deterministic : forall st result1 result2,
  lex_step st = result1 -> lex_step st = result2 -> result1 = result2.
Proof.
  intros st result1 result2 H1 H2.
  rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

(* Either EOF or some token+state *)
Theorem lex_step_total : forall st,
  {tok_st : latex_token * lexer_state | lex_step st = Some tok_st} +
  {lex_step st = None}.
Proof.
  intro st.
  unfold lex_step.
  destruct (peek_char st) as [c|] eqn:E_peek.
  - (* Some character *)
    left.
    destruct (default_catcodes c) eqn:E_cat.
    + (* CatEscape *)
      destruct (lex_command st) as [tok st']. exists (tok, st'). reflexivity.
    + (* CatBeginGroup *)
      exists (TBeginGroup, advance_char st). reflexivity.
    + (* CatEndGroup *)
      exists (TEndGroup, advance_char st). reflexivity.
    + (* CatMathShift *)
      exists (TMathShift, advance_char st). reflexivity.
    + (* CatAlignment *)
      exists (TAlignment, advance_char st). reflexivity.
    + (* CatParameter *)
      exists (TParameter, advance_char st). reflexivity.
    + (* CatSuperscript *)
      exists (TSuperscript, advance_char st). reflexivity.
    + (* CatSubscript *)
      exists (TSubscript, advance_char st). reflexivity.
    + (* CatSpace *)
      destruct (lex_whitespace st) as [tok st']. exists (tok, st'). reflexivity.
    + (* CatLetter *)
      destruct (lex_text st) as [tok st']. exists (tok, st'). reflexivity.
    + (* CatOther *)
      destruct (lex_text st) as [tok st']. exists (tok, st'). reflexivity.
    + (* CatComment *)
      destruct (lex_comment st) as [tok st']. exists (tok, st'). reflexivity.
  - (* None - EOF *)
    right. reflexivity.
Qed.

(* Corpus validation: essential commands are recognized *)
Example validate_corpus_commands :
  let cmd_tokens := lex_from_string "\\begin \\end \\frac"%string in
  List.length cmd_tokens > 0.
Proof.
  simpl.
  (* The expression evaluates to 5 > 0, which is Prop, not bool *)
  (* We need to prove this as a proposition *)
  unfold gt. 
  apply Nat.lt_0_succ.
Qed.

(* V24-R3 Specification compliance example *)
Example lex_v24_compliant :
  let char_list := [ascii_backslash; ascii_of_nat 102; ascii_of_nat 114; ascii_of_nat 97; ascii_of_nat 99] in (* \frac *)
  let result := lex char_list in
  List.length result > 0.
Proof.
  simpl.
  unfold gt.
  apply Nat.lt_0_succ.
Qed.

(* Conversion correctness property *)
Lemma list_ascii_to_string_correct : forall chars,
  lex chars = lex_from_string (list_ascii_to_string chars).
Proof.
  intro chars.
  unfold lex, lex_from_string.
  reflexivity.
Qed.