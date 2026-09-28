(** * Strict.DecideBytes — the proven decision on the BYTES of a file.

    ADR-012, milestone M2 phase 2.  Phase 1 proved [decide] exact against the
    declarative semantics [Runs] on documents given as trees.  This file
    decides a file given as bytes: [decide_bytes C b] reads it (Lexer.v),
    parses its front matter and body (Front.v) and runs the SAME kernel
    ([Decide.run], [Semantics.Runs]) on the resulting token stream.

    Membership ([in_strict_bytes], decidable: [in_strict_bytes_dec]):
    - the file has at most [max_file_bytes] bytes;
    - it parses ([Front.Parse]: declarative reading, front matter, body);
    - its kernel stream is in the phase-1 tier ([Decide.in_strict_toks]:
      every character safe, every control word undefined or attested, every
      script with an argument) and within the capacity bounds
      ([Decide.bounded]);
    - its kernel stream does not END with [$] (the stream then has no
      [\end{document}]; measured: [$$x$%] at the end of a file gives
      "! Emergency stop." where [Semantics.R_dollar_display_eof] says
      "Display math should end with $$" — a file whose last line ends in
      [$] followed by a comment is the one way bytes reach that rule without
      the end-of-line space the rule was attested with, so it is outside).

    THE LINE OF A NOT-READY.  [Runs] gives a fatal reason and the INDEX of a
    token.  pdfTeX prints [l.N], the line its reader stands on when it stops,
    and that can be after the token of the fatal: after a [$] in display
    math, TeX reads (and expands) the NEXT token before it reports "Display
    math should end with $$" (correction C-84 found that in phase 1).  The
    declarative definition used here needs no knowledge of which rule fired:
    the reported token is the LAST TOKEN THE OUTCOME DEPENDS ON —
    [Determined K ts n o] says that every stream with the first [n] tokens of
    [ts] has the outcome [o] under [Runs]; the reported index [k] is the one
    with [Determined (S k)] and not [Determined k] (unique, since
    [Determined] is monotone: [determined_threshold_unique]).  When no prefix
    determines the outcome (the file ends without [\end{document}]), pdfTeX
    prints no [l.N] and the reported line is 0.  [decide_bytes] computes it
    with [rd], and [decide_bytes_exact] proves it equal to this definition.
    That pdfTeX's [l.N] IS this line is attested, not proved: by the rule
    probes and the byte-level differential (0 disagreements on line).

    The verdict type is phase 1's: [ProvenReady], [ProvenNotReady r ln] with
    [ln] the LINE (0: no line), [NotStrict] for a file outside the fragment. *)

From Coq Require Import List Ascii Bool Arith Lia.
Import ListNotations.
From LaTeXPerfectionist.Strict Require Import Syntax Contract Semantics Decide Lexer Front.

(** The configuration's two contracts: the kernel's (names, signatures) and
    the lexical one (catcodes, structural names). *)
Record bcontract := mkBC { bc_kernel : contract; bc_lex : lexcon }.

(** At most 1,000,000 bytes (the probe family L0/bounds grades a file at the
    bound). *)
Definition max_file_bytes : nat := Nat.mul max_line_bytes (Nat.mul ten ten).

Example max_file_bytes_is_1000000 : max_file_bytes = Nat.mul max_line_bytes 100.
Proof. reflexivity. Qed.

Definition ends_dollar (ts : list tok) : bool :=
  match last ts TSpace with TDollar => true | _ => false end.

(** ** Membership *)

Definition in_strict_bytes (C : bcontract) (b : list ascii) : Prop :=
  length b <= max_file_bytes /\
  exists ks, Parse (bc_lex C) b ks /\
    in_strict_toks (bc_kernel C) (toks_of ks) /\
    bounded (toks_of ks) = true /\
    ends_dollar (toks_of ks) = false.

Definition strict_ks_b (K : contract) (ts : list tok) : bool :=
  forallb (tok_ok K) ts && scripts_ok ts && bounded ts && negb (ends_dollar ts).

Definition in_strict_bytes_b (C : bcontract) (b : list ascii) : bool :=
  Nat.leb (length b) max_file_bytes &&
  match parse (bc_lex C) b with
  | Some ks => strict_ks_b (bc_kernel C) (toks_of ks)
  | None => false
  end.

Lemma strict_ks_b_spec : forall K ts,
  strict_ks_b K ts = true <->
  in_strict_toks K ts /\ bounded ts = true /\ ends_dollar ts = false.
Proof.
  intros K ts. unfold strict_ks_b, in_strict_toks.
  rewrite !andb_true_iff, forallb_forall, Forall_forall, negb_true_iff. tauto.
Qed.

Lemma in_strict_bytes_b_spec : forall C b, in_strict_bytes_b C b = true <-> in_strict_bytes C b.
Proof.
  intros C b. unfold in_strict_bytes_b, in_strict_bytes. rewrite andb_true_iff, Nat.leb_le.
  split.
  - intros [Hl Hp]. split; [exact Hl|].
    destruct (parse (bc_lex C) b) as [ks|] eqn:P; [|discriminate].
    exists ks. split; [apply parse_exact; exact P|]. apply strict_ks_b_spec. exact Hp.
  - intros [Hl [ks [Hp Hs]]]. split; [exact Hl|].
    apply parse_exact in Hp. rewrite Hp. apply strict_ks_b_spec. exact Hs.
Qed.

Theorem in_strict_bytes_dec : forall C b, {in_strict_bytes C b} + {~ in_strict_bytes C b}.
Proof.
  intros C b. destruct (in_strict_bytes_b C b) eqn:E.
  - left. apply in_strict_bytes_b_spec. exact E.
  - right. intro H. apply in_strict_bytes_b_spec in H. congruence.
Qed.

(** ** How far TeX has read when the run stops *)

(** The step at [t] reads the next token to decide whether it STOPS: a [$]
    in display math (tex.web §1197). *)
Definition reads_next (s : state) (t : tok) : bool :=
  match t, s_frames s with
  | TDollar, FShift true _ _ :: _ => true
  | _, _ => false
  end.

(** The number of tokens of [ts] read when [run] stops ([None]: it stops at
    the end of the stream, or needs a token after the last one). *)
Fixpoint rd (K : contract) (s : state) (ts : list tok) : option nat :=
  match ts with
  | [] => None
  | t :: rest =>
      match step K s t (hd_error rest) with
      | Go1 s' => option_map S (rd K s' rest)
      | Go2 s' =>
          match rest with
          | [] => None
          | _ :: r' => option_map (fun n => S (S n)) (rd K s' r')
          end
      | Stop _ =>
          if reads_next s t
          then match rest with [] => None | _ => Some 2 end
          else Some 1
      | Stuck => None
      end
  end.

Definition line_at (ks : list ktok) (k : nat) : nat :=
  match nth_error ks k with Some t => k_line t | None => 0 end.

Definition report_line (ks : list ktok) (r : option nat) : nat :=
  match r with Some n => line_at ks (pred n) | None => 0 end.

(** ** The decider *)

Definition decide_bytes (C : bcontract) (b : list ascii) : verdict :=
  if Nat.leb (length b) max_file_bytes then
    match parse (bc_lex C) b with
    | None => NotStrict
    | Some ks =>
        if strict_ks_b (bc_kernel C) (toks_of ks) then
          match run (bc_kernel C) init (toks_of ks) with
          | Some Compiles => ProvenReady
          | Some (Fatal r _) =>
              ProvenNotReady r (report_line ks (rd (bc_kernel C) init (toks_of ks)))
          | None => NotStrict
          end
        else NotStrict
    end
  else NotStrict.

(** ** The declarative location *)

Definition Determined (K : contract) (ts : list tok) (n : nat) (o : outcome) : Prop :=
  forall rest, Runs K init (firstn n ts ++ rest) o.

(** The line pdfTeX reports for the outcome [o] of the stream of [ks]: the
    line of the last token [o] depends on, or 0 when no prefix determines
    [o]. *)
Definition ReportedLine (K : contract) (ks : list ktok) (o : outcome) (ln : nat) : Prop :=
  (exists k, Determined K (toks_of ks) (S k) o /\ ~ Determined K (toks_of ks) k o
             /\ ln = line_at ks k)
  \/ ((forall n, ~ Determined K (toks_of ks) n o) /\ ln = 0).

(** ** Lemmas about [step] and [rd] *)

Lemma in_math_fresh_tail : forall fs, in_math (fresh_tail fs) = in_math fs.
Proof. intros [|[] r]; reflexivity. Qed.

Lemma step_go1_nx : forall K s t nx nx' s',
  step K s t nx = Go1 s' -> nx' <> Some TDollar -> step K s t nx' = Go1 s'.
Proof.
  intros K [fs o p] t nx nx' s' H Hn.
  destruct t; cbn [step] in *; cbn [s_frames s_out s_pos] in *; try exact H; try discriminate.
  - (* TDollar *)
    destruct fs as [|[|[] sp sb|g sp sb] r]; try exact H; try discriminate;
      destruct nx as [[]|]; try discriminate;
      try (destruct (c_defined K n); [destruct (is_some (c_sig K n))|]; discriminate);
      (destruct nx' as [[]|]; try exact H; contradiction Hn; reflexivity).
  - (* TScript *)
    destruct (negb (in_math fs)); [discriminate|].
    destruct (tail_has up fs); [discriminate|].
    destruct nx as [[]|]; discriminate.
Qed.

Lemma step_stop_nx : forall K s t nx nx' o,
  step K s t nx = Stop o -> reads_next s t = false -> step K s t nx' = Stop o.
Proof.
  intros K [fs ob p] t nx nx' o H Hr.
  destruct t; cbn [step] in *; cbn [s_frames s_out s_pos reads_next] in *; try exact H.
  - destruct fs as [|[|[] sp sb|g sp sb] r]; try exact H; try discriminate.
    + destruct nx as [[]|]; discriminate.
    + destruct nx as [[]|]; discriminate.
  - destruct (negb (in_math fs)); [exact H|].
    destruct (tail_has up fs); [exact H|].
    destruct nx as [[]|]; discriminate.
Qed.

(** A step stops at the token's own position, or (only for an undefined
    name after a display [$]) at the next one. *)
Lemma step_stop_pos : forall K fs ob p t nx r l,
  step K (mkState fs ob p) t nx = Stop (Fatal r l) -> l = p \/ l = S p.
Proof.
  intros K fs ob p t nx r l H.
  destruct t; cbn [step s_frames s_out s_pos] in H.
  - destruct (in_math fs); discriminate.
  - discriminate.
  - destruct (in_math fs); [injection H as _ <-; left; reflexivity|discriminate].
  - destruct (in_math fs); discriminate.
  - destruct fs as [|[] r']; try discriminate; injection H as _ <-; left; reflexivity.
  - destruct fs as [|[|[] sp sb|g sp sb] r'].
    + destruct nx as [[]|]; discriminate.
    + destruct nx as [[]|]; discriminate.
    + destruct nx as [[]|]; try discriminate; try (injection H as _ <-; left; reflexivity).
      destruct (c_defined K n).
      * destruct (is_some (c_sig K n)); [injection H as _ <-; left; reflexivity|discriminate].
      * injection H as _ <-. right. reflexivity.
    + discriminate.
    + injection H as _ <-. left. reflexivity.
  - destruct (in_math fs); [injection H as _ <-; left; reflexivity|discriminate].
  - destruct fs as [|[|[] sp sb|g sp sb] r']; try discriminate;
      injection H as _ <-; left; reflexivity.
  - destruct (in_math fs); [injection H as _ <-; left; reflexivity|discriminate].
  - destruct fs as [|[|[] sp sb|g sp sb] r']; try discriminate;
      injection H as _ <-; left; reflexivity.
  - destruct (negb (in_math fs)); [injection H as _ <-; left; reflexivity|].
    destruct (tail_has up fs); [injection H as _ <-; left; reflexivity|].
    destruct nx as [[]|]; discriminate.
  - destruct (negb (c_defined K n)); [injection H as _ <-; left; reflexivity|].
    destruct (c_sig K n) as [sg|]; [|discriminate].
    destruct (in_math fs);
      [destruct (sig_math sg)|destruct (sig_text sg)]; try discriminate;
      injection H as _ <-; left; reflexivity.
  - destruct (in_math fs); [injection H as _ <-; left; reflexivity|].
    destruct ob; [discriminate|injection H as _ <-; left; reflexivity].
Qed.

(** A step that does not read the next token stops at its own position. *)
Lemma step_stop_self : forall K fs ob p t nx r l,
  step K (mkState fs ob p) t nx = Stop (Fatal r l) ->
  reads_next (mkState fs ob p) t = false -> l = p.
Proof.
  intros K fs ob p t nx r l H Hr.
  destruct (step_stop_pos K fs ob p t nx r l H) as [E|E]; [exact E|exfalso].
  subst l. destruct t; cbn [step s_frames s_out s_pos] in H; cbn [reads_next s_frames] in Hr.
  - destruct (in_math fs); discriminate.
  - discriminate.
  - destruct (in_math fs); [injection H as _ E; lia|discriminate].
  - destruct (in_math fs); discriminate.
  - destruct fs as [|[] r']; try discriminate; injection H as _ E; lia.
  - destruct fs as [|[|[] sp sb|g sp sb] r']; try discriminate.
    + destruct nx as [[]|]; discriminate.
    + destruct nx as [[]|]; discriminate.
    + injection H as _ E; lia.
  - destruct (in_math fs); [injection H as _ E; lia|discriminate].
  - destruct fs as [|[|[] sp sb|g sp sb] r']; try discriminate; injection H as _ E; lia.
  - destruct (in_math fs); [injection H as _ E; lia|discriminate].
  - destruct fs as [|[|[] sp sb|g sp sb] r']; try discriminate; injection H as _ E; lia.
  - destruct (negb (in_math fs)); [injection H as _ E; lia|].
    destruct (tail_has up fs); [injection H as _ E; lia|].
    destruct nx as [[]|]; discriminate.
  - destruct (negb (c_defined K n)); [injection H as _ E; lia|].
    destruct (c_sig K n) as [sg|]; [|discriminate].
    destruct (in_math fs);
      [destruct (sig_math sg)|destruct (sig_text sg)]; try discriminate;
      injection H as _ E; lia.
  - destruct (in_math fs); [injection H as _ E; lia|].
    destruct ob; [discriminate|injection H as _ E; lia].
Qed.

Lemma step_reads_display : forall s t,
  reads_next s t = true ->
  exists sp sb r, t = TDollar /\ s_frames s = FShift true sp sb :: r.
Proof.
  intros [fs o p] t H. destruct t; try discriminate.
  destruct fs as [|[|[] sp sb|g sp sb] r]; try discriminate.
  exists sp, sb, r. split; reflexivity.
Qed.

Lemma rd_pos : forall K s ts n, rd K s ts = Some n -> 1 <= n.
Proof.
  intros K s ts. revert s. induction ts as [|t r IH]; intros s n H; simpl in H; [discriminate|].
  destruct (step K s t (hd_error r)); try discriminate.
  - destruct (rd K s0 r); simpl in H; [injection H as <-; lia|discriminate].
  - destruct r as [|t2 r']; [discriminate|].
    destruct (rd K s0 r'); simpl in H; [injection H as <-; lia|discriminate].
  - destruct (reads_next s t); [destruct r|]; try discriminate; injection H as <-; lia.
Qed.

Lemma hd_firstn_app : forall (ts rest : list tok) n,
  1 <= n -> ts <> [] -> hd_error (firstn n ts ++ rest) = hd_error ts.
Proof.
  intros ts rest n Hn Hts. destruct ts as [|t r]; [contradiction|].
  destruct n as [|n]; [lia|]. reflexivity.
Qed.

Local Ltac rd_run :=
  match goal with
  | [ H : run _ _ (_ :: _) = _ |- _ ] => cbn [run] in H
  end.

(** (A) Once [rd] tokens are read, the rest of the stream does not matter. *)
Lemma rd_stable : forall K k ts s o n,
  length ts <= k -> run K s ts = Some o -> rd K s ts = Some n ->
  forall rest, run K s (firstn n ts ++ rest) = Some o.
Proof.
  intros K k. induction k as [|k IH]; intros ts s o n Hlen Hrun Hrd rest.
  - destruct ts; [discriminate|simpl in Hlen; lia].
  - destruct ts as [|t ts']; [discriminate|].
    simpl in Hlen. cbn [run] in Hrun. cbn [rd] in Hrd.
    destruct (step K s t (hd_error ts')) as [s'|s'|o'|] eqn:St; try discriminate.
    + destruct (rd K s' ts') as [n'|] eqn:R; [|discriminate]. simpl in Hrd. injection Hrd as <-.
      assert (Hne : ts' <> []) by (intro E; subst ts'; discriminate).
      pose proof (rd_pos _ _ _ _ R) as Hp.
      cbn [firstn app run]. rewrite (hd_firstn_app ts' rest n' Hp Hne), St.
      apply (IH ts' s'); [lia|exact Hrun|exact R].
    + destruct ts' as [|t2 r']; [discriminate|].
      destruct (rd K s' r') as [n'|] eqn:R; [|discriminate]. simpl in Hrd. injection Hrd as <-.
      cbn [firstn app run hd_error]. simpl in St. rewrite St.
      apply (IH r' s'); [simpl in Hlen; lia|exact Hrun|exact R].
    + injection Hrun as <-.
      destruct (reads_next s t) eqn:Rn.
      * destruct ts' as [|t2 r']; [discriminate|]. injection Hrd as <-.
        cbn [firstn app run hd_error]. simpl in St. rewrite St. reflexivity.
      * injection Hrd as <-. cbn [firstn app run].
        rewrite (step_stop_nx K s t (hd_error ts') (hd_error rest) o' St Rn). reflexivity.
Qed.

(** A witness stream that is never [$] first, and runs past a stop. *)
Definition zc : ascii := Ascii.zero.

Lemma run_char_end : forall K fs ob p,
  run K (mkState fs ob p) [TChar zc; TEnd] =
  Some (if in_math fs then Fatal E5 (S p) else Compiles).
Proof.
  intros K fs ob p. cbn [run hd_error step s_frames s_out s_pos].
  destruct (in_math fs) eqn:M.
  - cbn [run step s_frames s_out s_pos]. rewrite in_math_fresh_tail, M. reflexivity.
  - cbn [run step s_frames s_out s_pos]. rewrite M. reflexivity.
Qed.

(** (B) One token fewer than [rd] does not determine the outcome. *)
Lemma rd_unstable : forall K k ts s r l n,
  length ts <= k -> run K s ts = Some (Fatal r l) -> rd K s ts = Some n ->
  exists rest, (pred n = 0 -> hd_error rest <> Some TDollar) /\
               run K s (firstn (pred n) ts ++ rest) <> Some (Fatal r l).
Proof.
  intros K k. induction k as [|k IH]; intros ts s r l n Hlen Hrun Hrd.
  - destruct ts; [discriminate|simpl in Hlen; lia].
  - destruct ts as [|t ts']; [discriminate|].
    simpl in Hlen. cbn [run] in Hrun. cbn [rd] in Hrd.
    destruct (step K s t (hd_error ts')) as [s'|s'|o'|] eqn:St; try discriminate.
    + destruct (rd K s' ts') as [n'|] eqn:R; [|discriminate]. simpl in Hrd. injection Hrd as <-.
      assert (Hne : ts' <> []) by (intro E; subst ts'; discriminate).
      destruct (IH ts' s' r l n' ltac:(lia) Hrun R) as [w [Hw Hr]].
      exists w. split; [intro E; simpl in E; pose proof (rd_pos _ _ _ _ R); lia|].
      destruct n' as [|[|n'']]; [pose proof (rd_pos _ _ _ _ R); lia| |].
      * (* the stop is the next token: the witness replaces it *)
        cbn [pred firstn app run]. simpl in Hr.
        rewrite (step_go1_nx K s t (hd_error ts') (hd_error w) s' St (Hw eq_refl)). exact Hr.
      * cbn [pred firstn app run]. simpl pred in Hr.
        destruct ts' as [|t2 r2]; [contradiction|]. cbn [firstn app hd_error].
        simpl in St. rewrite St. exact Hr.
    + destruct ts' as [|t2 r']; [discriminate|].
      destruct (rd K s' r') as [n'|] eqn:R; [|discriminate]. simpl in Hrd. injection Hrd as <-.
      destruct (IH r' s' r l n' ltac:(simpl in Hlen; lia) Hrun R) as [w [Hw Hr]].
      exists w. split; [intro E; simpl in E; discriminate|].
      pose proof (rd_pos _ _ _ _ R) as Hp.
      destruct n' as [|n'']; [lia|].
      cbn [pred firstn app run hd_error]. simpl in St. rewrite St. exact Hr.
    + injection Hrun as Ho. subst o'. destruct s as [fs ob p].
      destruct (reads_next (mkState fs ob p) t) eqn:Rn.
      * destruct ts' as [|t2 r']; [discriminate|]. injection Hrd as <-.
        destruct (step_reads_display _ _ Rn) as [sp [sb [rr [-> Hf]]]].
        simpl in Hf. subst fs.
        destruct (step_stop_pos K _ ob p _ _ r l St) as [-> | ->];
          (exists [TDollar]; split; [intro E; simpl in E; discriminate|];
           cbn [pred firstn app run hd_error step s_frames s_out s_pos];
           intro E; injection E as _ E; lia).
      * injection Hrd as <-.
        rewrite (step_stop_self K _ ob p _ _ r l St Rn).
        exists [TChar zc; TEnd]. split; [intros _; simpl; discriminate|].
        cbn [pred firstn app]. rewrite run_char_end.
        destruct (in_math fs); intro E; injection E as E; [lia|discriminate].
Qed.

(** (C) When [rd] is [None], no prefix determines the outcome. *)
Lemma rd_never : forall K k ts s o,
  length ts <= k -> run K s ts = Some o -> rd K s ts = None ->
  exists w, (ts = [] -> hd_error w <> Some TDollar) /\ run K s (ts ++ w) <> Some o.
Proof.
  intros K k. induction k as [|k IH]; intros ts s o Hlen Hrun Hrd.
  - destruct ts; [|simpl in Hlen; lia].
    destruct s as [fs ob p]. cbn [run s_pos] in Hrun. injection Hrun as <-.
    exists [TChar zc; TEnd]. split; [intros _; simpl; discriminate|].
    simpl app. rewrite run_char_end. destruct (in_math fs); intro E; injection E as E; [lia|discriminate].
  - destruct ts as [|t ts'].
    + destruct s as [fs ob p]. cbn [run s_pos] in Hrun. injection Hrun as <-.
      exists [TChar zc; TEnd]. split; [intros _; simpl; discriminate|].
      simpl app. rewrite run_char_end. destruct (in_math fs); intro E; injection E as E; [lia|discriminate].
    + simpl in Hlen. cbn [run] in Hrun. cbn [rd] in Hrd.
      destruct (step K s t (hd_error ts')) as [s'|s'|o'|] eqn:St; try discriminate.
      * destruct (rd K s' ts') eqn:R; [discriminate|].
        destruct (IH ts' s' o ltac:(lia) Hrun R) as [w [Hw Hr]].
        exists w. split; [intro E; discriminate|].
        cbn [app run].
        destruct ts' as [|t2 r2].
        -- simpl app in *. rewrite (step_go1_nx K s t None (hd_error w) s' St (Hw eq_refl)). exact Hr.
        -- cbn [app hd_error] in *. rewrite St. exact Hr.
      * destruct ts' as [|t2 r']; [discriminate|].
        destruct (rd K s' r') eqn:R; [discriminate|].
        destruct (IH r' s' o ltac:(simpl in Hlen; lia) Hrun R) as [w [Hw Hr]].
        exists w. split; [intro E; discriminate|].
        cbn [app run hd_error]. simpl in St. rewrite St. exact Hr.
      * injection Hrun as <-. destruct s as [fs ob p].
        destruct (reads_next (mkState fs ob p) t) eqn:Rn; [|discriminate].
        destruct ts' as [|t2 r']; [|discriminate].
        destruct (step_reads_display _ _ Rn) as [sp [sb [rr [-> Hf]]]].
        simpl in Hf. subst fs.
        cbn [step s_frames s_out s_pos hd_error] in St. injection St as <-.
        exists [TDollar]. split; [intro E; discriminate|].
        cbn [app run hd_error step s_frames s_out s_pos].
        intro E. injection E as E. lia.
Qed.

(** ** [Determined]: monotone, so the threshold is unique *)

Lemma firstn_S_split : forall (ts : list tok) n,
  firstn (S n) ts = firstn n ts ++ firstn 1 (skipn n ts).
Proof.
  intros ts n. revert ts. induction n as [|n IH]; intros [|t r]; try reflexivity.
  cbn [firstn skipn app]. f_equal. apply IH.
Qed.

Lemma determined_mono : forall K ts n o, Determined K ts n o -> Determined K ts (S n) o.
Proof.
  intros K ts n o H rest. rewrite firstn_S_split, <- app_assoc. apply H.
Qed.

Lemma determined_mono_le : forall K ts n m o,
  n <= m -> Determined K ts n o -> Determined K ts m o.
Proof.
  intros K ts n m o Hle H. induction Hle; [exact H|]. apply determined_mono. exact IHHle.
Qed.

Theorem determined_threshold_unique : forall K ts o k1 k2,
  Determined K ts (S k1) o -> ~ Determined K ts k1 o ->
  Determined K ts (S k2) o -> ~ Determined K ts k2 o -> k1 = k2.
Proof.
  intros K ts o k1 k2 D1 N1 D2 N2.
  destruct (Nat.lt_trichotomy k1 k2) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
  - exfalso. apply N2. apply (determined_mono_le K ts (S k1)); [lia|exact D1].
  - exfalso. apply N1. apply (determined_mono_le K ts (S k2)); [lia|exact D2].
Qed.

Lemma determined_run : forall K ts n o,
  Determined K ts n o <-> forall rest, run K init (firstn n ts ++ rest) = Some o.
Proof.
  intros K ts n o. split.
  - intros H rest. apply run_complete. apply H.
  - intros H rest. apply run_sound. apply H.
Qed.

Theorem reported_line_unique : forall K ks o l1 l2,
  ReportedLine K ks o l1 -> ReportedLine K ks o l2 -> l1 = l2.
Proof.
  intros K ks o l1 l2 [[k1 [D1 [N1 ->]]]|[A1 ->]] [[k2 [D2 [N2 ->]]]|[A2 ->]].
  - f_equal. eapply determined_threshold_unique; eassumption.
  - exfalso. exact (A2 _ D1).
  - exfalso. exact (A1 _ D2).
  - reflexivity.
Qed.

(** What [decide_bytes] reports is the declarative line. *)
Lemma report_line_spec : forall K ks r l,
  run K init (toks_of ks) = Some (Fatal r l) ->
  ReportedLine K ks (Fatal r l) (report_line ks (rd K init (toks_of ks))).
Proof.
  intros K ks r l Hrun. unfold report_line.
  destruct (rd K init (toks_of ks)) as [n|] eqn:R.
  - left. exists (pred n). pose proof (rd_pos _ _ _ _ R) as Hp.
    split; [|split; [|reflexivity]].
    + apply (proj2 (determined_run _ _ _ _)). replace (S (pred n)) with n by lia.
      intro rest. exact (rd_stable K _ _ _ _ _ (le_n _) Hrun R rest).
    + intro D. pose proof (proj1 (determined_run _ _ _ _) D) as D'. clear D. rename D' into D.
      destruct (rd_unstable K _ _ _ _ _ _ (le_n _) Hrun R) as [w [_ Hw]].
      exact (Hw (D w)).
  - right. split; [|reflexivity]. intros n D.
    pose proof (proj1 (determined_run _ _ _ _) D) as D'. clear D. rename D' into D.
    destruct (rd_never K _ _ _ _ (le_n _) Hrun R) as [w [_ Hw]].
    apply Hw. rewrite <- (firstn_skipn n (toks_of ks)), <- app_assoc. apply D.
Qed.

(** ** Exactness of the decision on bytes *)

(** For a file in the fragment, with [ks] its (unique) parse:
    PROVEN READY iff [Runs ... Compiles], and PROVEN NOT-READY with reason
    [r] on line [ln] iff [Runs ... (Fatal r l)] for some [l] and [ln] is
    the declarative reported line of that outcome. *)
Theorem decide_bytes_exact : forall C b ks,
  in_strict_bytes C b -> Parse (bc_lex C) b ks ->
  (decide_bytes C b = ProvenReady <-> Runs (bc_kernel C) init (toks_of ks) Compiles) /\
  (forall r ln, decide_bytes C b = ProvenNotReady r ln <->
     exists l, Runs (bc_kernel C) init (toks_of ks) (Fatal r l) /\
               ReportedLine (bc_kernel C) ks (Fatal r l) ln).
Proof.
  intros C b ks [Hlen [ks' [Hp' Hs]]] Hp.
  rewrite (parse_deterministic _ _ _ _ Hp Hp') in *. clear Hp.
  apply parse_exact in Hp'. apply strict_ks_b_spec in Hs.
  unfold decide_bytes. apply Nat.leb_le in Hlen. rewrite Hlen, Hp', Hs.
  set (K := bc_kernel C). set (ts := toks_of ks').
  split.
  - split.
    + intro H. destruct (run K init ts) as [[|r l]|] eqn:R; try discriminate.
      apply run_sound. exact R.
    + intro H. apply run_complete in H. rewrite H. reflexivity.
  - intros r ln. split.
    + intro H. destruct (run K init ts) as [[|r' l]|] eqn:R; try discriminate.
      injection H as <- <-. exists l. split; [apply run_sound; exact R|].
      apply report_line_spec. exact R.
    + intros [l [Hr HL]]. apply run_complete in Hr. rewrite Hr. f_equal.
      apply (reported_line_unique K ks' (Fatal r l)); [|exact HL].
      apply report_line_spec. exact Hr.
Qed.

(** Outside the fragment, and only there, the answer is [NotStrict]. *)
Theorem decide_bytes_not_strict_iff : forall C b,
  decide_bytes C b = NotStrict <-> ~ in_strict_bytes C b.
Proof.
  intros C b. split.
  - intros H Hin. destruct Hin as [Hlen [ks [Hp Hs]]].
    pose proof Hs as Hs'. apply strict_ks_b_spec in Hs'.
    apply parse_exact in Hp. unfold decide_bytes in H.
    apply Nat.leb_le in Hlen. rewrite Hlen, Hp, Hs' in H.
    destruct (run (bc_kernel C) init (toks_of ks)) as [[|r l]|] eqn:R; try discriminate.
    exact (run_total_n _ _ _ _ (le_n _) (proj1 Hs) R).
  - intro H. unfold decide_bytes.
    destruct (Nat.leb (length b) max_file_bytes) eqn:Hlen; [|reflexivity].
    destruct (parse (bc_lex C) b) as [ks|] eqn:Hp; [|reflexivity].
    destruct (strict_ks_b (bc_kernel C) (toks_of ks)) eqn:Hs; [|reflexivity].
    exfalso. apply H. split; [apply Nat.leb_le; exact Hlen|].
    exists ks. split; [apply parse_exact; exact Hp|]. apply strict_ks_b_spec. exact Hs.
Qed.

Corollary decide_bytes_total : forall C b,
  in_strict_bytes C b -> decide_bytes C b <> NotStrict.
Proof.
  intros C b H E. apply decide_bytes_not_strict_iff in E. contradiction.
Qed.
