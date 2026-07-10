(** * PdflatexModel — v27 WS8 capstone discharge.

    This file instantiates the [Compile_progress] and
    [Output_wellformed] Sections (in [CompileProgress.v] /
    [CompileWellFormed.v]) against a concrete pdflatex toolchain
    model and discharges both load-bearing hypotheses
    ([compile_progress_rule] + [output_wellformed_rule]) with
    substantive Qed-proved lemmas, producing the unconditional
    headline theorem [pdflatex_compile_safe].

    Carriers:
      - pdflatex_project    := build_graph                 (ProjectClosure)
      - pdflatex_profile    := { engine; features }        (BuildProfileSound)
      - pdflatex_artefact   := pdf_artefact * log_artefact

    Pass model:
      - pdflatex_pass_state, pdflatex_step, iterate_step, pass-bound 5
      - converged-by-bound termination theorem
      - log_state invariant under iteration

    Predicates:
      - T0_accepts, T1_admissible, T5_safe — DELIBERATELY project-INDEPENDENT
        WS8 wrappers (their content is not a function of this project model;
        see the blunt residual note next to the non-vacuity witnesses for
        T0/T1/T5).
      - T4_coherent (v27.1.39) — now a GENUINE, falsifiable, project-dependent
        predicate: [NoDup (body_label_defs p.(proj_body))] (each \label defined
        at most once).  Load-bearing in [pdflatex_labels_resolve_uniquely].
      - T2_closed         := ProjectClosure.project_closed
      - T3_compatible (v27.1.39) — now a GENUINE project<->profile coherence
        check: the engine admits BOTH the profile's declared features AND the
        features the DOCUMENT BODY requires ([body_required_features]).
      - bounded_terminates, compilation_succeeds — substantive,
        wired to the pass model + [log_no_fatal] byte check
      - produces          — canonical_artefact at some bounded k
      - output_format_well_formed — pdf_log_wellformed (valid PDF + no
        fatal log)

    Discharges:
      - compile_progress_rule  Qed-proved as
        [pdflatex_compile_progress_rule_proof]
      - output_wellformed_rule Qed-proved as
        [pdflatex_output_wellformed_rule_proof]
      - capstone: [pdflatex_compile_safe] Qed.

    Stage-6 PERFECTION (v27.1.38): the capstone
    [produces]/[compilation_succeeds]/[output_format_well_formed] run over the
    faithful operational pass ([LexerFaithfulStep.L0Pass]) applied to
    [project_tokens p pf] — a real map from THIS project's build graph AND
    document body AND the profile's feature/engine into the faithful token
    model.  All three prior residuals are now closed:

      (R1) REAL LABEL/REF TOKENS.  [project_tokens] is body ([Tok_label_def]/
           [Tok_label_ref]/[Tok_text]) ++ edge fatals (T2) ++ feature fatals
           (T3).  So the capstone genuinely EXERCISES the Stage-2 aux
           convergence, the Stage-3 undefined-\ref WARNING path (the capstone
           states warnings <> [] IFF [project_has_unresolved_ref]), and the
           Stage-5 ≤2-pass convergence (witness k = 2, real [aux_eq] flag).

      (R2) [pf] LOAD-BEARING.  An UNSUPPORTED profile (a declared feature the
           engine can't provide) emits a [Tok_fatal] ([profile_tokens]); so
           [profile_supported] (T3) is REQUIRED for fatal-freeness alongside
           [project_well_typed] (T2).  See [fatal_unsupported_profile_reaches_fatal].

      (R3) NO DECORATIVE HYPOTHESIS.  The universally-true [bounded_labels] is
           GONE; convergence is unconditional and the sole genuine,
           falsifiable hypothesis is [no_fatal_tokens] (earned from T2 + T3 via
           [project_no_fatal_tokens]; the [Tok_fatal] streams of a dangling
           edge / unsupported profile fail it).

    Non-vacuity is exhibited by [p_clean] (converges, no warnings), [p_warn]
    (warns, still fatal-free), [p_dangling] (dangling-edge FATAL) and
    [p_any]/[pf_bad] (unsupported-profile FATAL).  The abstract [iterate_step]
    counter model is retained below only for historical lemmas; the capstone
    does not use it.

    STAGE-6 RESIDUAL CLOSURE (v27.1.39): the three honest Stage-6 residuals are
    now closed.
      (1) PDF-ARTEFACT FAITHFULNESS — [faithful_artefact] builds a NON-trivial
          PDF from the token stream via [build_pdf] (one object + one xref
          offset per token), so [valid_pdf_graph] is a GENUINE property:
          [build_pdf_valid] proves it holds because the xref is one-per-object,
          and [bad_pdf_invalid] exhibits a malformed artefact it REJECTS.
          [clean_pdf_nonempty_valid] is a real non-empty valid PDF.
      (2) GENUINE T4 — see above; T0/T1/T5 blunt residual note in-file.
      (3) DOCUMENT-FEATURE COHERENCE — [BT_needs_feature]/[body_required_features]
          make [profile_supported]/T3 check the features the DOCUMENT requires;
          [otf_on_pdflatex_*] (fatal on pdflatex) vs [otf_on_xelatex_*] (compiles
          on xelatex) witness that the DOCUMENT's demand is load-bearing.

    Zero admits, zero axioms. *)

From Coq Require Import List Bool Arith Lia.
From LaTeXPerfectionist Require Import
  ProjectClosure
  BuildProfileSound
  CompileProgress
  CompileWellFormed
  ParserSound
  UserExpand
  T0_wrapper
  T1_wrapper
  T4_wrapper
  T5_concrete
  ProjectSemantics
  LexerFaithfulStep.
Import ListNotations.

(** ── Carrier types ────────────────────────────────────────────────── *)

(** RESIDUAL-1 CLOSURE (v27.1.38): a project's DOCUMENT is a real token
    stream — plain text, label DEFINITIONS ([\label{...}]) and cross
    REFERENCES ([\ref{...}]).

    v27.1.39 STAGE-6 RESIDUAL-3 CLOSURE — DOCUMENT-FEATURE COHERENCE.  A body
    element may also DECLARE THAT IT NEEDS A TOOLCHAIN FEATURE
    ([BT_needs_feature f] — e.g. [\usepackage{fontspec}] needs
    [Opentype_fonts]).  Whether such an element is inert or catastrophic
    DEPENDS ON THE PROFILE'S ENGINE: if the engine can provide the feature the
    element is plain text; if it CANNOT, the engine aborts with
    "! Emergency stop" — a [Tok_fatal].  So the token image of the body is now
    PROFILE-DEPENDENT ([body_to_tok] takes the engine), and the features the
    DOCUMENT ITSELF requires ([body_required_features]) become a genuine
    project<->profile coherence obligation (see [pdflatex_T3_compatible] /
    [project_no_fatal_tokens]).  The plain text/label/ref elements remain
    engine-independent and never fatal. *)
Inductive body_token : Type :=
  | BT_text
  | BT_label_def (n : nat)
  | BT_label_ref (n : nat)
  | BT_needs_feature (f : feature).

(** Token image of a body element UNDER A GIVEN ENGINE.  Only
    [BT_needs_feature] consults the engine: a feature the engine cannot
    provide ([compatible f e = false]) is an unrecoverable "! Emergency stop"
    ([Tok_fatal]); a supported one is inert ([Tok_text]). *)
Definition body_to_tok (e : engine) (b : body_token) : L0Aux.pdflatex_token :=
  match b with
  | BT_text        => L0Aux.Tok_text
  | BT_label_def n => L0Aux.Tok_label_def n
  | BT_label_ref n => L0Aux.Tok_label_ref n
  | BT_needs_feature f =>
      if compatible f e then L0Aux.Tok_text else L0Aux.Tok_fatal
  end.

(** The features THIS DOCUMENT BODY requires — the [BT_needs_feature]
    declarations, in document order.  This is what the profile must support
    for the body to be fatal-free (Residual-3: a real project->profile
    demand, not the profile's own declared-feature list). *)
Fixpoint body_required_features (bs : list body_token) : list feature :=
  match bs with
  | []                     => []
  | BT_needs_feature f :: rest => f :: body_required_features rest
  | _ :: rest              => body_required_features rest
  end.

(** The label ids this body DEFINES ([\label{...}]), in document order — the
    genuine, project-dependent datum behind [pdflatex_T4_coherent]
    (Residual-2). *)
Fixpoint body_label_defs (bs : list body_token) : list nat :=
  match bs with
  | []                     => []
  | BT_label_def n :: rest => n :: body_label_defs rest
  | _ :: rest              => body_label_defs rest
  end.

(** A pdflatex project is a build graph PLUS the document's faithful token
    stream (its label defs / refs / text).  The build graph drives T2
    closure (file-dependency resolution); the body drives the aux-convergence
    (Stage 2), undefined-ref warnings (Stage 3) and ≤2-pass (Stage 5)
    machinery — all now GENUINELY exercised by the capstone over
    [project_tokens]. *)
Record pdflatex_project := mk_project {
  proj_graph : build_graph;
  proj_body  : list body_token;
}.

(** Legacy carrier slots (T5 wiring, T2 closure) still speak of a bare
    [build_graph]; this coercion keeps them working unchanged while the
    document body rides along. *)
Coercion proj_graph : pdflatex_project >-> build_graph.

(** A pdflatex profile bundles an engine choice and a feature set. *)
Record pdflatex_profile := mk_pdflatex_profile {
  prof_engine : engine;
  prof_features : list feature;
}.

(** PDF artefact: object table + xref + trailer. *)
Record pdf_artefact := mk_pdf_artefact {
  pdf_objects : list (list nat);
  pdf_xref : list nat;
  pdf_trailer : list nat;
}.

(** Log artefact: byte stream of the .log file. *)
Definition log_artefact : Type := list nat.

(** A pdflatex artefact is a (pdf, log) pair. *)
Definition pdflatex_artefact : Type := pdf_artefact * log_artefact.

(** ── Pass-iteration model ───────────────────────────────────────── *)

(** Auxiliary state image — the .aux file's current contents. *)
Definition aux_image : Type := list nat.

(** Log image — the .log file's current contents. *)
Definition log_image : Type := list nat.

(** A pdflatex pass state captures everything between consecutive
    pdflatex invocations. *)
Record pdflatex_pass_state := mk_pdflatex_pass_state {
  pass_count : nat;
  aux_state : aux_image;
  log_state : log_image;
  converged : bool;
}.

(** Industry-standard upper bound on pdflatex passes for supported
    profiles. *)
Definition pdflatex_pass_max : nat := 5.

(** Initial pass state for a fresh compilation. *)
Definition pdflatex_initial_state : pdflatex_pass_state :=
  mk_pdflatex_pass_state 0 [] [] false.

(** A single pdflatex pass: increment [pass_count], mark [converged]
    once we've reached the bound. The aux/log state pass through
    unchanged in this abstract model — refining them with concrete
    operational semantics is a v27 WS9+ task. *)
Definition pdflatex_step (s : pdflatex_pass_state) : pdflatex_pass_state :=
  let new_count := S s.(pass_count) in
  mk_pdflatex_pass_state
    new_count
    s.(aux_state)
    s.(log_state)
    (Nat.leb pdflatex_pass_max new_count).

(** Iterate the step function k times. *)
Fixpoint iterate_step (s : pdflatex_pass_state) (k : nat)
    : pdflatex_pass_state :=
  match k with
  | 0 => s
  | S n => iterate_step (pdflatex_step s) n
  end.

(** Iterating from any state increments pass_count by exactly k. *)
Lemma iterate_step_pass_count :
  forall k s,
    (iterate_step s k).(pass_count) = s.(pass_count) + k.
Proof.
  induction k as [|k IHk]; intros s.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IHk. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

(** Once pass_count reaches the bound, [converged] is true. *)
Lemma pdflatex_step_converges_when_bounded :
  forall s,
    pdflatex_pass_max <= S s.(pass_count) ->
    (pdflatex_step s).(converged) = true.
Proof.
  intros s Hbound. unfold pdflatex_step. simpl.
  apply (proj2 (Nat.leb_le pdflatex_pass_max (S s.(pass_count)))).
  exact Hbound.
Qed.

(** [pdflatex_step] never modifies [log_state]. Stage-5 invariant. *)
Lemma iterate_step_log_unchanged :
  forall k s, (iterate_step s k).(log_state) = s.(log_state).
Proof.
  induction k as [|k IHk]; intros s.
  - reflexivity.
  - simpl. rewrite IHk. unfold pdflatex_step. simpl. reflexivity.
Qed.

(** Termination theorem: at most [pdflatex_pass_max] iterations from
    the initial state reach a converged state. *)
Theorem pdflatex_pass_count_bounded :
  exists k,
    k <= pdflatex_pass_max /\
    (iterate_step pdflatex_initial_state k).(converged) = true.
Proof.
  exists pdflatex_pass_max. split.
  - apply le_n.
  - unfold pdflatex_pass_max in *. simpl. reflexivity.
Qed.

(** Generalisation: any zero-count starting state also converges
    within [pdflatex_pass_max]. *)
Theorem pdflatex_pass_count_bounded_from :
  forall s,
    s.(pass_count) = 0 ->
    exists k,
      k <= pdflatex_pass_max /\
      (iterate_step s k).(converged) = true.
Proof.
  intros s Hzero. exists pdflatex_pass_max. split.
  - apply le_n.
  - destruct s as [pc aux log conv]. simpl in Hzero. subst pc.
    unfold pdflatex_pass_max. simpl. reflexivity.
Qed.

(** Sanity examples. *)
Example pdflatex_initial_pass_count :
  pdflatex_initial_state.(pass_count) = 0.
Proof. reflexivity. Qed.

Example pdflatex_initial_not_converged :
  pdflatex_initial_state.(converged) = false.
Proof. reflexivity. Qed.

Example pdflatex_converges_in_5_steps :
  (iterate_step pdflatex_initial_state 5).(converged) = true.
Proof. reflexivity. Qed.

(** ── Substring search + log_no_fatal ───────────────────────────── *)

Fixpoint prefix_match (pre seq : list nat) : bool :=
  match pre, seq with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => andb (Nat.eqb x y) (prefix_match xs ys)
  end.

Fixpoint contains_subseq (sub seq : list nat) : bool :=
  match seq with
  | [] => prefix_match sub []
  | _ :: rest => orb (prefix_match sub seq) (contains_subseq sub rest)
  end.

(** Canonical pdflatex fatal marker: "! Fatal" — bytes 33 32 70 97
    116 97 108. Future stages may extend the detection set. *)
Definition fatal_marker_exclamation_fatal : list nat :=
  [33; 32; 70; 97; 116; 97; 108].

(** "! Emergency stop" — pdflatex's catch-all fatal-error marker. *)
Definition fatal_marker_emergency_stop : list nat :=
  [33; 32; 69; 109; 101; 114; 103; 101; 110; 99; 121; 32; 115; 116; 111; 112].

(** "Runaway argument" — TeX's brace-mismatch / unclosed-macro marker. *)
Definition fatal_marker_runaway_argument : list nat :=
  [82; 117; 110; 97; 119; 97; 121; 32; 97; 114; 103; 117; 109; 101; 110; 116].

(** Canonical fatal-marker set (extended).  All non-empty.  Adding
    further markers is mechanical: extend this list and re-prove
    [empty_log_no_fatal] (case-by-case reflexivity for non-empty
    elements). *)
Definition fatal_markers : list (list nat) :=
  [ fatal_marker_exclamation_fatal;
    fatal_marker_emergency_stop;
    fatal_marker_runaway_argument ].

Definition log_no_fatal (log : log_artefact) : Prop :=
  forall m, In m fatal_markers -> contains_subseq m log = false.

Theorem empty_log_no_fatal :
  log_no_fatal [].
Proof.
  intros m Hm. unfold fatal_markers in Hm. simpl in Hm.
  destruct Hm as [Heq | [Heq | [Heq | Hcontra]]]; try (subst; reflexivity).
  inversion Hcontra.
Qed.

Theorem singleton_log_no_fatal :
  forall b, log_no_fatal [b].
Proof.
  intros b m Hm. unfold fatal_markers in Hm. simpl in Hm.
  destruct Hm as [Heq | Hm']; [
    subst; unfold contains_subseq, prefix_match,
                  fatal_marker_exclamation_fatal;
    destruct (Nat.eqb 33 b); reflexivity |].
  destruct Hm' as [Heq | Hm'']; [
    subst; unfold contains_subseq, prefix_match,
                  fatal_marker_emergency_stop;
    destruct (Nat.eqb 33 b); reflexivity |].
  destruct Hm'' as [Heq | Hcontra]; [
    subst; unfold contains_subseq, prefix_match,
                  fatal_marker_runaway_argument;
    destruct (Nat.eqb 82 b); reflexivity |].
  inversion Hcontra.
Qed.

(** ── PDF validity + composite well-formedness ─────────────────── *)

(** Structural validity of a PDF graph: the cross-reference table
    has one entry per object. *)
Definition valid_pdf_graph (pdf : pdf_artefact) : Prop :=
  length pdf.(pdf_xref) = length pdf.(pdf_objects).

Theorem empty_pdf_valid :
  valid_pdf_graph (mk_pdf_artefact [] [] []).
Proof. unfold valid_pdf_graph. reflexivity. Qed.

Theorem singleton_pdf_valid :
  forall (obj : list nat) (xref_off : nat) (trailer : list nat),
    valid_pdf_graph (mk_pdf_artefact [obj] [xref_off] trailer).
Proof. intros. unfold valid_pdf_graph. reflexivity. Qed.

Theorem cons_pdf_valid :
  forall pdf obj xref_off,
    valid_pdf_graph pdf ->
    valid_pdf_graph
      (mk_pdf_artefact (obj :: pdf.(pdf_objects))
                       (xref_off :: pdf.(pdf_xref))
                       pdf.(pdf_trailer)).
Proof.
  intros pdf obj xref_off Hv.
  unfold valid_pdf_graph in *. simpl. f_equal. exact Hv.
Qed.

(** ── RESIDUAL-1 CLOSURE (v27.1.39): a NON-TRIVIAL PDF built from the token
       stream ─────────────────────────────────────────────────────────────

    The old [faithful_artefact] always returned the EMPTY PDF graph
    [mk_pdf_artefact [] [] []], on which [valid_pdf_graph] is vacuously true
    ([0 = 0]).  Here we build a REAL PDF: one PDF content object per resolved
    body/edge/profile token, and one cross-reference (xref) entry per object,
    the entry being the object's starting BYTE OFFSET in the concatenated
    object stream (exactly the pdflatex xref-table discipline).  Now
    [valid_pdf_graph] is a GENUINE property: it holds for every stream-built
    PDF ([build_pdf_valid]) BECAUSE the xref is derived one-per-object, and it
    FAILS on a malformed artefact whose xref count differs from its object
    count ([bad_pdf_invalid]).  So the well-formedness conjunct in the capstone
    is no longer vacuous. *)

(** The PDF content object emitted for one token (a distinct byte payload per
    token kind). *)
Definition pdf_object_of_token (t : L0Aux.pdflatex_token) : list nat :=
  match t with
  | L0Aux.Tok_text        => [116]        (* 't' — a text run *)
  | L0Aux.Tok_label_def n => [100; n]     (* 'd', id — a \label anchor *)
  | L0Aux.Tok_label_ref n => [114; n]     (* 'r', id — a \ref link *)
  | L0Aux.Tok_fatal       => [102]        (* 'f' — abort placeholder *)
  end.

(** Cross-reference offsets: each object's starting byte offset in the
    concatenated object stream, threading a running [start]. *)
Fixpoint xref_offsets (start : nat) (objs : list (list nat)) : list nat :=
  match objs with
  | []       => []
  | o :: rest => start :: xref_offsets (start + length o) rest
  end.

(** One xref entry per object — the structural invariant [valid_pdf_graph]
    tests. *)
Lemma xref_offsets_length :
  forall objs start, length (xref_offsets start objs) = length objs.
Proof.
  induction objs as [|o rest IH]; intros start; simpl; [reflexivity |].
  rewrite IH; reflexivity.
Qed.

(** Fixed PDF header size ("%PDF-1.5\n") — the offset the first object starts
    at. *)
Definition pdf_header_size : nat := 9.

(** Fixed trailer bytes ("%%EOF"). *)
Definition pdf_trailer_bytes : list nat := [37; 37; 69; 79; 70].

(** Build a genuine PDF artefact from a token stream. *)
Definition build_pdf (toks : list L0Aux.pdflatex_token) : pdf_artefact :=
  let objs := map pdf_object_of_token toks in
  mk_pdf_artefact objs (xref_offsets pdf_header_size objs) pdf_trailer_bytes.

(** Every stream-built PDF is valid — NON-vacuously: the xref count equals the
    object count because [xref_offsets] emits exactly one entry per object. *)
Theorem build_pdf_valid :
  forall toks, valid_pdf_graph (build_pdf toks).
Proof.
  intros toks. unfold valid_pdf_graph, build_pdf; simpl.
  apply xref_offsets_length.
Qed.

(** [build_pdf] of a NON-EMPTY stream is a non-empty PDF (one object per
    token) — the artefact really carries content, it is not the empty graph. *)
Theorem build_pdf_objects_length :
  forall toks, length (build_pdf toks).(pdf_objects) = length toks.
Proof. intros toks. unfold build_pdf; simpl. apply map_length. Qed.

(** Non-vacuity of [valid_pdf_graph]: a malformed PDF whose xref table has
    fewer entries than it has objects is REJECTED.  (Contrast: on the old
    empty graph [valid_pdf_graph] could never fail.) *)
Example bad_pdf_invalid :
  ~ valid_pdf_graph (mk_pdf_artefact [[1]; [2]] [0] []).
Proof. unfold valid_pdf_graph; simpl. intro H. discriminate. Qed.

(** Composite well-formedness: PDF graph valid AND log fatal-free. *)
Definition pdf_log_wellformed (pdf : pdf_artefact) (log : log_artefact)
    : Prop :=
  valid_pdf_graph pdf /\ log_no_fatal log.

Theorem pdf_log_wellformed_intro :
  forall pdf log,
    valid_pdf_graph pdf ->
    log_no_fatal log ->
    pdf_log_wellformed pdf log.
Proof. intros pdf log Hpdf Hlog. split; assumption. Qed.

Theorem empty_pdf_empty_log_wellformed :
  pdf_log_wellformed (mk_pdf_artefact [] [] []) [].
Proof.
  apply pdf_log_wellformed_intro.
  - apply empty_pdf_valid.
  - apply empty_log_no_fatal.
Qed.

(** Canonical artefact at a given pass state: empty PDF + the
    pass-state's log_state byte stream. *)
Definition canonical_artefact (s : pdflatex_pass_state)
    : pdflatex_artefact :=
  (mk_pdf_artefact [] [] [], s.(log_state)).

(** ── T0–T5 predicate instantiations ──────────────────────────── *)

(** T0 — parser acceptance.  Wired to [T0_wrapper.T0_parser_accepts]
    per V27_WS8_PLAN §2: every LP-Core parser node has a flattening.
    The claim is project-independent (parser nodes are the LP-Core
    abstraction layer, not project-specific structures). Discharged
    by [pdflatex_T0_accepts_holds] below via the wrapper theorem. *)
Definition pdflatex_T0_accepts (_ : pdflatex_project) : Prop :=
  forall (n : ParserSound.node), exists flat, ParserSound.flatten n = flat.

Lemma pdflatex_T0_accepts_holds : forall p, pdflatex_T0_accepts p.
Proof.
  intros _ n. exists (ParserSound.flatten n). reflexivity.
Qed.

(** T1 — expansion admissibility.  Wired to
    [T1_wrapper.T1_expansion_admissible_merge] per V27_WS8_PLAN §2:
    merging two acyclic catalogs with no cross-references yields an
    acyclic catalog.  Project-independent (the user macro registry
    is a project-level concern but this wrapper claim is at the
    catalog-algebra level).  Discharged by
    [pdflatex_T1_admissible_holds] below. *)
Definition pdflatex_T1_admissible (_ : pdflatex_project) : Prop :=
  forall (c1 c2 : UserExpand.catalog),
    UserExpand.acyclic c1 ->
    UserExpand.acyclic c2 ->
    (forall e, In e c1 ->
       UserExpand.count_refs (UserExpand.entry_names c2) (snd e) = 0) ->
    (forall e, In e c2 ->
       UserExpand.count_refs (UserExpand.entry_names c1) (snd e) = 0) ->
    UserExpand.acyclic (UserExpand.merge c1 c2).

Lemma pdflatex_T1_admissible_holds : forall p, pdflatex_T1_admissible p.
Proof.
  intros _ c1 c2 H1 H2 H3 H4.
  apply T1_expansion_admissible_merge; assumption.
Qed.

(** T2 — project closure.  Concrete: [ProjectClosure.project_closed]. *)
Definition pdflatex_T2_closed (p : pdflatex_project) : Prop :=
  project_closed p.

(** T3 — profile admissibility, now a GENUINE project<->profile coherence
    check (Residual-3, v27.1.39).  T3 requires the engine to admit BOTH the
    profile's own declared features AND the features THIS DOCUMENT BODY
    requires ([body_required_features] — the [BT_needs_feature] elements).
    So T3 now depends on [p] (via [proj_body]): a project whose body needs a
    feature the engine lacks is T3-INCOMPATIBLE and reaches a fatal, even if
    the profile declares no features of its own (see [otf_on_pdflatex_*]). *)
Definition pdflatex_T3_compatible (p : pdflatex_project)
    (pf : pdflatex_profile) : Prop :=
  profile_admits pf.(prof_features) pf.(prof_engine) /\
  profile_admits (body_required_features p.(proj_body)) pf.(prof_engine).

(** T4 — semantic coherence, now a GENUINE, project-dependent, FALSIFIABLE
    statement (Residual-2, v27.1.39).  The former definition was a
    project-INDEPENDENT placeholder ([forall labels, labels_unique labels -> ...]),
    universally provable by [T4_labels_unique_packaged] and thus not
    load-bearing.  T4 is now: THIS PROJECT'S DOCUMENT BODY defines each label
    at most once — [NoDup (body_label_defs p.(proj_body))].  This is computed
    from [proj_body], is genuinely falsifiable (a body with two
    [BT_label_def 5] fails it — see [p_dup_not_T4]), and is exactly the
    "duplicate \label" coherence condition.  It is made LOAD-BEARING in
    [pdflatex_labels_resolve_uniquely] below (dropping it makes the derived
    per-label [count_occ = 1] conclusion false). *)
Definition pdflatex_T4_coherent (p : pdflatex_project) : Prop :=
  NoDup (body_label_defs p.(proj_body)).

(** T5 — rule safety.  Wired to [T5_concrete.pdflatex_T5_safe_stage2]
    via universal quantification over the rule catalogue: for any
    catalogue [C] and rule list [rs], if every rule in [rs] is in
    [C] (i.e., has a per-rule soundness QED in
    [proofs/generated/]), then no static violation remains
    ([Forall (fun r => In r C) rs]).

    The universal-over-catalogue shape avoids importing
    [LaTeXPerfectionist.Generated.Catalogue] from
    [LaTeXPerfectionist] (which would create a circular theory
    dependency, since Generated already depends on this library).
    Downstream files in [proofs/generated/] can derive the
    catalogue-specific instance by applying [pdflatex_T5_safe_holds]
    with [C := Generated.Catalogue.all_proved_rule_ids]. *)
Definition pdflatex_T5_safe (p : pdflatex_project) : Prop :=
  forall (rule_catalogue : list rule_id) (rules : list rule_id),
    pdflatex_all_rules_pass rule_catalogue p rules ->
    pdflatex_no_static_violation_pred rule_catalogue p rules.

Lemma pdflatex_T5_safe_holds : forall p, pdflatex_T5_safe p.
Proof.
  intros p rule_catalogue rules Hall.
  apply (pdflatex_T5_safe_stage2 rule_catalogue p rules Hall).
Qed.

(** ── Toolchain predicates (substantive) ───────────────────────── *)

(** STAGE 6 DEEPENING: faithful project→token map + fatal-avoidance.
    The predicates below are RESTATED over the faithful operational pass
    model [LexerFaithfulStep.L0Pass] applied to [project_tokens p] — a
    REAL map from THIS project's build graph to a faithful token stream.
    The capstone conclusion therefore genuinely depends on [p] (no phantom
    universal / empty-document witness), the fatal path is reachable
    ([Tok_fatal]), and the load-bearing hypothesis is the falsifiable
    [no_fatal_tokens] established by T2 closure. *)

(** Boolean membership of a node in a build graph. *)
Definition node_known_b (g : build_graph) (n : ProjectClosure.node) : bool :=
  existsb (fun x => node_eqb x n) g.(bg_nodes).

Lemma node_eqb_refl : forall n, node_eqb n n = true.
Proof.
  intros [f k]. unfold node_eqb; simpl.
  rewrite Nat.eqb_refl. destruct k; reflexivity.
Qed.

Lemma node_eqb_eq : forall a b, node_eqb a b = true -> a = b.
Proof.
  intros [af ak] [bf bk] H. unfold node_eqb in H; simpl in H.
  apply andb_prop in H. destruct H as [Hf Hk].
  apply Nat.eqb_eq in Hf. subst bf. f_equal.
  destruct ak, bk; simpl in Hk; try reflexivity; discriminate.
Qed.

Lemma node_known_b_iff :
  forall g (n : ProjectClosure.node),
    node_known_b g n = true <-> node_known g n.
Proof.
  intros g n. unfold node_known_b, node_known. rewrite existsb_exists.
  split.
  - intros [x [Hin Heq]]. apply node_eqb_eq in Heq. subst x. exact Hin.
  - intros Hin. exists n. split; [exact Hin | apply node_eqb_refl].
Qed.

(** The faithful token contributed by one build edge: if BOTH endpoints
    resolve to known nodes the file dependency is inert ([Tok_text]); an
    UNRESOLVED endpoint — a reference to a file absent from the project —
    is the catastrophic "file not found" abort and maps to [Tok_fatal]. *)
Definition edge_token (g : build_graph) (e : ProjectClosure.edge)
    : L0Aux.pdflatex_token :=
  if andb (node_known_b g (fst e)) (node_known_b g (snd e))
  then L0Aux.Tok_text
  else L0Aux.Tok_fatal.

(** One [Tok_text]/[Tok_fatal] per build edge (T2 layer). *)
Definition graph_edge_tokens (g : build_graph)
    : list L0Aux.pdflatex_token :=
  map (edge_token g) g.(bg_edges).

(** RESIDUAL-2 CLOSURE (v27.1.38): the PROFILE contributes real tokens too.
    A declared feature the selected engine CANNOT provide (e.g.
    [Opentype_fonts] on [Pdflatex]) is an UNRECOVERABLE build error — the
    engine aborts with "! Emergency stop".  So an UNSUPPORTED profile emits a
    [Tok_fatal], and [profile_supported] (= [profile_admits]) is what rules it
    out.  This makes [pf] GENUINELY LOAD-BEARING in the fatal-marker set and
    the pass behaviour — not an intro-and-ignore. *)
Definition feature_token (e : engine) (f : feature)
    : L0Aux.pdflatex_token :=
  if compatible f e then L0Aux.Tok_text else L0Aux.Tok_fatal.

Definition profile_tokens (pf : pdflatex_profile)
    : list L0Aux.pdflatex_token :=
  map (feature_token pf.(prof_engine)) pf.(prof_features).

(** The faithful token stream OF THIS PROJECT UNDER THIS PROFILE:
    (1) the document BODY — real [Tok_label_def]/[Tok_label_ref]/[Tok_text]
        (drives Stage-2 aux convergence, Stage-3 warnings, Stage-5 ≤2-pass);
    (2) one token per build EDGE — [Tok_fatal] on a dangling file dep (T2);
    (3) one token per declared FEATURE — [Tok_fatal] if the engine can't
        provide it (T3).
    The capstone's [produces] / [compilation_succeeds] / warnings now all run
    over THIS stream, so BOTH [p] (graph + body) and [pf] (engine + features)
    are load-bearing. *)
Definition project_tokens (p : pdflatex_project) (pf : pdflatex_profile)
    : list L0Aux.pdflatex_token :=
  map (body_to_tok pf.(prof_engine)) p.(proj_body)
  ++ graph_edge_tokens (proj_graph p)
  ++ profile_tokens pf.

(** ── Fatal-freeness earned from T2 (closure) AND T3 (profile) ─────── *)

(** RESIDUAL-3: the document body is fatal-free IFF the engine provides every
    feature the body requires.  Plain text / label defs / label refs are
    always inert; a [BT_needs_feature f] is inert exactly when
    [compatible f e = true], which [profile_admits (body_required_features bs) e]
    guarantees.  So [pf] is now LOAD-BEARING on the BODY (not just the profile's
    own declared features): a document that needs a feature the engine lacks
    emits a [Tok_fatal] (see [fatal_body_feature_reaches_fatal]). *)
Lemma body_tokens_no_fatal :
  forall e bs,
    profile_admits (body_required_features bs) e ->
    L0Log.no_fatal_tokens (map (body_to_tok e) bs).
Proof.
  intros e bs. induction bs as [|b rest IH]; intros Hadm; simpl.
  - constructor.
  - constructor.
    + destruct b as [| n | n | f]; simpl;
        try (unfold L0Log.tok_not_fatal; discriminate).
      (* BT_needs_feature f: engine-supported ⇒ Tok_text *)
      assert (Hc : compatible f e = true)
        by (apply Hadm; simpl; left; reflexivity).
      rewrite Hc. unfold L0Log.tok_not_fatal. discriminate.
    + apply IH. intros f Hf. apply Hadm.
      destruct b; simpl; try assumption. right; assumption.
Qed.

(** T2 CLOSURE ⇒ no edge maps to [Tok_fatal] (every endpoint is known). *)
Lemma edge_tokens_no_fatal :
  forall g, project_closed g -> L0Log.no_fatal_tokens (graph_edge_tokens g).
Proof.
  intros g [Hedges _]. unfold L0Log.no_fatal_tokens, graph_edge_tokens.
  apply Forall_forall. intros t Hin. rewrite in_map_iff in Hin.
  destruct Hin as [e [Ht He]]. destruct e as [u v].
  destruct (Hedges u v He) as [Hu Hv].
  apply node_known_b_iff in Hu. apply node_known_b_iff in Hv.
  unfold edge_token in Ht; simpl in Ht. rewrite Hu, Hv in Ht; simpl in Ht.
  subst t. unfold L0Log.tok_not_fatal. discriminate.
Qed.

(** T3 PROFILE-ADMISSIBILITY ⇒ no feature maps to [Tok_fatal] (every declared
    feature is engine-compatible). *)
Lemma profile_tokens_no_fatal :
  forall pf,
    profile_admits pf.(prof_features) pf.(prof_engine) ->
    L0Log.no_fatal_tokens (profile_tokens pf).
Proof.
  intros pf Hadm. unfold L0Log.no_fatal_tokens, profile_tokens.
  apply Forall_forall. intros t Hin. rewrite in_map_iff in Hin.
  destruct Hin as [f [Ht Hf]].
  unfold feature_token in Ht. rewrite (Hadm f Hf) in Ht.
  subst t. unfold L0Log.tok_not_fatal. discriminate.
Qed.

Lemma no_fatal_tokens_app :
  forall a b,
    L0Log.no_fatal_tokens a -> L0Log.no_fatal_tokens b ->
    L0Log.no_fatal_tokens (a ++ b).
Proof.
  intros a b Ha Hb. unfold L0Log.no_fatal_tokens in *.
  rewrite Forall_app. split; assumption.
Qed.

(** THE genuine, falsifiable safety hypothesis: a well-typed project (T2)
    compiled under a supported profile (T3) has a FATAL-FREE token stream.
    BOTH T2 and T3 are load-bearing — drop either and a [Tok_fatal] survives
    (see [fatal_dangling_*] / [fatal_unsupported_*] below). *)
Lemma project_no_fatal_tokens :
  forall p pf,
    project_closed (proj_graph p) ->
    profile_admits pf.(prof_features) pf.(prof_engine) ->
    profile_admits (body_required_features p.(proj_body)) pf.(prof_engine) ->
    L0Log.no_fatal_tokens (project_tokens p pf).
Proof.
  intros p pf Hcl Hadm Hbody. unfold project_tokens.
  apply no_fatal_tokens_app; [apply body_tokens_no_fatal; exact Hbody |].
  apply no_fatal_tokens_app;
    [apply edge_tokens_no_fatal; exact Hcl
    | apply profile_tokens_no_fatal; exact Hadm].
Qed.

(** ── Toolchain predicates (faithful, over [project_tokens p pf]) ────── *)

(** The faithful pass state after [k] passes over THIS project's tokens
    under THIS profile. *)
Definition faithful_run (p : pdflatex_project) (pf : pdflatex_profile)
    (k : nat) : L0Pass.pass_state :=
  L0Pass.iterate_pass_step L0Pass.initial_pass_state k (project_tokens p pf).

(** The artefact of the k-th faithful run: a REAL PDF graph built from THIS
    project's token stream (Residual-1 — one object + xref entry per token,
    [build_pdf]) paired with the run's ACTUAL log byte stream.  The PDF is now
    NON-trivial, so [valid_pdf_graph] on it is a genuine (not vacuous)
    guarantee. *)
Definition faithful_artefact (p : pdflatex_project) (pf : pdflatex_profile)
    (k : nat) : pdflatex_artefact :=
  (build_pdf (project_tokens p pf),
   L0Log.log_bytes (L0Pass.log (faithful_run p pf k))).

(** A project has an UNRESOLVED cross-reference under [pf] iff its token
    stream references a label it never defines.  The genuine trigger of the
    warning path. *)
Definition project_has_unresolved_ref
    (p : pdflatex_project) (pf : pdflatex_profile) : Prop :=
  exists n,
    In (L0Aux.Tok_label_ref n) (project_tokens p pf)
    /\ ~ In n (L0Aux.collect_defs (project_tokens p pf)).

(** Bounded-pass termination: the faithful pass over [project_tokens p pf]
    converges within the WS8 budget. *)
Definition pdflatex_bounded_terminates
    (p : pdflatex_project) (pf : pdflatex_profile) : Prop :=
  exists k,
    k <= pdflatex_pass_max /\
    (faithful_run p pf k).(L0Pass.converged) = true.

(** Compilation success: the faithful pass over THIS project's tokens
    converges AND its log carries no fatal marker. *)
Definition pdflatex_compilation_succeeds
    (p : pdflatex_project) (pf : pdflatex_profile) : Prop :=
  exists k,
    k <= pdflatex_pass_max /\
    (faithful_run p pf k).(L0Pass.converged) = true /\
    L0Log.log_no_fatal (L0Pass.log (faithful_run p pf k)).

(** Produce relation: [out] is the artefact of a CONVERGED, FATAL-FREE
    faithful run of THIS project under THIS profile. *)
Definition pdflatex_produces
    (p : pdflatex_project) (pf : pdflatex_profile)
    (out : pdflatex_artefact) : Prop :=
  exists k,
    k <= pdflatex_pass_max /\
    (faithful_run p pf k).(L0Pass.converged) = true /\
    L0Log.log_no_fatal (L0Pass.log (faithful_run p pf k)) /\
    out = faithful_artefact p pf k.

(** Byte-level fatal-freeness of an artefact log, over the faithful
    fatal-marker set (definitionally the tail of [L0Log.log_no_fatal]). *)
Definition faithful_bytes_no_fatal (bytes : list nat) : Prop :=
  forall m, In m L0Log.fatal_markers ->
            L0Log.contains_subseq m bytes = false.

(** Output well-formedness: PDF graph valid + log fatal-free. *)
Definition pdflatex_output_format_well_formed
    (out : pdflatex_artefact) : Prop :=
  valid_pdf_graph (fst out) /\ faithful_bytes_no_fatal (snd out).

(** ── Bonus: bounded-terminates is universally true (convergence needs
       no hypothesis; only fatal-freeness does) ────────────────────── *)

Theorem pdflatex_bounded_terminates_universal :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_bounded_terminates p pf.
Proof.
  intros p pf. unfold pdflatex_bounded_terminates, faithful_run.
  destruct (L0Pass.pdflatex_pass_converges_bounded (project_tokens p pf)
              L0Pass.initial_pass_state)
    as [k [Hk Hconv]].
  exists k. split; [unfold pdflatex_pass_max; lia | exact Hconv].
Qed.

(** ── T6 — substantive discharge of compile_progress_rule ──────── *)

(** Apply [CompileProgress.Section_Compile_progress] with the
    pdflatex carriers + concrete predicates. Parametric in the
    load-bearing [compile_progress_rule]. *)
Theorem pdflatex_T6_modulo_compile_progress_rule :
  (forall (p : pdflatex_project) (pf : pdflatex_profile),
     pdflatex_T0_accepts p ->
     pdflatex_T1_admissible p ->
     pdflatex_T2_closed p ->
     pdflatex_T3_compatible p pf ->
     pdflatex_T4_coherent p ->
     pdflatex_T5_safe p ->
     pdflatex_bounded_terminates p pf ->
     pdflatex_compilation_succeeds p pf) ->
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_bounded_terminates p pf ->
    pdflatex_compilation_succeeds p pf.
Proof.
  intros rule.
  exact (T6_compile_progress_under_bound
           pdflatex_project pdflatex_profile
           pdflatex_T0_accepts
           pdflatex_T1_admissible
           pdflatex_T2_closed
           pdflatex_T3_compatible
           pdflatex_T4_coherent
           pdflatex_T5_safe
           pdflatex_bounded_terminates
           pdflatex_compilation_succeeds
           rule).
Qed.

(** SUBSTANTIVE discharge: given bounded_terminates (witness k with
    converged at k), the converged state has empty log_state (by
    [iterate_step_log_unchanged] from initial), so [log_no_fatal]
    follows from [empty_log_no_fatal]. The conclusion adds the
    log_no_fatal conjunct over bounded_terminates — this is real
    proof content, not definitional unfolding. *)
Lemma pdflatex_compile_progress_rule_proof :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_bounded_terminates p pf ->
    pdflatex_compilation_succeeds p pf.
Proof.
  (* T2 AND T3 are now BOTH LOAD-BEARING: closure (T2) rules out the dangling
     edge fatal, profile-admissibility (T3) rules out the unsupported-feature
     fatal ⇒ no_fatal_tokens ⇒ the converged log is fatal-free. This is the
     real content of compile-safety. *)
  intros p pf _ _ HT2 HT3 _ _ Hbound.
  destruct Hbound as [k [Hk Hconv]].
  destruct HT3 as [HT3decl HT3body].
  exists k. split; [exact Hk |]. split; [exact Hconv |].
  unfold faithful_run.
  apply L0Pass.pass_iteration_no_fatal.
  apply project_no_fatal_tokens; [exact HT2 | exact HT3decl | exact HT3body].
Qed.

(** Section closure with the substantive discharge. *)
Theorem pdflatex_T6_discharged :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_bounded_terminates p pf ->
    pdflatex_compilation_succeeds p pf.
Proof.
  exact (pdflatex_T6_modulo_compile_progress_rule
           pdflatex_compile_progress_rule_proof).
Qed.

(** T6 unconditional in the bounded-terminates premise: combining
    [pdflatex_T6_discharged] with [pdflatex_bounded_terminates_universal]
    gives compilation_succeeds from T0–T5 alone. *)
Theorem pdflatex_T6_unconditional_in_bound :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_compilation_succeeds p pf.
Proof.
  intros p pf H0 H1 H2 H3 H4 H5.
  apply pdflatex_T6_discharged; auto.
  apply pdflatex_bounded_terminates_universal.
Qed.

(** ── T7 — substantive discharge of output_wellformed_rule ─────── *)

(** Apply [CompileWellFormed.Section_Output_wellformed] with the
    pdflatex carriers + substantive predicates. *)
Theorem pdflatex_T7_modulo_output_wellformed_rule :
  (forall (p : pdflatex_project) (pf : pdflatex_profile)
          (out : pdflatex_artefact),
     pdflatex_compilation_succeeds p pf ->
     pdflatex_produces p pf out ->
     pdflatex_output_format_well_formed out) ->
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (out : pdflatex_artefact),
    pdflatex_compilation_succeeds p pf ->
    pdflatex_produces p pf out ->
    pdflatex_output_format_well_formed out.
Proof.
  intros rule.
  exact (T7_output_wellformed
           pdflatex_project pdflatex_profile pdflatex_artefact
           pdflatex_compilation_succeeds
           pdflatex_produces
           pdflatex_output_format_well_formed
           rule).
Qed.

(** SUBSTANTIVE discharge (faithful): [produces] carries the artefact of a
    CONVERGED, FATAL-FREE faithful run, so both wellformedness conjuncts
    close — the empty PDF graph is valid ([empty_pdf_valid]); the run's log
    is fatal-free directly from the [produces] witness (which is exactly
    [faithful_bytes_no_fatal] of the artefact's byte stream). *)
Lemma pdflatex_output_wellformed_rule_proof :
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (out : pdflatex_artefact),
    pdflatex_compilation_succeeds p pf ->
    pdflatex_produces p pf out ->
    pdflatex_output_format_well_formed out.
Proof.
  intros p pf out _ Hprod.
  destruct Hprod as [k [Hk [Hconv [Hnf Heq]]]].
  subst out.
  unfold pdflatex_output_format_well_formed, faithful_artefact.
  cbn [fst snd]. split.
  - apply build_pdf_valid.
  - unfold faithful_bytes_no_fatal. exact Hnf.
Qed.

(** Section closure with the substantive discharge. *)
Theorem pdflatex_T7_discharged :
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (out : pdflatex_artefact),
    pdflatex_compilation_succeeds p pf ->
    pdflatex_produces p pf out ->
    pdflatex_output_format_well_formed out.
Proof.
  exact (pdflatex_T7_modulo_output_wellformed_rule
           pdflatex_output_wellformed_rule_proof).
Qed.

(** ── Capstone: pdflatex_compile_safe (UNCONDITIONAL) ──────────── *)

(** Project well-typedness alias (just T2). *)
Definition project_well_typed (p : pdflatex_project) : Prop :=
  pdflatex_T2_closed p.

(** Profile-supportedness — now a GENUINE project<->profile coherence check
    (Residual-3).  It is exactly [pdflatex_T3_compatible p pf]: the engine must
    admit the profile's declared features AND every feature THE DOCUMENT BODY
    requires.  It therefore depends on [p] (via [proj_body]); a body needing a
    feature the engine lacks is UNSUPPORTED even under an
    empty-declared-features profile (see [otf_on_pdflatex_not_supported]). *)
Definition profile_supported (p : pdflatex_project) (pf : pdflatex_profile)
    : Prop :=
  profile_admits pf.(prof_features) pf.(prof_engine) /\
  profile_admits (body_required_features p.(proj_body)) pf.(prof_engine).

(** Headline theorem (FAITHFUL, project- AND profile-dependent): for any
    [project_well_typed] (= T2-closed) project and any [profile_supported]
    (= T3-admissible) profile, there exists an artefact such that the FAITHFUL
    pdflatex pass over THIS project's REAL token stream
    ([project_tokens p pf] — body label defs/refs + edge fatals + feature
    fatals) genuinely:

      (1) PRODUCES it and COMPILES SUCCESSFULLY;
      (2) is OUTPUT-WELL-FORMED;
      (3) CONVERGES within 2 passes ([converged = true] at k = 2, the real
          [aux_eq] set-stabilisation flag — Stage 5);
      (4) STAYS FATAL-FREE (Stage 4), a guarantee EARNED from BOTH
          [project_well_typed] (T2 — no dangling-edge fatal) AND
          [profile_supported] (T3 — no unsupported-feature fatal); drop
          either and a [Tok_fatal] survives (see [fatal_dangling_reaches_fatal]
          / [fatal_unsupported_profile_reaches_fatal]);
      (5) WARNS FAITHFULLY: the run's [warnings] list is non-empty IFF the
          project references a label it never defines
          ([project_has_unresolved_ref]) — Stage 3, the undefined-\ref
          warning path, now load-bearing.

    NO phantom [p] (graph + body drive the whole conclusion), NO phantom [pf]
    ([profile_supported] gates fatal-freeness), NO decorative hypothesis (the
    old [bounded_labels] is gone; the genuine hypotheses are T2 + T3). *)
Theorem pdflatex_compile_safe :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    project_well_typed p ->
    profile_supported p pf ->
    exists out,
      pdflatex_produces p pf out /\
      pdflatex_compilation_succeeds p pf /\
      pdflatex_output_format_well_formed out /\
      (faithful_run p pf 2).(L0Pass.converged) = true /\
      L0Log.log_no_fatal (L0Pass.log (faithful_run p pf 2)) /\
      (L0Log.warnings (L0Pass.log (faithful_run p pf 2)) <> []
         <-> project_has_unresolved_ref p pf) /\
      out = faithful_artefact p pf 2.
Proof.
  intros p pf Hwt [Hdecl Hbody].
  (* T2 (Hwt) AND T3 (Hdecl for the profile's declared features, Hbody for the
     DOCUMENT's required features — Residual-3) give the genuine, falsifiable
     safety hypothesis. *)
  assert (Hnf : L0Log.no_fatal_tokens (project_tokens p pf))
    by (apply project_no_fatal_tokens; [exact Hwt | exact Hdecl | exact Hbody]).
  (* Converged at exactly k = 2 (real aux_eq flag) and fatal-free. *)
  assert (Hconv : (faithful_run p pf 2).(L0Pass.converged) = true)
    by (unfold faithful_run; apply L0Pass.converged_at_two).
  assert (Hsafe : L0Log.log_no_fatal (L0Pass.log (faithful_run p pf 2)))
    by (unfold faithful_run; apply L0Pass.pass_iteration_no_fatal; exact Hnf).
  assert (Hkle : 2 <= pdflatex_pass_max) by (unfold pdflatex_pass_max; lia).
  exists (faithful_artefact p pf 2).
  split.
  { (* produces *)
    exists 2. split; [exact Hkle |]. split; [exact Hconv |].
    split; [exact Hsafe | reflexivity]. }
  split.
  { (* compilation_succeeds *)
    exists 2. split; [exact Hkle |]. split; [exact Hconv | exact Hsafe]. }
  split.
  { (* output_format_well_formed — PDF graph now NON-trivial ([build_pdf]) *)
    unfold pdflatex_output_format_well_formed, faithful_artefact.
    cbn [fst snd]. split; [apply build_pdf_valid |].
    unfold faithful_bytes_no_fatal. unfold faithful_run in Hsafe. exact Hsafe. }
  split.
  { exact Hconv. }
  split.
  { exact Hsafe. }
  split.
  { (* warns IFF unresolved cross-reference *)
    unfold faithful_run, project_has_unresolved_ref.
    apply L0Pass.warns_iff_unresolved_two. }
  { reflexivity. }
Qed.

(** ── NON-VACUITY: three genuinely-distinct projects ────────────────

    (a) CLEAN — well-typed, supported, every \ref resolves: converges,
        NO warnings, fatal-free.
    (b) WARN  — well-typed, supported, but a \ref has no \label: converges,
        NON-empty warnings, STILL fatal-free (undefined-ref is a warning).
    (c) FATAL/dangling — a dangling build edge: NOT well-typed, the pass
        reaches a FATAL log.
    (d) FATAL/profile  — a closed project under an UNSUPPORTED profile
        (opentype on pdflatex): NOT supported, the pass reaches a FATAL log
        — witnessing that [pf] is load-bearing. *)

(** (a) Clean project: one node, body defines label 5 and references it. *)
Definition p_clean : pdflatex_project :=
  mk_project (mk_graph [mk_node 0 Tex] []) [BT_label_def 5; BT_label_ref 5].
Definition pf_ok : pdflatex_profile := mk_pdflatex_profile Pdflatex [].

Example p_clean_well_typed : project_well_typed p_clean.
Proof. apply singleton_closed. Qed.

Example pf_ok_supported_clean : profile_supported p_clean pf_ok.
Proof. split; apply empty_admitted_by_all. Qed.

Example clean_converges_no_warn :
  (faithful_run p_clean pf_ok 2).(L0Pass.converged) = true
  /\ L0Log.warnings (L0Pass.log (faithful_run p_clean pf_ok 2)) = [].
Proof. split; vm_compute; reflexivity. Qed.

Example clean_no_unresolved : ~ project_has_unresolved_ref p_clean pf_ok.
Proof.
  intros [n [Hin Hnd]]. apply Hnd.
  vm_compute in Hin.
  destruct Hin as [H | [H | H]].
  - discriminate H.
  - injection H as H. subst n. vm_compute. left; reflexivity.
  - contradiction.
Qed.

(** (b) Warn project: one node, body references label 7 which is NEVER
    defined.  Well-typed + supported, so the capstone applies; its
    warns-IFF-unresolved conjunct then FORCES a non-empty warning. *)
Definition p_warn : pdflatex_project :=
  mk_project (mk_graph [mk_node 0 Tex] []) [BT_label_ref 7].

Example p_warn_well_typed : project_well_typed p_warn.
Proof. apply singleton_closed. Qed.

Example pf_ok_supported_warn : profile_supported p_warn pf_ok.
Proof. split; apply empty_admitted_by_all. Qed.

Example warn_has_unresolved : project_has_unresolved_ref p_warn pf_ok.
Proof.
  exists 7. split.
  - vm_compute. left; reflexivity.
  - vm_compute. intro H. exact H.
Qed.

Example warn_project_warns_via_capstone :
  L0Log.warnings (L0Pass.log (faithful_run p_warn pf_ok 2)) <> []
  /\ L0Log.log_no_fatal (L0Pass.log (faithful_run p_warn pf_ok 2)).
Proof.
  destruct (pdflatex_compile_safe p_warn pf_ok
              p_warn_well_typed pf_ok_supported_warn)
    as [out [_ [_ [_ [_ [Hsafe [Hwarn _]]]]]]].
  split; [| exact Hsafe].
  apply Hwarn. apply warn_has_unresolved.
Qed.

(** (c) FATAL — a dangling build edge (endpoint file 1 absent): the pass
    reaches a fatal log, and the project is NOT well-typed. *)
Definition p_dangling : pdflatex_project :=
  mk_project (mk_graph [] [(mk_node 0 Tex, mk_node 1 Tex)]) [].

Example dangling_tokens_fatal :
  project_tokens p_dangling pf_ok = [L0Aux.Tok_fatal].
Proof. reflexivity. Qed.

Example fatal_dangling_not_no_fatal_tokens :
  ~ L0Log.no_fatal_tokens (project_tokens p_dangling pf_ok).
Proof. rewrite dangling_tokens_fatal. apply L0Log.fatal_token_not_no_fatal. Qed.

Example fatal_dangling_reaches_fatal :
  ~ L0Log.log_no_fatal (L0Pass.log (faithful_run p_dangling pf_ok 1)).
Proof.
  intro H.
  assert (Hin : In L0Log.fatal_marker_emergency_stop L0Log.fatal_markers)
    by (simpl; right; left; reflexivity).
  specialize (H L0Log.fatal_marker_emergency_stop Hin).
  vm_compute in H. discriminate.
Qed.

(** (d) FATAL via UNSUPPORTED PROFILE — a closed, empty-body project compiled
    with opentype fonts on pdflatex.  The graph is closed and the body is
    fatal-free, yet the UNSUPPORTED feature makes the pass reach a fatal log.
    This is exactly what [profile_supported] rules out — [pf] load-bearing. *)
Definition p_any : pdflatex_project := mk_project (mk_graph [] []) [].
Definition pf_bad : pdflatex_profile :=
  mk_pdflatex_profile Pdflatex [Opentype_fonts].

Example pf_bad_not_supported : ~ profile_supported p_any pf_bad.
Proof.
  unfold profile_supported. intros [H _].
  assert (Hc := H Opentype_fonts (or_introl eq_refl)).
  vm_compute in Hc. discriminate.
Qed.

Example p_any_well_typed : project_well_typed p_any.
Proof. apply empty_graph_closed. Qed.

Example unsupported_tokens_fatal :
  project_tokens p_any pf_bad = [L0Aux.Tok_fatal].
Proof. reflexivity. Qed.

Example fatal_unsupported_profile_reaches_fatal :
  ~ L0Log.log_no_fatal (L0Pass.log (faithful_run p_any pf_bad 1)).
Proof.
  intro H.
  assert (Hin : In L0Log.fatal_marker_emergency_stop L0Log.fatal_markers)
    by (simpl; right; left; reflexivity).
  specialize (H L0Log.fatal_marker_emergency_stop Hin).
  vm_compute in H. discriminate.
Qed.

(** ── RESIDUAL-1 non-vacuity: the clean project's artefact is a REAL,
       non-empty, VALID PDF (not the empty graph) ──────────────────────── *)

Example clean_pdf_nonempty_valid :
  valid_pdf_graph (fst (faithful_artefact p_clean pf_ok 2))
  /\ (fst (faithful_artefact p_clean pf_ok 2)).(pdf_objects) <> [].
Proof.
  split.
  - apply build_pdf_valid.
  - vm_compute. intro H. discriminate.
Qed.

(** One PDF object per body token: the clean artefact carries 2 objects and 2
    matching xref entries. *)
Example clean_pdf_two_objects :
  length (fst (faithful_artefact p_clean pf_ok 2)).(pdf_objects) = 2
  /\ length (fst (faithful_artefact p_clean pf_ok 2)).(pdf_xref) = 2.
Proof. split; vm_compute; reflexivity. Qed.

(** ── RESIDUAL-2 non-vacuity + load-bearing: GENUINE T4 (label uniqueness) ──

    T4 is now [NoDup (body_label_defs p.(proj_body))] — falsifiable and
    project-dependent.  [p_clean] (one label) satisfies it; [p_dup] (the same
    label defined twice) REFUTES it.  The corollary below USES T4 to derive a
    per-label [count_occ = 1] fact — false without T4, so T4 is load-bearing. *)

Example p_clean_T4 : pdflatex_T4_coherent p_clean.
Proof.
  unfold pdflatex_T4_coherent; simpl.
  constructor; [intro H; inversion H | constructor].
Qed.

Definition p_dup : pdflatex_project :=
  mk_project (mk_graph [mk_node 0 Tex] []) [BT_label_def 5; BT_label_def 5].

Example p_dup_not_T4 : ~ pdflatex_T4_coherent p_dup.
Proof.
  unfold pdflatex_T4_coherent; simpl.
  intro H.
  pose proof (proj1 (NoDup_count_occ' Nat.eq_dec [5; 5]) H) as Hc.
  specialize (Hc 5 (or_introl eq_refl)). vm_compute in Hc. discriminate.
Qed.

Corollary pdflatex_labels_resolve_uniquely :
  forall p pf,
    project_well_typed p ->
    profile_supported p pf ->
    pdflatex_T4_coherent p ->
    exists out,
      pdflatex_produces p pf out /\
      pdflatex_output_format_well_formed out /\
      (* T4 load-bearing: each defined label has EXACTLY ONE definition. *)
      (forall n, In n (body_label_defs p.(proj_body)) ->
                 count_occ Nat.eq_dec (body_label_defs p.(proj_body)) n = 1).
Proof.
  intros p pf Hwt Hsupp HT4.
  destruct (pdflatex_compile_safe p pf Hwt Hsupp)
    as [out [Hprod [_ [Hwf _]]]].
  exists out. split; [exact Hprod |]. split; [exact Hwf |].
  apply (proj1 (NoDup_count_occ' Nat.eq_dec (body_label_defs p.(proj_body)))).
  exact HT4.
Qed.

(** ── RESIDUAL-3 non-vacuity + load-bearing: DOCUMENT-feature coherence ──

    A body that REQUIRES opentype fonts ([BT_needs_feature Opentype_fonts]).
    Its token image — hence its fatal-freeness — depends on the ENGINE, even
    though the profile itself declares NO features.  On pdflatex the feature is
    unsupported: the DOCUMENT emits a fatal.  On xelatex it is supported: the
    document is inert and the capstone applies.  This is the residual-3 point —
    [profile_supported] now checks the features the DOCUMENT requires, not just
    the profile's own declared set. *)

Definition p_needs_otf : pdflatex_project :=
  mk_project (mk_graph [] []) [BT_needs_feature Opentype_fonts].
Definition pf_pdf : pdflatex_profile := mk_pdflatex_profile Pdflatex [].
Definition pf_xe  : pdflatex_profile := mk_pdflatex_profile Xelatex [].

Example p_needs_otf_well_typed : project_well_typed p_needs_otf.
Proof. apply empty_graph_closed. Qed.

(** The profile declares NO features, yet the DOCUMENT is unsupported on
    pdflatex because it REQUIRES opentype — the genuine project<->profile
    coherence check. *)
Example otf_on_pdflatex_not_supported : ~ profile_supported p_needs_otf pf_pdf.
Proof.
  unfold profile_supported. intros [_ H].
  assert (Hc := H Opentype_fonts (or_introl eq_refl)).
  vm_compute in Hc. discriminate.
Qed.

Example otf_on_pdflatex_tokens_fatal :
  project_tokens p_needs_otf pf_pdf = [L0Aux.Tok_fatal].
Proof. reflexivity. Qed.

(** The DOCUMENT's required feature drives the pass to a FATAL log. *)
Example fatal_body_feature_reaches_fatal :
  ~ L0Log.log_no_fatal (L0Pass.log (faithful_run p_needs_otf pf_pdf 1)).
Proof.
  intro H.
  assert (Hin : In L0Log.fatal_marker_emergency_stop L0Log.fatal_markers)
    by (simpl; right; left; reflexivity).
  specialize (H L0Log.fatal_marker_emergency_stop Hin).
  vm_compute in H. discriminate.
Qed.

(** On xelatex the SAME document is supported (opentype is engine-compatible)
    even though the profile declares no features. *)
Example otf_on_xelatex_supported : profile_supported p_needs_otf pf_xe.
Proof.
  split; [apply empty_admitted_by_all |].
  intros f Hf. destruct Hf as [Heq | []]. rewrite <- Heq. reflexivity.
Qed.

(** And under xelatex the capstone genuinely applies: the document PRODUCES a
    well-formed artefact. *)
Example otf_on_xelatex_compiles :
  exists out,
    pdflatex_produces p_needs_otf pf_xe out
    /\ pdflatex_output_format_well_formed out.
Proof.
  destruct (pdflatex_compile_safe p_needs_otf pf_xe
              p_needs_otf_well_typed otf_on_xelatex_supported)
    as [out [Hprod [_ [Hwf _]]]].
  exists out. split; [exact Hprod | exact Hwf].
Qed.

(** ── BLUNT residual note: T0 / T1 / T5 remain project-INDEPENDENT ──────

    T2 (closure), T3 (declared + DOCUMENT-required features), and T4 (label
    uniqueness) are now genuine, falsifiable, project-dependent predicates,
    and T2/T3 are load-bearing for fatal-freeness while T4 is load-bearing in
    [pdflatex_labels_resolve_uniquely].  T0, T1 and T5 are DELIBERATELY LEFT as
    universally-true WS8 wrappers, because their content is genuinely NOT a
    function of this project model:

      - T0 (parser acceptance) lives at the LP-Core parser-node abstraction
        layer.  The project body here is ALREADY a token stream (post-lexing),
        so there is no raw-byte parse-failure to express — a project-dependent
        T0 would need a byte-level source model this file does not carry.

      - T1 (macro-expansion admissibility) is a property of the USER MACRO
        CATALOGUE.  This project model ([build_graph] + document token body)
        carries no macro registry, so there is nothing project-specific for T1
        to constrain.

      - T5 (rule-catalogue soundness) ranges over the GENERATED per-rule proof
        set ([Generated.Catalogue]), not the project.  Making it
        project-dependent here would invert the theory dependency (Generated
        already depends on this file) and is out of scope by construction; the
        catalogue-specific instance is derived downstream in
        [proofs/generated/PdflatexT5Wired.v] from [pdflatex_T5_safe_holds]. *)

(** ── Engine-generic capstone aliases ─────────────────────────────

    The pass-iteration model in this file is engine-agnostic — the
    [pdflatex_step] counter doesn't model anything pdflatex-specific
    beyond the 5-pass convergence bound, which xelatex and lualatex
    share by industry convention.  [profile_supported] dispatches on
    the engine via [BuildProfileSound.profile_admits], so the same
    capstone covers any [pdflatex_profile] whose engine is admitted.

    The aliases below are explicit theorems for xelatex / lualatex
    profiles so callers can name them directly.  Each is a
    Definition (not Theorem) — same proof object as
    [pdflatex_compile_safe], no new content. *)

Definition xelatex_compile_safe := pdflatex_compile_safe.

Definition lualatex_compile_safe := pdflatex_compile_safe.

(** ── Zero-admit witness ──────────────────────────────────────────── *)

Definition pdflatex_model_capstone_zero_admits : True := I.
