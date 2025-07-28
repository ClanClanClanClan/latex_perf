From Coq Require Import String List.
Require Import LatexLexer ExpanderTypes.
Open Scope string_scope.

(** * LaTeX Perfectionist v24 - Built-in Macro Catalog
    
    Complete catalog of 76 built-in macros as specified in LAYER_L1_SPECIFICATION.md.
    These are the exact macros the L1 Expander must handle.
    
    Status: 0 axioms, 0 admits required
*)

(** ** Typography Macros (12) *)
Definition latex_macro : macro_definition := {|
  macro_name := "LaTeX";
  macro_body := TText "LaTeX" :: nil;
  is_builtin := true
|}.

Definition tex_macro : macro_definition := {|
  macro_name := "TeX";  
  macro_body := TText "TeX" :: nil;
  is_builtin := true
|}.

Definition ldots_macro : macro_definition := {|
  macro_name := "ldots";
  macro_body := TText "…" :: nil;
  is_builtin := true
|}.

Definition textit_macro : macro_definition := {|
  macro_name := "textit";
  macro_body := TText "⟨italic⟩" :: nil; (* placeholder for italic representation *)
  is_builtin := true
|}.

Definition textbf_macro : macro_definition := {|
  macro_name := "textbf";
  macro_body := TText "⟨bold⟩" :: nil;
  is_builtin := true
|}.

Definition emph_macro : macro_definition := {|
  macro_name := "emph";
  macro_body := TText "⟨emphasis⟩" :: nil;
  is_builtin := true
|}.

Definition underline_macro : macro_definition := {|
  macro_name := "underline";
  macro_body := TText "⟨underline⟩" :: nil;
  is_builtin := true
|}.

Definition texttt_macro : macro_definition := {|
  macro_name := "texttt";
  macro_body := TText "⟨typewriter⟩" :: nil;
  is_builtin := true
|}.

Definition textsf_macro : macro_definition := {|
  macro_name := "textsf";
  macro_body := TText "⟨sans-serif⟩" :: nil;
  is_builtin := true
|}.

Definition textsc_macro : macro_definition := {|
  macro_name := "textsc";
  macro_body := TText "⟨small-caps⟩" :: nil;
  is_builtin := true
|}.

Definition today_macro : macro_definition := {|
  macro_name := "today";
  macro_body := TText "2025-07-21" :: nil; (* current date representation *)
  is_builtin := true
|}.

Definition copyright_macro : macro_definition := {|
  macro_name := "copyright";
  macro_body := TText "©" :: nil;
  is_builtin := true
|}.

(** ** Mathematical Macros (32) *)
(* Greek lowercase *)
Definition alpha_macro : macro_definition := {|
  macro_name := "alpha";
  macro_body := TText "α" :: nil;
  is_builtin := true
|}.

Definition beta_macro : macro_definition := {|
  macro_name := "beta";
  macro_body := TText "β" :: nil;
  is_builtin := true
|}.

Definition gamma_macro : macro_definition := {|
  macro_name := "gamma";
  macro_body := TText "γ" :: nil;
  is_builtin := true
|}.

Definition delta_macro : macro_definition := {|
  macro_name := "delta";
  macro_body := TText "δ" :: nil;
  is_builtin := true
|}.

Definition epsilon_macro : macro_definition := {|
  macro_name := "epsilon";
  macro_body := TText "ε" :: nil;
  is_builtin := true
|}.

Definition zeta_macro : macro_definition := {|
  macro_name := "zeta";
  macro_body := TText "ζ" :: nil;
  is_builtin := true
|}.

Definition eta_macro : macro_definition := {|
  macro_name := "eta";
  macro_body := TText "η" :: nil;
  is_builtin := true
|}.

Definition theta_macro : macro_definition := {|
  macro_name := "theta";
  macro_body := TText "θ" :: nil;
  is_builtin := true
|}.

Definition iota_macro : macro_definition := {|
  macro_name := "iota";
  macro_body := TText "ι" :: nil;
  is_builtin := true
|}.

Definition kappa_macro : macro_definition := {|
  macro_name := "kappa";
  macro_body := TText "κ" :: nil;
  is_builtin := true
|}.

Definition lambda_macro : macro_definition := {|
  macro_name := "lambda";
  macro_body := TText "λ" :: nil;
  is_builtin := true
|}.

Definition mu_macro : macro_definition := {|
  macro_name := "mu";
  macro_body := TText "μ" :: nil;
  is_builtin := true
|}.

Definition nu_macro : macro_definition := {|
  macro_name := "nu";
  macro_body := TText "ν" :: nil;
  is_builtin := true
|}.

Definition xi_macro : macro_definition := {|
  macro_name := "xi";
  macro_body := TText "ξ" :: nil;
  is_builtin := true
|}.

Definition pi_macro : macro_definition := {|
  macro_name := "pi";
  macro_body := TText "π" :: nil;
  is_builtin := true
|}.

Definition rho_macro : macro_definition := {|
  macro_name := "rho";
  macro_body := TText "ρ" :: nil;
  is_builtin := true
|}.

Definition sigma_macro : macro_definition := {|
  macro_name := "sigma";
  macro_body := TText "σ" :: nil;
  is_builtin := true
|}.

Definition tau_macro : macro_definition := {|
  macro_name := "tau";
  macro_body := TText "τ" :: nil;
  is_builtin := true
|}.

Definition upsilon_macro : macro_definition := {|
  macro_name := "upsilon";
  macro_body := TText "υ" :: nil;
  is_builtin := true
|}.

Definition phi_macro : macro_definition := {|
  macro_name := "phi";
  macro_body := TText "φ" :: nil;
  is_builtin := true
|}.

Definition chi_macro : macro_definition := {|
  macro_name := "chi";
  macro_body := TText "χ" :: nil;
  is_builtin := true
|}.

Definition psi_macro : macro_definition := {|
  macro_name := "psi";
  macro_body := TText "ψ" :: nil;
  is_builtin := true
|}.

Definition omega_macro : macro_definition := {|
  macro_name := "omega";
  macro_body := TText "ω" :: nil;
  is_builtin := true
|}.

(* Greek uppercase *)
Definition Gamma_macro : macro_definition := {|
  macro_name := "Gamma";
  macro_body := TText "Γ" :: nil;
  is_builtin := true
|}.

Definition Delta_macro : macro_definition := {|
  macro_name := "Delta";
  macro_body := TText "Δ" :: nil;
  is_builtin := true
|}.

Definition Theta_macro : macro_definition := {|
  macro_name := "Theta";
  macro_body := TText "Θ" :: nil;
  is_builtin := true
|}.

Definition Lambda_macro : macro_definition := {|
  macro_name := "Lambda";
  macro_body := TText "Λ" :: nil;
  is_builtin := true
|}.

Definition Xi_macro : macro_definition := {|
  macro_name := "Xi";
  macro_body := TText "Ξ" :: nil;
  is_builtin := true
|}.

Definition Pi_macro : macro_definition := {|
  macro_name := "Pi";
  macro_body := TText "Π" :: nil;
  is_builtin := true
|}.

Definition Sigma_macro : macro_definition := {|
  macro_name := "Sigma";
  macro_body := TText "Σ" :: nil;
  is_builtin := true
|}.

Definition Upsilon_macro : macro_definition := {|
  macro_name := "Upsilon";
  macro_body := TText "Υ" :: nil;
  is_builtin := true
|}.

Definition Phi_macro : macro_definition := {|
  macro_name := "Phi";
  macro_body := TText "Φ" :: nil;
  is_builtin := true
|}.

Definition Psi_macro : macro_definition := {|
  macro_name := "Psi";
  macro_body := TText "Ψ" :: nil;
  is_builtin := true
|}.

Definition Omega_macro : macro_definition := {|
  macro_name := "Omega";
  macro_body := TText "Ω" :: nil;
  is_builtin := true
|}.

(* Mathematical operators *)
Definition infty_macro : macro_definition := {|
  macro_name := "infty";
  macro_body := TText "∞" :: nil;
  is_builtin := true
|}.

Definition pm_macro : macro_definition := {|
  macro_name := "pm";
  macro_body := TText "±" :: nil;
  is_builtin := true
|}.

Definition mp_macro : macro_definition := {|
  macro_name := "mp";
  macro_body := TText "∓" :: nil;
  is_builtin := true
|}.

Definition times_macro : macro_definition := {|
  macro_name := "times";
  macro_body := TText "×" :: nil;
  is_builtin := true
|}.

Definition div_macro : macro_definition := {|
  macro_name := "div";
  macro_body := TText "÷" :: nil;
  is_builtin := true
|}.

Definition neq_macro : macro_definition := {|
  macro_name := "neq";
  macro_body := TText "≠" :: nil;
  is_builtin := true
|}.

Definition leq_macro : macro_definition := {|
  macro_name := "leq";
  macro_body := TText "≤" :: nil;
  is_builtin := true
|}.

Definition geq_macro : macro_definition := {|
  macro_name := "geq";
  macro_body := TText "≥" :: nil;
  is_builtin := true
|}.

Definition approx_macro : macro_definition := {|
  macro_name := "approx";
  macro_body := TText "≈" :: nil;
  is_builtin := true
|}.

Definition equiv_macro : macro_definition := {|
  macro_name := "equiv";
  macro_body := TText "≡" :: nil;
  is_builtin := true
|}.

Definition propto_macro : macro_definition := {|
  macro_name := "propto";
  macro_body := TText "∝" :: nil;
  is_builtin := true
|}.

(** ** Structural Macros (20) - Simplified for LaTeX ε *)
Definition section_macro : macro_definition := {|
  macro_name := "section";
  macro_body := TText "⟨section⟩" :: nil;
  is_builtin := true
|}.

Definition subsection_macro : macro_definition := {|
  macro_name := "subsection";
  macro_body := TText "⟨subsection⟩" :: nil;
  is_builtin := true
|}.

Definition subsubsection_macro : macro_definition := {|
  macro_name := "subsubsection";
  macro_body := TText "⟨subsubsection⟩" :: nil;
  is_builtin := true
|}.

Definition paragraph_macro : macro_definition := {|
  macro_name := "paragraph";
  macro_body := TText "⟨paragraph⟩" :: nil;
  is_builtin := true
|}.

Definition subparagraph_macro : macro_definition := {|
  macro_name := "subparagraph";
  macro_body := TText "⟨subparagraph⟩" :: nil;
  is_builtin := true
|}.

Definition item_macro : macro_definition := {|
  macro_name := "item";
  macro_body := TText "• " :: nil;
  is_builtin := true
|}.

Definition label_macro : macro_definition := {|
  macro_name := "label";
  macro_body := TText "⟨label⟩" :: nil;
  is_builtin := true
|}.

Definition ref_macro : macro_definition := {|
  macro_name := "ref";
  macro_body := TText "⟨ref⟩" :: nil;
  is_builtin := true
|}.

Definition cite_macro : macro_definition := {|
  macro_name := "cite";
  macro_body := TText "⟨cite⟩" :: nil;
  is_builtin := true
|}.

Definition footnote_macro : macro_definition := {|
  macro_name := "footnote";
  macro_body := TText "⟨footnote⟩" :: nil;
  is_builtin := true
|}.

Definition newpage_macro : macro_definition := {|
  macro_name := "newpage";
  macro_body := TText "⟨newpage⟩" :: nil;
  is_builtin := true
|}.

Definition clearpage_macro : macro_definition := {|
  macro_name := "clearpage";
  macro_body := TText "⟨clearpage⟩" :: nil;
  is_builtin := true
|}.

Definition tableofcontents_macro : macro_definition := {|
  macro_name := "tableofcontents";
  macro_body := TText "⟨TOC⟩" :: nil;
  is_builtin := true
|}.

Definition listoffigures_macro : macro_definition := {|
  macro_name := "listoffigures";
  macro_body := TText "⟨LOF⟩" :: nil;
  is_builtin := true
|}.

Definition listoftables_macro : macro_definition := {|
  macro_name := "listoftables";
  macro_body := TText "⟨LOT⟩" :: nil;
  is_builtin := true
|}.

Definition bibliography_macro : macro_definition := {|
  macro_name := "bibliography";
  macro_body := TText "⟨bibliography⟩" :: nil;
  is_builtin := true
|}.

Definition index_macro : macro_definition := {|
  macro_name := "index";
  macro_body := TText "⟨index⟩" :: nil;
  is_builtin := true
|}.

Definition maketitle_macro : macro_definition := {|
  macro_name := "maketitle";
  macro_body := TText "⟨title⟩" :: nil;
  is_builtin := true
|}.

Definition abstract_macro : macro_definition := {|
  macro_name := "abstract";
  macro_body := TText "⟨abstract⟩" :: nil;
  is_builtin := true
|}.

Definition appendix_macro : macro_definition := {|
  macro_name := "appendix";
  macro_body := TText "⟨appendix⟩" :: nil;
  is_builtin := true
|}.

(** ** Formatting Macros (12) *)
Definition centering_macro : macro_definition := {|
  macro_name := "centering";
  macro_body := TText "⟨center⟩" :: nil;
  is_builtin := true
|}.

Definition raggedright_macro : macro_definition := {|
  macro_name := "raggedright";
  macro_body := TText "⟨left-align⟩" :: nil;
  is_builtin := true
|}.

Definition raggedleft_macro : macro_definition := {|
  macro_name := "raggedleft";
  macro_body := TText "⟨right-align⟩" :: nil;
  is_builtin := true
|}.

Definition small_macro : macro_definition := {|
  macro_name := "small";
  macro_body := TText "⟨small⟩" :: nil;
  is_builtin := true
|}.

Definition large_macro : macro_definition := {|
  macro_name := "large";
  macro_body := TText "⟨large⟩" :: nil;
  is_builtin := true
|}.

Definition Large_macro : macro_definition := {|
  macro_name := "Large";
  macro_body := TText "⟨Large⟩" :: nil;
  is_builtin := true
|}.

Definition LARGE_macro : macro_definition := {|
  macro_name := "LARGE";
  macro_body := TText "⟨LARGE⟩" :: nil;
  is_builtin := true
|}.

Definition tiny_macro : macro_definition := {|
  macro_name := "tiny";
  macro_body := TText "⟨tiny⟩" :: nil;
  is_builtin := true
|}.

Definition scriptsize_macro : macro_definition := {|
  macro_name := "scriptsize";
  macro_body := TText "⟨scriptsize⟩" :: nil;
  is_builtin := true
|}.

Definition footnotesize_macro : macro_definition := {|
  macro_name := "footnotesize";
  macro_body := TText "⟨footnotesize⟩" :: nil;
  is_builtin := true
|}.

Definition normalsize_macro : macro_definition := {|
  macro_name := "normalsize";
  macro_body := TText "⟨normalsize⟩" :: nil;
  is_builtin := true
|}.

Definition huge_macro : macro_definition := {|
  macro_name := "huge";
  macro_body := TText "⟨huge⟩" :: nil;
  is_builtin := true
|}.

(** ** Complete Catalog (76 macros total) *)
Definition builtin_macros : list macro_definition :=
  (* Typography (12) *)
  latex_macro :: tex_macro :: ldots_macro :: textit_macro :: textbf_macro :: emph_macro ::
  underline_macro :: texttt_macro :: textsf_macro :: textsc_macro :: today_macro :: copyright_macro ::
  
  (* Mathematical (32) *)
  alpha_macro :: beta_macro :: gamma_macro :: delta_macro :: epsilon_macro :: zeta_macro ::
  eta_macro :: theta_macro :: iota_macro :: kappa_macro :: lambda_macro :: mu_macro ::
  nu_macro :: xi_macro :: pi_macro :: rho_macro :: sigma_macro :: tau_macro ::
  upsilon_macro :: phi_macro :: chi_macro :: psi_macro :: omega_macro ::
  Gamma_macro :: Delta_macro :: Theta_macro :: Lambda_macro :: Xi_macro :: Pi_macro ::
  Sigma_macro :: Upsilon_macro :: Phi_macro :: Psi_macro :: Omega_macro ::
  infty_macro :: pm_macro :: mp_macro :: times_macro :: div_macro :: neq_macro ::
  leq_macro :: geq_macro :: approx_macro :: equiv_macro :: propto_macro ::
  
  (* Structural (20) *)
  section_macro :: subsection_macro :: subsubsection_macro :: paragraph_macro :: subparagraph_macro ::
  item_macro :: label_macro :: ref_macro :: cite_macro :: footnote_macro ::
  newpage_macro :: clearpage_macro :: tableofcontents_macro :: listoffigures_macro :: listoftables_macro ::
  bibliography_macro :: index_macro :: maketitle_macro :: abstract_macro :: appendix_macro ::
  
  (* Formatting (12) *)
  centering_macro :: raggedright_macro :: raggedleft_macro :: small_macro :: large_macro :: Large_macro ::
  LARGE_macro :: tiny_macro :: scriptsize_macro :: footnotesize_macro :: normalsize_macro :: huge_macro ::
  nil.

(** ** Lookup Function *)
Fixpoint lookup_builtin_aux (macros : list macro_definition) (name : string) : option (list latex_token) :=
  match macros with
  | nil => None
  | m :: rest => 
      if String.eqb name m.(macro_name) then
        Some m.(macro_body)
      else
        lookup_builtin_aux rest name
  end.

Definition lookup_builtin (name : string) : option (list latex_token) :=
  lookup_builtin_aux builtin_macros name.

(* ================================== *)
(* ===  Proof that built‑ins are   ===*)
(* ===  one‑token, no‑TEOF bodies  ===*)
(* ================================== *)

(* Helper to check if a token is TText *)
Definition is_ttext (t : latex_token) : bool :=
  match t with
  | TText _ => true
  | _ => false
  end.

(* Check that a macro body has form TText s :: nil *)
Definition check_macro_body (m : macro_definition) : bool :=
  match macro_body m with
  | TText _ :: nil => true
  | _ => false
  end.

(* Computational check that all builtins are safe *)
Lemma all_builtin_bodies_safe_compute : 
  forallb check_macro_body builtin_macros = true.
Proof.
  reflexivity.
Qed.

Lemma all_builtin_bodies_safe :
  forall m,
    In m builtin_macros ->
    exists s, macro_body m = TText s :: nil.
Proof.
  intros m Hin.
  (* Since all 76 macros follow the pattern, we can prove this systematically *)
  pose proof all_builtin_bodies_safe_compute as Hcomp.
  rewrite forallb_forall in Hcomp.
  specialize (Hcomp m Hin).
  unfold check_macro_body in Hcomp.
  (* Destruct macro_body m and analyze *)
  destruct (macro_body m) as [|t ts] eqn:Hmb.
  - (* nil case - impossible by Hcomp *)
    simpl in Hcomp. discriminate.
  - (* cons case *)
    destruct ts as [|t' ts'].
    + (* single element: t :: nil *)
      destruct t eqn:Ht.
      all: try (simpl in Hcomp; discriminate).
      (* TText case *)
      * exists s.
        (* We need to prove: macro_body m = TText s :: nil *)
        (* We have: Hmb: macro_body m = t :: nil *)
        (* We have: Ht: t = TText s *)
        subst t.
        reflexivity.
    + (* multiple elements - impossible by Hcomp *)
      simpl in Hcomp. 
      destruct t; discriminate.
Qed.

Corollary lookup_builtin_no_teof :
  forall name body,
    lookup_builtin name = Some body ->
    ~ In TEOF body.
Proof.
  intros name body Hlk.
  unfold lookup_builtin in Hlk.
  (* Need to handle the lookup_builtin_aux structure *)
  unfold lookup_builtin_aux in Hlk.
  
  (* Since lookup scans through builtin_macros, we need to relate back to it *)
  assert (forall macros name body,
    lookup_builtin_aux macros name = Some body ->
    (forall m, In m macros -> exists s, macro_body m = TText s :: nil) ->
    ~ In TEOF body) as Haux.
  {
    intro macros.
    induction macros as [|m rest IHmacros].
    - intros. simpl in H. discriminate.
    - intros name' body' Hlookup Hall.
      simpl in Hlookup.
      destruct (String.eqb name' (macro_name m)) eqn:Heq.
      + injection Hlookup as Heq_body.
        subst body'.
        assert (In m (m :: rest)) by (simpl; left; reflexivity).
        apply Hall in H as [s Hmacro].
        rewrite Hmacro.
        intros [Hbad|[]].
        (* TText s cannot equal TEOF - different constructors *)
        discriminate Hbad.
      + apply IHmacros with name'.
        * exact Hlookup.
        * intros m' Hin. apply Hall. simpl. right. exact Hin.
  }
  
  apply Haux with builtin_macros name.
  - exact Hlk.
  - apply all_builtin_bodies_safe.
Qed.

Corollary lookup_builtin_no_command :
  forall name body,
    lookup_builtin name = Some body ->
    forall c, ~ In (TCommand c) body.
Proof.
  intros name body Hlk c.
  unfold lookup_builtin in Hlk.
  unfold lookup_builtin_aux in Hlk.
  
  (* Same structure as lookup_builtin_no_teof proof *)
  assert (forall macros name body,
    lookup_builtin_aux macros name = Some body ->
    (forall m, In m macros -> exists s, macro_body m = TText s :: nil) ->
    forall c, ~ In (TCommand c) body) as Haux.
  {
    intro macros.
    induction macros as [|m rest IHmacros].
    - intros. simpl in H. discriminate.
    - intros name' body' Hlookup Hall c'.
      simpl in Hlookup.
      destruct (String.eqb name' (macro_name m)) eqn:Heq.
      + injection Hlookup as Heq_body.
        subst body'.
        assert (In m (m :: rest)) by (simpl; left; reflexivity).
        apply Hall in H as [s Hmacro].
        rewrite Hmacro.
        intros [Hbad|[]].
        (* TText s cannot equal TCommand c' - different constructors *)
        discriminate Hbad.
      + apply IHmacros with name'.
        * exact Hlookup.
        * intros m' Hin. apply Hall. simpl. right. exact Hin.
  }
  
  apply Haux with builtin_macros name.
  - exact Hlk.
  - apply all_builtin_bodies_safe.
Qed.