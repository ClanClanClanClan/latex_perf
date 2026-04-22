(** * BuildProfileSound — T3 profile/feature compatibility (memo §5.5).

    Models [Compile_contract.feature_compatible] in the OCaml runtime.
    Each build profile (engine) admits a specific set of declared
    features; T3 says: if every declared feature is compatible with the
    selected profile, then the profile admits the project.

    The compatibility table here mirrors the decision logic in
    [compile_contract.ml]. Every clause of the OCaml match is reflected
    in a clause of [compatible] here, so the Coq table is an
    executable specification the OCaml runtime can be audited against.

    Zero admits, zero axioms. *)

From Coq Require Import List Bool Arith.
Import ListNotations.

(** ── Engines ─────────────────────────────────────────────────────── *)

Inductive engine : Type :=
  | Pdflatex
  | Xelatex
  | Lualatex
  | Ptex_uptex.

Definition engine_eqb (a b : engine) : bool :=
  match a, b with
  | Pdflatex, Pdflatex | Xelatex, Xelatex
  | Lualatex, Lualatex | Ptex_uptex, Ptex_uptex => true
  | _, _ => false
  end.

(** ── Declared features ───────────────────────────────────────────── *)

(** Matches the OCaml [Project_model.declared_feature] sum. Adding a
    constructor here requires updating the [compatible] table below —
    the [completeness] theorem at the end checks that every engine is
    compatible with at least one feature, ensuring the table isn't
    vacuously false. *)
Inductive feature : Type :=
  | UTF8_inputenc
  | UTF8_direct
  | Unicode_math
  | Opentype_fonts
  | Lua_scripting
  | Japanese_cjk
  | Bibtex
  | Biber.

(** ── Compatibility table (mirrors compile_contract.ml) ─────────────── *)

Definition compatible (f : feature) (e : engine) : bool :=
  match f, e with
  | UTF8_inputenc, Ptex_uptex => false
  | UTF8_inputenc, _ => true
  | UTF8_direct, Xelatex => true
  | UTF8_direct, Lualatex => true
  | UTF8_direct, _ => false
  | Unicode_math, Xelatex => true
  | Unicode_math, Lualatex => true
  | Unicode_math, _ => false
  | Opentype_fonts, Xelatex => true
  | Opentype_fonts, Lualatex => true
  | Opentype_fonts, _ => false
  | Lua_scripting, Lualatex => true
  | Lua_scripting, _ => false
  | Japanese_cjk, Ptex_uptex => true
  | Japanese_cjk, _ => false
  | Bibtex, _ => true
  | Biber, _ => true
  end.

Fixpoint all_features_compatible (fs : list feature) (e : engine) : bool :=
  match fs with
  | [] => true
  | f :: rest => andb (compatible f e) (all_features_compatible rest e)
  end.

(** ── Profile admissibility (T3 claim) ─────────────────────────────── *)

Definition profile_admits (fs : list feature) (e : engine) : Prop :=
  forall f, In f fs -> compatible f e = true.

(** ── Theorem 1: T3 — table compatibility ⇒ profile admits ─────────── *)

Theorem T3_profile_compatible :
  forall fs e,
    all_features_compatible fs e = true ->
    profile_admits fs e.
Proof.
  intros fs e. induction fs as [|f rest IH]; simpl.
  - intros _ f Hin. inversion Hin.
  - intros Hall f0 Hin. apply andb_prop in Hall. destruct Hall as [Hf Hrest].
    destruct Hin as [Heq | Hin'].
    + subst. exact Hf.
    + apply IH; assumption.
Qed.

(** ── Theorem 2: converse — pointwise ⇒ table bulk ─────────────────── *)

Theorem profile_admits_implies_bulk :
  forall fs e,
    profile_admits fs e ->
    all_features_compatible fs e = true.
Proof.
  intros fs e Hpw. induction fs as [|f rest IH]; simpl; auto.
  rewrite (Hpw f (or_introl eq_refl)).
  simpl. apply IH. intros f' Hin. apply Hpw. right. exact Hin.
Qed.

(** ── Theorem 3: decidability ─────────────────────────────────────── *)

Theorem profile_admits_dec :
  forall fs e, {profile_admits fs e} + {~ profile_admits fs e}.
Proof.
  intros fs e.
  destruct (all_features_compatible fs e) eqn:Hall.
  - left. apply T3_profile_compatible. exact Hall.
  - right. intros Hpw.
    assert (Hbulk := profile_admits_implies_bulk fs e Hpw).
    rewrite Hall in Hbulk. discriminate.
Qed.

(** ── Theorem 4: empty feature list is admitted by every engine ───── *)

Theorem empty_admitted_by_all :
  forall e, profile_admits [] e.
Proof.
  intros e f Hin. inversion Hin.
Qed.

(** ── Theorem 5: monotonicity — sublist admitted if superlist is ──── *)

Theorem admits_monotone_sublist :
  forall fs1 fs2 e,
    (forall f, In f fs1 -> In f fs2) ->
    profile_admits fs2 e ->
    profile_admits fs1 e.
Proof.
  intros fs1 fs2 e Hsub Hadm f Hin. apply Hadm. apply Hsub. exact Hin.
Qed.

(** ── Theorem 6: known-incompatible witnesses from the memo ────────── *)

Theorem opentype_rejected_on_pdflatex :
  compatible Opentype_fonts Pdflatex = false.
Proof. reflexivity. Qed.

Theorem lua_scripting_rejected_off_lualatex :
  forall e,
    e <> Lualatex ->
    compatible Lua_scripting e = false.
Proof.
  intros e Hne. destruct e; simpl; try reflexivity. exfalso. apply Hne. reflexivity.
Qed.

Theorem japanese_cjk_requires_ptex :
  forall e,
    e <> Ptex_uptex ->
    compatible Japanese_cjk e = false.
Proof.
  intros e Hne. destruct e; simpl; try reflexivity. exfalso. apply Hne. reflexivity.
Qed.

(** ── Theorem 7: completeness — every engine supports at least one
       feature (Bibtex/Biber are engine-agnostic) ───────────────────── *)

Theorem every_engine_has_compatible_feature :
  forall e, exists f, compatible f e = true.
Proof.
  intros e. exists Bibtex. destruct e; reflexivity.
Qed.

(** ── Decidability ────────────────────────────────────────────────── *)

Theorem engine_eq_dec :
  forall (a b : engine), {a = b} + {a <> b}.
Proof.
  intros a b. destruct a, b;
    try (left; reflexivity); right; discriminate.
Qed.

Theorem feature_eq_dec :
  forall (a b : feature), {a = b} + {a <> b}.
Proof.
  intros a b. destruct a, b;
    try (left; reflexivity); right; discriminate.
Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition build_profile_sound_zero_admits : True := I.
