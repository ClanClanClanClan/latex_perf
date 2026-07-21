(** Compile-guarantee evidence extractor + OCaml mirror of the Coq capstone
    premise-checker.

    This module bridges a REAL .tex document to the abstract
    [PdflatexModel.pdflatex_project] / [pdflatex_profile] structures that the
    Coq theorem [PdflatexModel.pdflatex_compile_safe] governs, and EXECUTES the
    Coq-EXTRACTED decidable checker [CompileGuaranteeBridge.project_wf_dec]
    (module [Compile_guarantee_extracted], generated from
    proofs/CompileGuaranteeExtract.v) whose soundness (Qed, 0 admits,
    [Print Assumptions] Closed) proves a [true] verdict is sufficient for that
    capstone. The hand-written OCaml mirror is ELIMINATED: [project_wf_dec] here
    converts the runtime types into the extracted Coq types and calls the proven
    extracted function.

    WHAT IS PROVEN (in Coq) AND EXECUTED (here): if
    [project_wf_dec p pf order =
    true] then the capstone conclusion holds —
    the project compiles, converges in ≤2 passes, stays fatal-free, warns iff a
    \ref is unresolved.

    WHAT IS TESTED (here + test_compile_evidence.ml): that this OCaml extractor
    faithfully reflects the source (duplicate \label, unsupported feature) and
    that the extracted [project_wf_dec] returns the same verdicts as the Coq
    [Example]s on the shared example projects.

    WHAT STAYS TRUSTED: [Parser_l2] byte->AST correctness, and the small
    runtime->extracted-type conversion in [compile_evidence.ml]. See
    docs/COMPILATION_GUARANTEE.md. *)

(** The abstract features the Coq model reasons about (mirror of
    [BuildProfileSound.feature]). *)
type feature =
  | UTF8_inputenc
  | UTF8_direct
  | Unicode_math
  | Opentype_fonts
  | Lua_scripting
  | Japanese_cjk
  | Bibtex
  | Biber

(** Mirror of [BuildProfileSound.engine]. *)
type engine = Pdflatex | Xelatex | Lualatex | Ptex_uptex

(** Mirror of [ProjectClosure.artefact_kind]. *)
type artefact_kind = Tex | Aux | Bbl | Bib | Pdf | Log

type node = { n_file : int; n_kind : artefact_kind }
(** Mirror of [ProjectClosure.node]: a build artefact identified by a numeric
    file id and its kind. *)

(** Mirror of [PdflatexModel.body_token]: the faithful document-body stream. *)
type body_token =
  | BT_text
  | BT_label_def of int
  | BT_label_ref of int
  | BT_needs_feature of feature

type project = {
  proj_nodes : node list;
  proj_edges : (node * node) list;
  proj_body : body_token list;
}
(** Mirror of [PdflatexModel.pdflatex_project]. *)

type profile = { prof_engine : engine; prof_features : feature list }
(** Mirror of [PdflatexModel.pdflatex_profile]. *)

val feature_to_string : feature -> string
(** Lowercase snake_case name of a feature (e.g.
    [Opentype_fonts ->
    "opentype_fonts"]), for the MODEL-CONNECTED verdict
    line. *)

val engine_to_string : engine -> string
(** Lowercase name of an engine (e.g. [Pdflatex -> "pdflatex"]). *)

val feature_compatible : feature -> engine -> bool
(** Mirror of [BuildProfileSound.compatible]. Kept byte-identical to the Coq
    table (and to [Compile_contract.feature_compatible]). *)

val body_required_features : body_token list -> feature list
(** [body_required_features body] — the [BT_needs_feature] elements, in order.
    Mirror of [PdflatexModel.body_required_features]. *)

val body_label_defs : body_token list -> int list
(** [body_label_defs body] — the [BT_label_def] ids, in order. Mirror of
    [PdflatexModel.body_label_defs]. *)

val project_wf_dec : project -> profile -> node list -> bool
(** The Coq-EXTRACTED [CompileGuaranteeBridge.project_wf_dec] (via
    [Compile_guarantee_extracted]), executed on the runtime project after a 1:1
    conversion to the extracted Coq types: the decidable capstone-premise check.
    [order] is a candidate topological order of the build-graph nodes (as the
    Coq checker verifies rather than searches for one). Returns [true] iff T2
    (closed+acyclic via [order]) AND T3 (engine admits declared + body-required
    features) AND T4 (label defs are unique). A [true] verdict is PROVEN
    sufficient for [pdflatex_compile_safe] by [project_wf_dec_sound]. *)

type premise_report = {
  t2_closed : bool;
      (** edges closed AND [order] is a valid topological sort. *)
  t3_declared : bool;  (** engine admits the profile's declared features. *)
  t3_body : bool;  (** engine admits every feature the body requires. *)
  t4_unique_labels : bool;  (** no duplicate \label in the body. *)
  duplicate_labels : string list;  (** the offending label keys, if any. *)
  unsupported_features : feature list;  (** body features the engine rejects. *)
}
(** Per-obligation verdict, for reporting WHICH premise failed. *)

val report : project -> profile -> node list -> premise_report
(** All four obligations, individually, for a MODEL-CONNECTED verdict line.
    [all_hold r] iff [project_wf_dec] would return [true]. *)

val all_hold : premise_report -> bool

(** ── Extraction from a real document ──────────────────────────────── *)

val extract : source:string -> engine:engine -> project * profile * node list
(** [extract ~source ~engine] maps a real .tex string to the abstract [project]
    \+ [profile] the Coq checker consumes, REUSING
    [Ast_semantic_state.labels]/[refs] for label/ref extraction and detecting
    the T3-relevant features (fontspec/unicode-math/luacode/CJK/…) from the
    source. Labels are hashed to stable [int]s ([label_id]); the same key hashes
    identically for a def and its refs. Also returns the candidate topological
    [order] for the build graph. *)

val extract_of_project :
  source:string -> Project_model.t -> project * profile * node list
(** [extract_of_project ~source proj] is [extract] with the engine taken from a
    [Project_model.t], and the build graph taken from [Build_graph.of_project]
    (so T2 reflects the real include graph, not just the root file). *)

val label_id : string -> int
(** Stable label-key -> nat hash (exposed for tests / mirror checks). *)

val duplicate_label_keys : string -> string list
(** [duplicate_label_keys source] — the label keys that appear more than once in
    [source] (under the [label_id] hash), for reporting a T4 violation with the
    offending names. *)

val feature_of_project_feature :
  Project_model.declared_feature -> feature option
(** [feature_of_project_feature] maps a [Project_model.declared_feature] to the
    Coq-model [feature] where one exists (the T3-relevant subset); features
    outside the model (Babel_standard, Hyperref, …) return [None] and are
    IGNORED by the T3 check, exactly as in Coq. *)
