(** Span Extractor Soundness — separate precision/recall bounds.

    Per Bootstrap Skeleton v25 R1, line 4492:
      ML/SpanExtractorSound.v — [span_extractor_sound_complete]

    v1 model (BERT+CRF) does NOT pass the F1 >= 0.94 gate.
    Actual v1 performance: precision=0.8965, recall=0.8086, F1=0.8503.
    v2 candidate classifier pipeline targets closing this gap.

    This proof:
    1. Records the actual measured error rates (honest, not aspirational).
    2. Documents the gap to target thresholds.
    3. Provides parameterised soundness theorems that hold once a model
       achieves the required precision/recall.

    Proof technique: concrete arithmetic on measured bounds via lra.
    Source: ml/results/20260319_234935/eval_results.json
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

(** ──────────────────────────────────────────────────────────────────── *)
(** Empirically measured error rates from v1 evaluation (2026-03-19).   *)
(** Model: bert-crf (allenai/scibert_scivocab_uncased), seed=42.       *)
(** Updated when model is retrained; values must match eval JSON.       *)
(** ──────────────────────────────────────────────────────────────────── *)

Definition measured_fp_rate : R := 1035 / 10000.  (* 1 - precision = 0.1035 *)
Definition measured_fn_rate : R := 1914 / 10000.  (* 1 - recall   = 0.1914 *)

(** Target thresholds per project spec (§14.2 line 250). *)
Definition precision_threshold : R := 94 / 100.
Definition recall_threshold    : R := 94 / 100.

(** ──────────────────────────────────────────────────────────────────── *)
(** Gap analysis: how far v1 is from the target.                        *)
(** precision_gap  = 0.94 - 0.8965 = 0.0435                            *)
(** recall_gap     = 0.94 - 0.8086 = 0.1314                            *)
(** ──────────────────────────────────────────────────────────────────── *)

Lemma precision_gap :
  (precision_threshold - (1 - measured_fp_rate) = 435 / 10000)%R.
Proof. unfold measured_fp_rate, precision_threshold. field. Qed.

Lemma recall_gap :
  (recall_threshold - (1 - measured_fn_rate) = 1314 / 10000)%R.
Proof. unfold measured_fn_rate, recall_threshold. field. Qed.

(** The v1 model does NOT pass the precision gate. *)
Lemma v1_precision_below_threshold :
  (1 - measured_fp_rate < precision_threshold)%R.
Proof. unfold measured_fp_rate, precision_threshold. lra. Qed.

(** The v1 model does NOT pass the recall gate. *)
Lemma v1_recall_below_threshold :
  (1 - measured_fn_rate < recall_threshold)%R.
Proof. unfold measured_fn_rate, recall_threshold. lra. Qed.

(** ──────────────────────────────────────────────────────────────────── *)
(** Parameterised soundness: holds for ANY model meeting the targets.   *)
(** These theorems become applicable once v2 achieves the thresholds.   *)
(** ──────────────────────────────────────────────────────────────────── *)

Theorem span_extractor_precision_sound :
  forall fp_rate : R,
    (fp_rate <= 1 - precision_threshold)%R ->
    (1 - fp_rate >= precision_threshold)%R.
Proof.
  intros fp_rate Hfp.
  unfold precision_threshold in *.
  lra.
Qed.

Theorem span_extractor_recall_sound :
  forall fn_rate : R,
    (fn_rate <= 1 - recall_threshold)%R ->
    (1 - fn_rate >= recall_threshold)%R.
Proof.
  intros fn_rate Hfn.
  unfold recall_threshold in *.
  lra.
Qed.

(** Combined soundness: if both rates are bounded, both thresholds hold. *)
Theorem span_extractor_sound_complete :
  forall fp_rate fn_rate : R,
    (fp_rate <= 1 - precision_threshold)%R ->
    (fn_rate <= 1 - recall_threshold)%R ->
    (1 - fp_rate >= precision_threshold)%R /\
    (1 - fn_rate >= recall_threshold)%R.
Proof.
  intros fp_rate fn_rate Hfp Hfn.
  split.
  - apply span_extractor_precision_sound; exact Hfp.
  - apply span_extractor_recall_sound; exact Hfn.
Qed.

(** ──────────────────────────────────────────────────────────────────── *)
(** Info severity invariant.                                            *)
(** When span extractor predictions are filtered to Info severity,      *)
(** false positives are bounded by the model's fp_rate.                 *)
(** ──────────────────────────────────────────────────────────────────── *)

Inductive severity := Error | Warning | Info.

Record span_prediction := mk_span {
  sp_severity : severity;
  sp_confidence : R;
}.

(** Info-filtered predictions maintain soundness when the model's
    false-positive rate meets the precision threshold. *)
Theorem info_severity_sound :
  forall (fp_rate : R) (sp : span_prediction),
    (fp_rate <= 1 - precision_threshold)%R ->
    sp_severity sp = Info ->
    (sp_confidence sp >= 1 - fp_rate)%R ->
    (sp_confidence sp >= precision_threshold)%R.
Proof.
  intros fp_rate sp Hfp _Hsev Hconf.
  unfold precision_threshold in *.
  lra.
Qed.
