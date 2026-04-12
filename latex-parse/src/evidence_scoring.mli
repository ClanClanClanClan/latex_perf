(** Confidence-weighted validator results (spec W75). *)

type confidence = High | Medium | Low

type scored_result = {
  id : string;
  severity : Validators_common.severity;
  message : string;
  count : int;
  confidence : confidence;
  evidence_weight : float;
}

type scoring_config = {
  min_confidence : confidence;
  min_weight : float;
  boost_vpd_rules : bool;
}

val default_config : scoring_config
val config_from_file : string -> scoring_config
val load_config : unit -> scoring_config
val score_result : Validators_common.result -> string list -> scored_result

val filter_by_config :
  scoring_config -> scored_result list -> scored_result list

type ml_rule_confidence = { precision : float; weight : float; suppress : bool }
(** ML-measured per-rule confidence (spec W105). *)

val load_ml_confidence_map : string -> (string, ml_rule_confidence) Hashtbl.t
(** Load ML confidence map from JSON. Returns empty table on error. *)

val apply_ml_boost :
  (string, ml_rule_confidence) Hashtbl.t ->
  scored_result list ->
  scored_result list
(** Suppress zero-TP rules, adjust weights for others. *)
