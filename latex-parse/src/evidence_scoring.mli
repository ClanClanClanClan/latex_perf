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
val score_result : Validators_common.result -> string list -> scored_result

val filter_by_config :
  scoring_config -> scored_result list -> scored_result list
