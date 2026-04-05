(* ══════════════════════════════════════════════════════════════════════
   Evidence_scoring — confidence-weighted validator results (spec W75)

   Each validator result can be assigned a confidence score based on: - Rule
   maturity (Draft vs Stable) - Pattern family reliability (exact match vs
   heuristic) - Language detection confidence - Context quality (full document
   vs snippet)
   ══════════════════════════════════════════════════════════════════════ *)

type confidence = High | Medium | Low

type scored_result = {
  id : string;
  severity : Validators_common.severity;
  message : string;
  count : int;
  confidence : confidence;
  evidence_weight : float; (* 0.0 to 1.0 *)
}

type scoring_config = {
  min_confidence : confidence;
  min_weight : float;
  boost_vpd_rules : bool; (* VPD-certified rules get higher confidence *)
}

let default_config : scoring_config =
  { min_confidence = Low; min_weight = 0.0; boost_vpd_rules = true }

(* ── Scoring logic ──────────────────────────────────────────── *)

let confidence_of_rule (id : string) (vpd_ids : string list) : confidence =
  if List.mem id vpd_ids then High
  else
    let prefix =
      match String.index_opt id '-' with
      | Some i -> String.sub id 0 i
      | None -> id
    in
    match prefix with
    | "TYPO" | "ENC" | "CHAR" | "SPC" -> High (* lexical, exact patterns *)
    | "MATH" | "DELIM" | "SCRIPT" | "CHEM" -> Medium (* structural, may FP *)
    | "STYLE" | "LANG" -> Low (* heuristic, text-scanning *)
    | _ -> Medium

let weight_of_confidence = function High -> 1.0 | Medium -> 0.7 | Low -> 0.4

let score_result (result : Validators_common.result) (vpd_ids : string list) :
    scored_result =
  let confidence = confidence_of_rule result.id vpd_ids in
  {
    id = result.id;
    severity = result.severity;
    message = result.message;
    count = result.count;
    confidence;
    evidence_weight = weight_of_confidence confidence;
  }

let filter_by_config (config : scoring_config) (results : scored_result list) :
    scored_result list =
  List.filter
    (fun r ->
      r.evidence_weight >= config.min_weight
      &&
      match (config.min_confidence, r.confidence) with
      | High, High -> true
      | High, _ -> false
      | Medium, (High | Medium) -> true
      | Medium, Low -> false
      | Low, _ -> true)
    results
