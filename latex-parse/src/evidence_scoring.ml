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

(** Load scoring config from a JSON file (spec W75: "config file loaded").
    Format: {"min_confidence":"Low","min_weight":0.0,"boost_vpd_rules":true} *)
let config_from_file (path : string) : scoring_config =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    let json = Yojson.Safe.from_string (Bytes.to_string s) in
    let open Yojson.Safe.Util in
    let min_conf =
      match json |> member "min_confidence" |> to_string with
      | "High" -> High
      | "Medium" -> Medium
      | _ -> Low
    in
    let min_w = try json |> member "min_weight" |> to_float with _ -> 0.0 in
    let boost =
      try json |> member "boost_vpd_rules" |> to_bool with _ -> true
    in
    { min_confidence = min_conf; min_weight = min_w; boost_vpd_rules = boost }
  with _ -> default_config

(** Try to load config from default path, fall back to default_config. *)
let load_config () : scoring_config =
  let default_path = "evidence_scoring.json" in
  match Sys.getenv_opt "LP_SCORING_CONFIG" with
  | Some path -> config_from_file path
  | None ->
      if Sys.file_exists default_path then config_from_file default_path
      else default_config

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

(* ── ML confidence integration (spec W105-110) ─────────────── *)

type ml_rule_confidence = { precision : float; weight : float; suppress : bool }

let load_ml_confidence_map (path : string) :
    (string, ml_rule_confidence) Hashtbl.t =
  let tbl = Hashtbl.create 16 in
  (try
     let ic = open_in path in
     let n = in_channel_length ic in
     let s = Bytes.create n in
     really_input ic s 0 n;
     close_in ic;
     let json = Yojson.Safe.from_string (Bytes.to_string s) in
     let open Yojson.Safe.Util in
     List.iter
       (fun (rule_id, obj) ->
         let precision =
           try obj |> member "precision" |> to_float with _ -> 1.0
         in
         let weight = try obj |> member "weight" |> to_float with _ -> 1.0 in
         let suppress =
           try obj |> member "suppress" |> to_bool with _ -> false
         in
         Hashtbl.replace tbl rule_id { precision; weight; suppress })
       (to_assoc json)
   with exn ->
     Printf.eprintf
       "[evidence_scoring] WARNING: failed to load ML confidence map from %s: %s\n\
        %!"
       path (Printexc.to_string exn));
  tbl

let apply_ml_boost (map : (string, ml_rule_confidence) Hashtbl.t)
    (results : scored_result list) : scored_result list =
  if Hashtbl.length map = 0 then results
  else
    List.filter_map
      (fun r ->
        match Hashtbl.find_opt map r.id with
        | None -> Some r
        | Some { suppress = true; _ } -> None
        | Some { weight; _ } ->
            Some { r with evidence_weight = r.evidence_weight *. weight })
      results

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
