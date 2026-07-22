(** Language profile classifier.

    Mirrors [specs/v26/language_contract.yaml] runtime definition. See
    [language_profile.mli] for API. *)

type tier = LP_Core | LP_Extended | LP_Foreign

let tier_to_string = function
  | LP_Core -> "lp-core"
  | LP_Extended -> "lp-extended"
  | LP_Foreign -> "lp-foreign"

let tier_name = function
  | LP_Core -> "LP-Core"
  | LP_Extended -> "LP-Extended"
  | LP_Foreign -> "LP-Foreign"

let tier_of_string s =
  match String.lowercase_ascii s with
  | "lp-core" | "lp_core" | "core" -> Some LP_Core
  | "lp-extended" | "lp_extended" | "extended" -> Some LP_Extended
  | "lp-foreign" | "lp_foreign" | "foreign" -> Some LP_Foreign
  | _ -> None

(* Ordering: LP_Foreign < LP_Extended < LP_Core as strengths of guarantee. *)
let tier_rank = function LP_Foreign -> 0 | LP_Extended -> 1 | LP_Core -> 2
let tier_is_at_least a b = tier_rank a >= tier_rank b

(* Map a runtime-detected feature's severity onto the extracted Coq [severity].
   [f_id] is a spec-level proxy the proven [classify] never inspects (it only
   matches on [f_severity]); we pass 0 to satisfy the record. *)
let to_extracted_feature (f : Unsupported_feature.t) :
    Language_contract_extracted.feature =
  {
    f_id = 0;
    f_severity =
      (match f.severity with
      | Unsupported_feature.Forbidden_in_core ->
          Language_contract_extracted.Forbidden_in_core
      | Unsupported_feature.Foreign_trigger ->
          Language_contract_extracted.Foreign_trigger);
  }

(* Translate the extracted Coq [tier] back to the runtime [tier]. *)
let of_extracted_tier = function
  | Language_contract_extracted.LP_Core -> LP_Core
  | Language_contract_extracted.LP_Extended -> LP_Extended
  | Language_contract_extracted.LP_Foreign -> LP_Foreign

(** Deterministic tier-membership decision procedure.

    The tier DECISION (feature-list -> tier) is delegated to the Coq-EXTRACTED
    [Language_contract_extracted.classify] (generated from
    proofs/LanguageContractExtract.v, governed by [classify_lp_core_sound], Qed,
    0 admits). This eliminates the former hand-written OCaml mirror of the
    decision logic; only [Unsupported_feature.detect] (bytes -> feature-list)
    remains trusted (adversarially certified in test_language_contract_cert.ml).

    Order proven by the extracted classifier (per
    specs/v26/language_contract.md): 1. If any foreign_trigger feature present →
    LP_Foreign 2. If any forbidden_in_core feature present → LP_Extended 3.
    Otherwise → LP_Core. The returned feature list is filtered to those features
    that justify the decided tier. *)
let classify_source src =
  let features = Unsupported_feature.detect src in
  let tier =
    of_extracted_tier
      (Language_contract_extracted.classify
         (List.map to_extracted_feature features))
  in
  match tier with
  | LP_Foreign ->
      ( LP_Foreign,
        List.filter
          (fun (f : Unsupported_feature.t) ->
            f.severity = Unsupported_feature.Foreign_trigger)
          features )
  | LP_Extended ->
      ( LP_Extended,
        List.filter
          (fun (f : Unsupported_feature.t) ->
            f.severity = Unsupported_feature.Forbidden_in_core)
          features )
  | LP_Core -> (LP_Core, [])

(** Thread-local profile context.

    Uses the same Hashtbl-keyed-by-Thread.id pattern as [Validators_context],
    [File_context], [Partial_context] for consistency with the rest of the
    runtime. *)
module Context = struct
  let tbl : (int, tier) Hashtbl.t = Hashtbl.create 16

  let set t =
    let tid = Thread.id (Thread.self ()) in
    Hashtbl.replace tbl tid t

  let get () =
    let tid = Thread.id (Thread.self ()) in
    Hashtbl.find_opt tbl tid

  let clear () =
    let tid = Thread.id (Thread.self ()) in
    Hashtbl.remove tbl tid
end
