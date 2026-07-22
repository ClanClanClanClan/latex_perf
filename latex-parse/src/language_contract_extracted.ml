(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the proven tier classifier
   [LanguageContract.classify] and all its dependencies (data model + boolean
   sub-checkers). Regenerate with
   scripts/tools/regen_language_contract_extract.sh from
   proofs/LanguageContractExtract.v.

   [classify] here is the PROVEN classifier itself (not a hand mirror): the Coq
   lemma [classify_lp_core_sound] (Qed, 0 admits) proves that an [LP_Core]
   verdict implies no forbidden-in-core feature is present. [Language_profile]
   executes this module for the tier DECISION (feature-list -> tier); only the
   bytes->feature-list step ([Unsupported_feature.detect]) stays trusted.

   nat is extracted to OCaml int (ExtrOcamlNatInt): feature ids are spec-level
   proxies, and classify performs no arithmetic on them. *)

[@@@warning "-a"]

let existsb f =
  let rec existsb0 = function [] -> false | a :: l0 -> f a || existsb0 l0 in
  existsb0

type tier = LP_Core | LP_Extended | LP_Foreign
type severity = Forbidden_in_core | Foreign_trigger
type feature = { f_id : int; f_severity : severity }

let is_foreign f =
  match f.f_severity with Forbidden_in_core -> false | Foreign_trigger -> true

let is_forbidden_core f =
  match f.f_severity with Forbidden_in_core -> true | Foreign_trigger -> false

let any_foreign fs = existsb is_foreign fs
let any_forbidden_core fs = existsb is_forbidden_core fs

let classify fs =
  if any_foreign fs then LP_Foreign
  else if any_forbidden_core fs then LP_Extended
  else LP_Core
