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

(** Deterministic tier-membership decision procedure.

    Order (per specs/v26/language_contract.md): 1. If any foreign_trigger
    feature present → LP_Foreign 2. If any forbidden_in_core feature present →
    LP_Extended 3. Otherwise → LP_Core *)
let classify_source src =
  let features = Unsupported_feature.detect src in
  if Unsupported_feature.any_foreign_trigger features then
    ( LP_Foreign,
      List.filter
        (fun (f : Unsupported_feature.t) ->
          f.severity = Unsupported_feature.Foreign_trigger)
        features )
  else if Unsupported_feature.any_forbidden_in_core features then
    ( LP_Extended,
      List.filter
        (fun (f : Unsupported_feature.t) ->
          f.severity = Unsupported_feature.Forbidden_in_core)
        features )
  else (LP_Core, [])

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
