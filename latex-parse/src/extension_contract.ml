(** Extension plane and foreign contracts (WS12 Stage 1). See the .mli. *)

module Y = Yojson.Safe

type risk = Safe | Review | Unsafe
type support = Foreign | Community | Supported

type contract = {
  ext_name : string;
  provides : string list;
  requires : string list;
  risk : risk;
  support : support;
}

(* ── Ordering / parsing ─────────────────────────────────────────── *)

let risk_to_string = function
  | Safe -> "safe"
  | Review -> "review"
  | Unsafe -> "unsafe"

let risk_of_string = function
  | "safe" -> Some Safe
  | "review" -> Some Review
  | "unsafe" -> Some Unsafe
  | _ -> None

let support_to_string = function
  | Foreign -> "foreign"
  | Community -> "community"
  | Supported -> "supported"

let support_of_string = function
  | "foreign" -> Some Foreign
  | "community" -> Some Community
  | "supported" -> Some Supported
  | _ -> None

let support_rank = function Foreign -> 0 | Community -> 1 | Supported -> 2
let support_min a b = if support_rank a <= support_rank b then a else b

(* The strongest support an extension of a given risk may legitimately claim.
   The higher the risk, the weaker the guarantee it is allowed to promise. *)
let max_support_for_risk = function
  | Safe -> Supported
  | Review -> Community
  | Unsafe -> Foreign

let over_claims (c : contract) : bool =
  support_rank c.support > support_rank (max_support_for_risk c.risk)

(* ── Manifest loading (total, errors reported) ──────────────────── *)

(* The manifest is a JSON object [{ "extensions": [ ... ] }], each entry
   declaring name / provides / requires / risk / support. Mirrors the
   rule_contracts.json shape. All parse failures are reported as [Error _]; this
   function never raises. *)

let string_list = function
  | `List xs ->
      List.fold_right
        (fun j acc ->
          match (j, acc) with
          | `String s, Ok tl -> Ok (s :: tl)
          | _, (Error _ as e) -> e
          | _, Ok _ -> Error "expected a list of strings")
        xs (Ok [])
  | `Null -> Ok []
  | _ -> Error "expected a JSON list"

let ( let* ) = Result.bind

let parse_contract (j : Y.t) : (contract, string) result =
  match j with
  | `Assoc _ ->
      let field k =
        match Y.Util.member k j with `Null -> None | v -> Some v
      in
      let* ext_name =
        match field "name" with
        | Some (`String s) -> Ok s
        | _ -> Error "extension missing string field \"name\""
      in
      let* risk =
        match field "risk" with
        | Some (`String s) -> (
            match risk_of_string s with
            | Some r -> Ok r
            | None ->
                Error
                  (Printf.sprintf
                     "extension %S: unknown risk %S (expected \
                      safe|review|unsafe)"
                     ext_name s))
        | _ ->
            Error
              (Printf.sprintf "extension %S missing string field \"risk\""
                 ext_name)
      in
      let* support =
        match field "support" with
        | Some (`String s) -> (
            match support_of_string s with
            | Some sp -> Ok sp
            | None ->
                Error
                  (Printf.sprintf
                     "extension %S: unknown support %S (expected \
                      supported|community|foreign)"
                     ext_name s))
        | _ ->
            Error
              (Printf.sprintf "extension %S missing string field \"support\""
                 ext_name)
      in
      let* provides =
        match field "provides" with
        | None -> Ok []
        | Some v ->
            Result.map_error
              (fun m -> Printf.sprintf "extension %S provides: %s" ext_name m)
              (string_list v)
      in
      let* requires =
        match field "requires" with
        | None -> Ok []
        | Some v ->
            Result.map_error
              (fun m -> Printf.sprintf "extension %S requires: %s" ext_name m)
              (string_list v)
      in
      Ok { ext_name; provides; requires; risk; support }
  | _ -> Error "each extension must be a JSON object"

let of_json (j : Y.t) : (contract list, string) result =
  let extensions =
    match j with
    | `Assoc _ -> (
        match Y.Util.member "extensions" j with `Null -> None | v -> Some v)
    | _ -> None
  in
  match extensions with
  | Some (`List xs) ->
      List.fold_right
        (fun j acc ->
          let* tl = acc in
          let* c = parse_contract j in
          Ok (c :: tl))
        xs (Ok [])
  | Some _ -> Error "\"extensions\" must be a JSON list"
  | None -> Error "manifest must be a JSON object with an \"extensions\" list"

let load_string (s : string) : (contract list, string) result =
  match Y.from_string s with
  | j -> of_json j
  | exception Yojson.Json_error msg ->
      (* EXN-OK: total loading — a malformed manifest is reported, not
         raised. *)
      Error (Printf.sprintf "invalid JSON: %s" msg)

let load_file (path : string) : (contract list, string) result =
  match
    let ic = open_in_bin path in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () -> really_input_string ic (in_channel_length ic))
  with
  | contents -> load_string contents
  | exception Sys_error msg ->
      (* EXN-OK: total loading — an unreadable file is reported, not raised. *)
      Error (Printf.sprintf "cannot read manifest %S: %s" path msg)

(* ── Foreign-contract boundary ──────────────────────────────────── *)

type entry = {
  e_name : string;
  e_risk : risk;
  e_declared : support;
  e_downgrade : bool;
  e_reason : string;
}

type effective = { base : support; effective : support; entries : entry list }

type rejection = {
  r_name : string;
  r_risk : risk;
  r_declared : support;
  r_reason : string;
}

let downgrade_cause (c : contract) : string =
  (* Prefer the most specific machine-readable cause. *)
  match (c.support, c.risk) with
  | Foreign, _ -> "foreign-support"
  | _, Unsafe -> "unsafe-risk"
  | _ -> "weaker-support"

let evaluate ~(base : support) (contracts : contract list) :
    (effective, rejection list) result =
  let rejections =
    List.filter_map
      (fun c ->
        if over_claims c then
          Some
            {
              r_name = c.ext_name;
              r_risk = c.risk;
              r_declared = c.support;
              r_reason =
                Printf.sprintf "over-claim:risk-%s-max-%s-declared-%s"
                  (risk_to_string c.risk)
                  (support_to_string (max_support_for_risk c.risk))
                  (support_to_string c.support);
            }
        else None)
      contracts
  in
  match rejections with
  | _ :: _ -> Error rejections
  | [] ->
      let effective =
        List.fold_left (fun acc c -> support_min acc c.support) base contracts
      in
      let entries =
        List.map
          (fun c ->
            let downgrade = support_rank c.support < support_rank base in
            let reason =
              if downgrade then
                Printf.sprintf "downgrade:%s-to-%s:%s" (support_to_string base)
                  (support_to_string c.support)
                  (downgrade_cause c)
              else Printf.sprintf "ok:%s" (support_to_string c.support)
            in
            {
              e_name = c.ext_name;
              e_risk = c.risk;
              e_declared = c.support;
              e_downgrade = downgrade;
              e_reason = reason;
            })
          contracts
      in
      Ok { base; effective; entries }

let downgrades_below (eff : effective) (threshold : support) : bool =
  support_rank eff.effective < support_rank threshold
