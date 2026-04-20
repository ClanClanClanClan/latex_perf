(** Load per-rule contracts. See [rule_contract_loader.mli]. *)

module Y = Yojson.Safe

type execution_class = A | B | C | D
type proof_class = Formal_faithful | Formal_conservative | Formal_conditional

type evidence_class =
  | Source_pattern
  | Statistical_ml_bounded
  | Compile_log_evidence
  | External_binary

type project_scope = Lp_core_or_extended | Any_tier
type fix_scope = Local | Document

type contract = {
  rule_id : string;
  layer : Validator_dag.phase;
  execution_class : execution_class;
  proof_class : proof_class;
  evidence_class : evidence_class;
  consumes : string list;
  provides : string list;
  depends_on : string list;
  conflicts_with : string list;
  fix_scope : fix_scope;
  project_scope : project_scope;
}

let execution_class_to_string = function
  | A -> "A"
  | B -> "B"
  | C -> "C"
  | D -> "D"

let parse_execution_class = function
  | "A" -> A
  | "B" -> B
  | "C" -> C
  | "D" -> D
  | s -> failwith (Printf.sprintf "unknown execution_class %S" s)

let proof_class_to_string = function
  | Formal_faithful -> "formal_faithful"
  | Formal_conservative -> "formal_conservative"
  | Formal_conditional -> "formal_conditional"

let parse_proof_class = function
  | "formal_faithful" -> Formal_faithful
  | "formal_conservative" -> Formal_conservative
  | "formal_conditional" -> Formal_conditional
  | s -> failwith (Printf.sprintf "unknown proof_class %S" s)

let parse_evidence_class = function
  | "source_pattern_evidence" -> Source_pattern
  | "statistical_ml_bounded" -> Statistical_ml_bounded
  | "compile_log_evidence" -> Compile_log_evidence
  | "external_binary_evidence" -> External_binary
  | s -> failwith (Printf.sprintf "unknown evidence_class %S" s)

let parse_project_scope = function
  | "lp_core_or_extended" -> Lp_core_or_extended
  | "any" -> Any_tier
  | s -> failwith (Printf.sprintf "unknown project_scope %S" s)

let parse_fix_scope = function
  | "local" -> Local
  | "document" -> Document
  | s -> failwith (Printf.sprintf "unknown fix_scope %S" s)

let string_list j =
  match j with
  | `List xs ->
      List.map (function `String s -> s | _ -> failwith "expected string") xs
  | `Null -> []
  | _ -> failwith "expected list"

let parse_contract (j : Y.t) : contract =
  let open Y.Util in
  {
    rule_id = j |> member "rule_id" |> to_string;
    layer = Validator_dag.phase_of_string (j |> member "layer" |> to_string);
    execution_class =
      parse_execution_class (j |> member "execution_class" |> to_string);
    proof_class = parse_proof_class (j |> member "proof_class" |> to_string);
    evidence_class =
      parse_evidence_class (j |> member "evidence_class" |> to_string);
    consumes = j |> member "consumes" |> string_list;
    provides = j |> member "provides" |> string_list;
    depends_on = j |> member "depends_on" |> string_list;
    conflicts_with = j |> member "conflicts_with" |> string_list;
    fix_scope = parse_fix_scope (j |> member "fix_scope" |> to_string);
    project_scope =
      parse_project_scope (j |> member "project_scope" |> to_string);
  }

(* ── Path resolution ────────────────────────────────────────────── *)

(** Candidate locations for rule_contracts.json. The env var takes precedence;
    then we search upward from [Sys.executable_name] for the repo root
    containing [specs/rules/rule_contracts.json]. *)
let candidate_paths () =
  let env =
    match Sys.getenv_opt "LP_RULE_CONTRACTS_JSON" with
    | Some s -> [ s ]
    | None -> []
  in
  let exe_dir = Filename.dirname Sys.executable_name in
  let upward =
    let rec up acc dir depth =
      if depth <= 0 then acc
      else
        let candidate = Filename.concat dir "specs/rules/rule_contracts.json" in
        let next = Filename.dirname dir in
        if next = dir then candidate :: acc
        else up (candidate :: acc) next (depth - 1)
    in
    up [] exe_dir 8
  in
  let cwd_relative = [ "specs/rules/rule_contracts.json" ] in
  env @ cwd_relative @ upward

let find_json_file () = List.find_opt Sys.file_exists (candidate_paths ())

(* ── Memoised loader ────────────────────────────────────────────── *)

let _cache : contract list option ref = ref None

let do_load () : contract list =
  match find_json_file () with
  | None ->
      Printf.eprintf
        "[rule_contracts] WARNING: rule_contracts.json not found; falling back \
         to empty contract list\n\
         %!";
      []
  | Some path -> (
      try
        let root = Y.from_file path in
        let rules = Y.Util.member "rules" root in
        match rules with
        | `List xs -> List.map parse_contract xs
        | _ -> failwith "missing 'rules' array"
      with exn ->
        Printf.eprintf
          "[rule_contracts] WARNING: failed to parse %s: %s; falling back to \
           empty contract list\n\
           %!"
          path (Printexc.to_string exn);
        [])

let load () : contract list =
  match !_cache with
  | Some xs -> xs
  | None ->
      let xs = do_load () in
      _cache := Some xs;
      xs

let find_opt (rule_id : string) : contract option =
  List.find_opt (fun c -> c.rule_id = rule_id) (load ())

let count () : int = List.length (load ())

let to_validator_meta (c : contract) : Validator_dag.validator_meta =
  {
    Validator_dag.id = c.rule_id;
    phase = c.layer;
    provides = c.provides;
    requires = c.consumes @ c.depends_on;
    conflicts = c.conflicts_with;
  }
