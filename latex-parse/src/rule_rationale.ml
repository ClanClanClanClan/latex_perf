(** Rule_rationale — WS9: policy explanation and rationale links.

    The plan for the ~211 genuinely-un-fixable diagnose-only rules: since we
    cannot auto-fix them, give the author a clear RATIONALE (why the rule
    matters), a MANUAL REMEDIATION (how to fix it yourself), and a DOC LINK to
    the rule catalogue. {!explain} resolves ANY rule id to a non-empty
    explanation without hand-writing 660 paragraphs, by composing three sources:

    - the rule's own {b catalogue description} (specs/rules/rules_v3.yaml) as
      the rule-specific rationale base;
    - a {b per-family remediation template} (governance/rule_remediation.yaml)
      covering EVERY family (e.g. LAY/COL/META/PDF/PRJ = "derived from the
      compile log / project state; adjust the layout or resolve the underlying
      issue — not a source-text fix"; REF/BIB = "check your \\label/\\ref keys
      and .bib entries match"; STYLE = "a stylistic/consistency choice;
      normalize per your house style");
    - curated per-rule OVERRIDES for the highest-value rules, which win over the
      family default.

    Every field of {!explanation} is non-empty for every catalogued rule; an
    unknown id returns [None]. There is deliberately NO [.mli] — the docs live
    inline (WS9 mli-doc-ceiling policy). *)

(* ── Types ─────────────────────────────────────────────────────────────── *)

type explanation = {
  rule_id : string;  (** the rule id this explains, e.g. ["LAY-001"] *)
  rule_message : string;
      (** the catalogue description of the rule (its human-readable meaning) *)
  rationale : string;
      (** why the rule matters — the catalogue description, prefixed with the
          rule's default severity so the author sees the stakes *)
  remediation : string;
      (** how to fix it by hand — the curated override if one exists, else the
          per-family remediation template. Always non-empty. *)
  doc_link : string;  (** a link/anchor into the rule catalogue for this id *)
}
(** A fully-resolved explanation for one rule. Every field is non-empty. *)

(* ── Family extraction ─────────────────────────────────────────────────── *)

(** The FAMILY of a rule id is its prefix up to the first ['-'] (e.g. ["LAY"]
    for ["LAY-001"]). Ids with no ['-'] are their own family. *)
let family_of (rule_id : string) : string =
  match String.index_opt rule_id '-' with
  | Some i -> String.sub rule_id 0 i
  | None -> rule_id

(* ── Minimal shared lexical helpers ────────────────────────────────────── *)

(* Extract the double-quoted value on a `key: "value"` line, or [None]. We do
   not depend on a YAML library: both source files use the same regular
   quoted-scalar shape (see rules_v3.yaml / rule_remediation.yaml). *)
let quoted_value (line : string) : string option =
  match String.index_opt line '"' with
  | None -> None
  | Some i -> (
      match String.rindex_opt line '"' with
      | Some j when j > i -> Some (String.sub line (i + 1) (j - i - 1))
      | _ -> None)

(* True iff [s] starts with [prefix]. *)
let starts_with (s : string) (prefix : string) : bool =
  let n = String.length prefix in
  String.length s >= n && String.sub s 0 n = prefix

let trim_l = String.trim

(* ── Path resolution (mirrors Rule_contract_loader) ────────────────────── *)

(* Search order for a data file [rel] (relative to repo root): an explicit env
   override, then the cwd-relative path, then an upward walk from the running
   executable's directory (so the CLI finds the files from a _build tree). *)
let candidate_paths ~(env_var : string) ~(rel : string) : string list =
  let env = match Sys.getenv_opt env_var with Some s -> [ s ] | None -> [] in
  let exe_dir = Filename.dirname Sys.executable_name in
  let upward =
    let rec up acc dir depth =
      if depth <= 0 then acc
      else
        let candidate = Filename.concat dir rel in
        let next = Filename.dirname dir in
        if next = dir then candidate :: acc
        else up (candidate :: acc) next (depth - 1)
    in
    up [] exe_dir 8
  in
  env @ [ rel ] @ upward

let read_file_opt (path : string) : string option =
  try
    let ic = open_in_bin path in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    Some content
  with Sys_error _ -> None

let find_and_read ~env_var ~rel : (string * string) option =
  let rec go = function
    | [] -> None
    | p :: rest -> (
        match read_file_opt p with Some c -> Some (p, c) | None -> go rest)
  in
  go (candidate_paths ~env_var ~rel)

(* ── Catalogue (rules_v3.yaml): id -> (description, severity) ──────────── *)

type cat_entry = { c_description : string; c_severity : string }

(* Parse rules_v3.yaml. Each record starts on a `- id: "..."` line and carries
   `description:` / `default_severity:` sibling lines until the next `- id:`.
   Loading is total: unparseable lines are skipped, never raised. *)
let parse_catalogue (content : string) : (string, cat_entry) Hashtbl.t =
  let tbl = Hashtbl.create 1024 in
  let cur_id = ref None in
  let cur_desc = ref "" in
  let cur_sev = ref "Info" in
  let flush () =
    match !cur_id with
    | Some id ->
        Hashtbl.replace tbl id
          { c_description = !cur_desc; c_severity = !cur_sev }
    | None -> ()
  in
  String.split_on_char '\n' content
  |> List.iter (fun raw ->
         let line = trim_l raw in
         if starts_with line "- id:" then (
           flush ();
           cur_id := quoted_value line;
           cur_desc := "";
           cur_sev := "Info")
         else if starts_with line "description:" then
           match quoted_value line with Some d -> cur_desc := d | None -> ()
         else if starts_with line "default_severity:" then
           (* default_severity: Warning (unquoted scalar) *)
           match String.index_opt line ':' with
           | Some i ->
               let v =
                 trim_l (String.sub line (i + 1) (String.length line - i - 1))
               in
               if v <> "" then cur_sev := v
           | None -> ());
  flush ();
  tbl

let _catalogue : (string, cat_entry) Hashtbl.t option ref = ref None
let _catalogue_path : string option ref = ref None

let catalogue () : (string, cat_entry) Hashtbl.t =
  match !_catalogue with
  | Some t -> t
  | None ->
      let t =
        match
          find_and_read ~env_var:"LP_RULES_YAML"
            ~rel:"specs/rules/rules_v3.yaml"
        with
        | Some (path, content) ->
            _catalogue_path := Some path;
            parse_catalogue content
        | None -> Hashtbl.create 1
      in
      _catalogue := Some t;
      t

(* ── Remediation table (rule_remediation.yaml) ─────────────────────────── *)

type remediation_table = {
  families : (string, string) Hashtbl.t;
  overrides : (string, string) Hashtbl.t;
  errors : (int * string) list;  (** (1-based line no, message) *)
}

(* Parse rule_remediation.yaml: a `families:` block and an `overrides:` block,
   each holding `KEY: "value"` lines. Section is chosen by the last top-level
   (column-0) `families:` / `overrides:` header seen. Loading is total: a
   two-space-indented entry with no parseable quoted value under a known section
   is recorded in [errors]. *)
let parse_remediation (content : string) : remediation_table =
  let families = Hashtbl.create 128 in
  let overrides = Hashtbl.create 128 in
  let errors = ref [] in
  let section = ref `None in
  String.split_on_char '\n' content
  |> List.iteri (fun idx raw ->
         let lineno = idx + 1 in
         (* Strip a trailing comment only when the line has no quoted value (a
            value may legitimately contain '#'). *)
         let no_comment =
           if String.contains raw '"' then raw
           else
             match String.index_opt raw '#' with
             | Some i -> String.sub raw 0 i
             | None -> raw
         in
         let trimmed = trim_l no_comment in
         if trimmed = "" then ()
         else if starts_with no_comment "families:" then section := `Families
         else if starts_with no_comment "overrides:" then section := `Overrides
         else if String.length no_comment >= 2 && no_comment.[0] = ' ' then
           (* an indented `KEY: "value"` entry *)
           match String.index_opt trimmed ':' with
           | Some ci -> (
               let key = trim_l (String.sub trimmed 0 ci) in
               match (quoted_value trimmed, !section) with
               | Some v, `Families -> Hashtbl.replace families key v
               | Some v, `Overrides -> Hashtbl.replace overrides key v
               | Some _, `None ->
                   errors :=
                     (lineno, "entry before any families:/overrides: section")
                     :: !errors
               | None, (`Families | `Overrides) ->
                   errors :=
                     (lineno, "missing quoted value for " ^ key) :: !errors
               | None, `None -> ())
           | None -> ());
  { families; overrides; errors = List.rev !errors }

let _remediation : remediation_table option ref = ref None
let _remediation_path : string option ref = ref None

let remediation () : remediation_table =
  match !_remediation with
  | Some t -> t
  | None ->
      let t =
        match
          find_and_read ~env_var:"LP_RULE_REMEDIATION_YAML"
            ~rel:"governance/rule_remediation.yaml"
        with
        | Some (path, content) ->
            _remediation_path := Some path;
            parse_remediation content
        | None ->
            {
              families = Hashtbl.create 1;
              overrides = Hashtbl.create 1;
              errors = [ (0, "rule_remediation.yaml not found") ];
            }
      in
      _remediation := Some t;
      t

(* ── Public API ────────────────────────────────────────────────────────── *)

(** The remediation string for [rule_id]: a curated per-rule override if one
    exists, else the family template, else a generic fallback. Never empty. *)
let remediation_for (rule_id : string) : string =
  let t = remediation () in
  match Hashtbl.find_opt t.overrides rule_id with
  | Some s -> s
  | None -> (
      match Hashtbl.find_opt t.families (family_of rule_id) with
      | Some s -> s
      | None ->
          "No auto-fix is available. Review the flagged construct in the \
           source and adjust it by hand to satisfy the rule.")

(** A stable documentation link/anchor into the rule catalogue for [rule_id].
    The anchor is the lower-cased id, matching the catalogue's per-rule entry. *)
let doc_link_for (rule_id : string) : string =
  "specs/rules/rules_v3.yaml#" ^ String.lowercase_ascii rule_id

(** [explain rule_id] resolves a full {!explanation}, or [None] if [rule_id] is
    not in the catalogue. Every field of the returned record is non-empty:
    - [rule_message] is the catalogue description;
    - [rationale] is the description prefixed with the default severity;
    - [remediation] is the curated override or the family template;
    - [doc_link] is the catalogue anchor. *)
let explain (rule_id : string) : explanation option =
  match Hashtbl.find_opt (catalogue ()) rule_id with
  | None -> None
  | Some { c_description; c_severity } ->
      let desc =
        if String.trim c_description = "" then
          "(no catalogue description on record for " ^ rule_id ^ ")"
        else c_description
      in
      Some
        {
          rule_id;
          rule_message = desc;
          rationale =
            Printf.sprintf "[%s] %s — this rule flags: %s" c_severity rule_id
              desc;
          remediation = remediation_for rule_id;
          doc_link = doc_link_for rule_id;
        }

(** Render an {!explanation} as a human-readable multi-line block suitable for
    [--explain] on the CLI. *)
let to_human_string (e : explanation) : string =
  Printf.sprintf
    "%s\n\
    \  message:     %s\n\
    \  rationale:   %s\n\
    \  remediation: %s\n\
    \  doc:         %s" e.rule_id e.rule_message e.rationale e.remediation
    e.doc_link

(** A one-line explanation for a rule id, for inline use next to a finding (e.g.
    the [--policy] output). Falls back to a family/remediation line even for an
    id missing from the catalogue, so a waived/flagged rule always shows WHY. *)
let one_line (rule_id : string) : string =
  match explain rule_id with
  | Some e -> Printf.sprintf "%s: %s [%s]" rule_id e.remediation e.doc_link
  | None ->
      Printf.sprintf "%s: %s [%s]" rule_id (remediation_for rule_id)
        (doc_link_for rule_id)

(* ── Coverage self-report ──────────────────────────────────────────────── *)

(** [(resolved, total)]: how many catalogued rule ids resolve to a non-empty
    rationale AND non-empty remediation. Used by the coverage gate/test. *)
let coverage () : int * int =
  let t = catalogue () in
  let total = Hashtbl.length t in
  let resolved = ref 0 in
  Hashtbl.iter
    (fun id _ ->
      match explain id with
      | Some e
        when String.trim e.rationale <> "" && String.trim e.remediation <> "" ->
          incr resolved
      | _ -> ())
    t;
  (!resolved, total)

(** The resolved paths of the catalogue and remediation data files (for
    diagnostics), or [None] if a file was not found. *)
let data_paths () : string option * string option =
  ignore (catalogue ());
  ignore (remediation ());
  (!_catalogue_path, !_remediation_path)
