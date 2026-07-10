(** Editorial_policy — WS9 Stage 1: editorial policy system.

    A NAMED house-style profile can (a) disable specific rule ids so their
    findings are removed from output, (b) re-enable a rule id (undoing a prior
    [disable] in the same profile), and (c) override a rule id's severity
    (Warning to Error, to Info, and so on).

    A WAIVER suppresses a specific finding by rule-id, optionally narrowed by a
    file glob and/or a line range, with a REQUIRED reason string. A waived
    finding is removed from normal output BUT recorded in an AUDIT trail so that
    suppression is never silent.

    File format ([.lppolicy]) — one directive per line, blank lines and
    [#]-comments ignored. The grammar of a directive is one of:
    {v
      profile  <name>
      disable  <RULE-ID>
      enable   <RULE-ID>
      severity <RULE-ID> error|warning|info
      waive    <RULE-ID> [file=<glob>] [lines=<a>-<b>] reason="<text>"
    v}
    Loading is total: [waive] with an empty/absent [reason=], unknown
    directives, and malformed lines are collected in [errors] (each with its
    1-based line number) rather than raised. *)

type severity = Validators.severity

(* Locate the first occurrence of [pat] in [s], returning its start offset. *)
let find_substring (s : string) (pat : string) : int option =
  let n = String.length s and m = String.length pat in
  if m = 0 then Some 0
  else
    let rec go i =
      if i + m > n then None
      else if String.sub s i m = pat then Some i
      else go (i + 1)
    in
    go 0

(* A single waiver. [w_file_glob = None] matches any file; [w_lines = None]
   matches any line. [w_reason] is always non-empty (enforced at parse time). *)
type waiver = {
  w_rule : string;
  w_file_glob : string option;
  w_lines : (int * int) option;
  w_reason : string;
}

type t = {
  name : string;
  disabled : string list;  (** rule ids turned off *)
  enabled : string list;
      (** rule ids explicitly turned on (overrides [disabled] for the same id) *)
  severity_overrides : (string * severity) list;
  waivers : waiver list;
}

let empty =
  {
    name = "(none)";
    disabled = [];
    enabled = [];
    severity_overrides = [];
    waivers = [];
  }

type audit_record = {
  a_rule : string;
  a_severity : severity;  (** severity at the time of suppression *)
  a_count : int;  (** how many firings the suppressed result represented *)
  a_scope : string;  (** human-readable scope, e.g. "file=*.tex;lines=10-20" *)
  a_reason : string;
}
(** An audit record for one suppressed finding. Emitted so that every waiver is
    accountable. *)

(* ── Parsing helpers ─────────────────────────────────────────────────── *)

let severity_of_string = function
  | "error" | "Error" | "ERROR" -> Some Validators.Error
  | "warning" | "Warning" | "WARNING" -> Some Validators.Warning
  | "info" | "Info" | "INFO" -> Some Validators.Info
  | _ -> None

(* Split a line into the part before a trailing reason="..." field and the raw
   reason string (without the quotes) if a reason= field is present. *)
let extract_reason (line : string) : string * string option =
  match find_substring line "reason=" with
  | None -> (line, None)
  | Some i ->
      let before = String.sub line 0 i in
      let after = String.sub line (i + 7) (String.length line - (i + 7)) in
      let reason =
        let n = String.length after in
        if n > 0 && after.[0] = '"' then
          match String.index_from_opt after 1 '"' with
          | Some j -> String.sub after 1 (j - 1)
          | None -> String.sub after 1 (n - 1)
        else String.trim after
      in
      (before, Some reason)

let split_ws (s : string) : string list =
  String.split_on_char ' ' (String.map (fun c -> if c = '\t' then ' ' else c) s)
  |> List.filter (fun t -> t <> "")

(* Parse "lines=10-20" or "lines=15" → (10,20) / (15,15). *)
let parse_lines_field (s : string) : (int * int) option =
  match String.split_on_char '-' s with
  | [ a ] -> (
      match int_of_string_opt a with Some n -> Some (n, n) | None -> None)
  | [ a; b ] -> (
      match (int_of_string_opt a, int_of_string_opt b) with
      | Some x, Some y -> Some (x, y)
      | _ -> None)
  | _ -> None

type parse_result = { policy : t; errors : (int * string) list }

let parse_lines (name0 : string) (lines : string list) : parse_result =
  let name = ref name0 in
  let disabled = ref [] in
  let enabled = ref [] in
  let sev = ref [] in
  let waivers = ref [] in
  let errors = ref [] in
  List.iteri
    (fun idx raw ->
      let lineno = idx + 1 in
      (* Strip a comment starting at '#', but never inside a reason="..." field
         (a reason may legitimately contain '#'). *)
      let has_reason = find_substring raw "reason=" <> None in
      let line =
        if has_reason then raw
        else
          match String.index_opt raw '#' with
          | Some i -> String.sub raw 0 i
          | None -> raw
      in
      let trimmed = String.trim line in
      if trimmed = "" then ()
      else
        let before_reason, reason = extract_reason trimmed in
        let toks = split_ws before_reason in
        match toks with
        | [] -> ()
        | "profile" :: rest -> (
            match rest with
            | [ n ] -> name := n
            | _ -> errors := (lineno, "profile expects one name") :: !errors)
        | "disable" :: rest -> (
            match rest with
            | [ id ] -> disabled := id :: !disabled
            | _ -> errors := (lineno, "disable expects one rule id") :: !errors)
        | "enable" :: rest -> (
            match rest with
            | [ id ] -> enabled := id :: !enabled
            | _ -> errors := (lineno, "enable expects one rule id") :: !errors)
        | "severity" :: rest -> (
            match rest with
            | [ id; s ] -> (
                match severity_of_string s with
                | Some sv -> sev := (id, sv) :: !sev
                | None ->
                    errors :=
                      (lineno, "severity: unknown level " ^ s) :: !errors)
            | _ ->
                errors :=
                  (lineno, "severity expects <rule-id> <level>") :: !errors)
        | "waive" :: rest -> (
            match rest with
            | id :: fields -> (
                let file_glob = ref None in
                let lines_r = ref None in
                let ok = ref true in
                List.iter
                  (fun f ->
                    if String.length f >= 5 && String.sub f 0 5 = "file=" then
                      file_glob := Some (String.sub f 5 (String.length f - 5))
                    else if String.length f >= 6 && String.sub f 0 6 = "lines="
                    then (
                      (* lines= is NOT supported: findings are rule-aggregated
                         (no per-line offsets), so a line range cannot narrow a
                         waiver — accepting it silently would mislead users into
                         file-wide suppression.  Reject it explicitly; scope by
                         file= only. *)
                      ignore parse_lines_field;
                      ok := false;
                      errors :=
                        ( lineno,
                          "waive: lines= scoping is not supported (findings are                            rule-aggregated); scope by file= only" )
                        :: !errors)
                    else (
                      ok := false;
                      errors := (lineno, "waive: unknown field " ^ f) :: !errors))
                  fields;
                match reason with
                | Some r when String.trim r <> "" && !ok ->
                    waivers :=
                      {
                        w_rule = id;
                        w_file_glob = !file_glob;
                        w_lines = !lines_r;
                        w_reason = r;
                      }
                      :: !waivers
                | Some _ ->
                    if !ok then
                      errors :=
                        (lineno, "waive: reason= must be non-empty") :: !errors
                | None ->
                    errors :=
                      (lineno, "waive: missing required reason=\"...\"")
                      :: !errors)
            | [] -> errors := (lineno, "waive expects a rule id") :: !errors)
        | d :: _ -> errors := (lineno, "unknown directive: " ^ d) :: !errors)
    lines;
  {
    policy =
      {
        name = !name;
        disabled = List.rev !disabled;
        enabled = List.rev !enabled;
        severity_overrides = List.rev !sev;
        waivers = List.rev !waivers;
      };
    errors = List.rev !errors;
  }

(** Load a policy from a file. Total: on a read error, returns [empty] with the
    error recorded; never raises. *)
let load (path : string) : parse_result =
  match
    try
      let ic = open_in_bin path in
      let content = really_input_string ic (in_channel_length ic) in
      close_in ic;
      Ok content
    with Sys_error msg -> Error msg
  with
  | Error msg ->
      { policy = empty; errors = [ (0, "cannot read policy: " ^ msg) ] }
  | Ok content ->
      let base = Filename.remove_extension (Filename.basename path) in
      parse_lines base (String.split_on_char '\n' content)

(* ── Application ─────────────────────────────────────────────────────── *)

let is_disabled (p : t) (id : string) : bool =
  List.mem id p.disabled && not (List.mem id p.enabled)

let severity_for (p : t) (id : string) (default : severity) : severity =
  match List.assoc_opt id p.severity_overrides with
  | Some sv -> sv
  | None -> default

(* Simple glob: '*' matches any run (including empty), '?' one char. Matched
   against the full path and the basename (either match counts), so both `*.tex`
   and `chapters/*.tex` work naturally. *)
let glob_match (pat : string) (s : string) : bool =
  let np = String.length pat and ns = String.length s in
  let rec go pi si =
    if pi = np then si = ns
    else
      match pat.[pi] with
      | '*' -> go (pi + 1) si || (si < ns && go pi (si + 1))
      | '?' -> si < ns && go (pi + 1) (si + 1)
      | c -> si < ns && c = s.[si] && go (pi + 1) (si + 1)
  in
  go 0 0

let waiver_matches_file (w : waiver) (file : string) : bool =
  match w.w_file_glob with
  | None -> true
  | Some g -> glob_match g file || glob_match g (Filename.basename file)

let scope_string (w : waiver) : string =
  let parts =
    (match w.w_file_glob with Some g -> [ "file=" ^ g ] | None -> [])
    @
    match w.w_lines with
    | Some (a, b) -> [ Printf.sprintf "lines=%d-%d" a b ]
    | None -> []
  in
  match parts with [] -> "-" | _ -> String.concat ";" parts

(** [apply p ~file results] applies the profile (disable/enable + severity
    override) and the waivers to [results] for the file at path [file].

    Returns [(kept, audit)]:
    - [kept] is the results to display: disabled rules removed, severities
      overridden, waived findings removed.
    - [audit] is one {!audit_record} per waived finding.

    A finding is waived when a waiver's rule id matches AND its file glob (if
    any) matches [file]. (Findings are rule-aggregated — they carry no per-line
    offsets — so a [lines=] scope is recorded in the audit trail for
    accountability but does not further narrow which aggregated result is
    suppressed.) *)
let apply (p : t) ~(file : string) (results : Validators.result list) :
    Validators.result list * audit_record list =
  let audit = ref [] in
  let kept =
    List.filter_map
      (fun (r : Validators.result) ->
        if is_disabled p r.id then None
        else
          let sv = severity_for p r.id r.severity in
          match
            List.find_opt
              (fun w -> w.w_rule = r.id && waiver_matches_file w file)
              p.waivers
          with
          | Some w ->
              audit :=
                {
                  a_rule = r.id;
                  a_severity = sv;
                  a_count = r.count;
                  a_scope = scope_string w;
                  a_reason = w.w_reason;
                }
                :: !audit;
              None
          | None -> Some { r with severity = sv })
      results
  in
  (kept, List.rev !audit)

(** Render one audit record as a tab-separated line:
    [WAIVED\t<rule-id>\t<severity>\t<count>\t<scope>\t<reason>]. *)
let audit_record_to_string (a : audit_record) : string =
  Printf.sprintf "WAIVED\t%s\t%s\t%d\t%s\t%s" a.a_rule
    (Validators.severity_to_string a.a_severity)
    a.a_count a.a_scope a.a_reason
