(** Editorial_review — WS9 Stage 2: issue review-states + batch editorial
    reports.

    This module builds on {!Editorial_policy} (WS9 Stage 1). Where a policy
    DISABLES or WAIVES a finding outright, a REVIEW STATE tracks the editorial
    lifecycle of a finding without necessarily removing it: a finding (keyed by
    rule-id, optionally narrowed by a file glob and/or a free-form scope label)
    can be marked [new], [acknowledged], [resolved] or [wontfix] and given an
    OWNER (who is responsible) and a NOTE (why). State assignments are AUDITABLE
    in the same spirit as waivers — every applied assignment is recorded with
    who/what/why so ownership is never silent.

    A REVIEW-STATE FILE ([.lpreview]) records assignments, one directive per
    line, blank lines and [#]-comments ignored. A directive is:
    {v
      review <RULE-ID> <state> owner=<name> [file=<glob>] [scope=<label>] \
             [reason="<why>"]
    v}
    where [<state>] is one of [new|acknowledged|resolved|wontfix] and
    [owner=<name>] is REQUIRED. Loading is total: a missing/unknown state, a
    missing owner, unknown fields and malformed lines are collected in [errors]
    (each with its 1-based line number) rather than raised.

    The shared lexical helpers ([glob_match], [split_ws], [find_substring],
    [extract_reason]) are REUSED from {!Editorial_policy} rather than
    duplicated. *)

module EP = Editorial_policy

type severity = Validators.severity

(* ── Review states ───────────────────────────────────────────────────── *)

type review_state =
  | New  (** freshly reported, not yet triaged *)
  | Acknowledged  (** seen and accepted as a real issue, owner working on it *)
  | Resolved  (** the underlying issue has been fixed / addressed *)
  | Wontfix  (** deliberately not going to be fixed (accepted as-is) *)

(** Parse a review-state keyword (case-insensitive). Returns [None] for an
    unknown token so the caller can report it as a parse error. *)
let review_state_of_string (s : string) : review_state option =
  match String.lowercase_ascii s with
  | "new" -> Some New
  | "acknowledged" | "ack" -> Some Acknowledged
  | "resolved" | "fixed" -> Some Resolved
  | "wontfix" | "won't-fix" | "wont-fix" -> Some Wontfix
  | _ -> None

(** Render a review state as its canonical lower-case keyword (the inverse of
    the primary spelling accepted by {!review_state_of_string}). *)
let review_state_to_string : review_state -> string = function
  | New -> "new"
  | Acknowledged -> "acknowledged"
  | Resolved -> "resolved"
  | Wontfix -> "wontfix"

type assignment = {
  rs_rule : string;  (** rule id this assignment applies to *)
  rs_file_glob : string option;
      (** [None] = any file; otherwise a glob matched against the path and its
          basename (see {!Editorial_policy.glob_match}) *)
  rs_scope : string option;
      (** optional free-form scope label, recorded as-is *)
  rs_state : review_state;
  rs_owner : string;  (** who owns the finding (required, non-empty) *)
  rs_note : string;  (** why — free text, may be empty *)
}
(** A single review-state assignment parsed from a [.lpreview] line. *)

type t = { assignments : assignment list }
(** A loaded review-state set. *)

let empty : t = { assignments = [] }

type review_audit = {
  ra_rule : string;
  ra_file : string;  (** the file the assignment was applied to *)
  ra_state : review_state;
  ra_owner : string;
  ra_scope : string;  (** human-readable scope, e.g. "file=*.tex;scope=intro" *)
  ra_note : string;
  ra_count : int;  (** firings the annotated result represented *)
}
(** An audit record for one applied review-state assignment. Emitted so that
    every ownership/state decision is accountable (who/what/why). *)

type annotated = {
  an_result : Validators.result;
  an_state : review_state;  (** [New] when no assignment matched *)
  an_owner : string option;  (** [Some owner] when an assignment matched *)
  an_note : string option;
}
(** A validator result annotated with its review state and owner. Results with
    no matching assignment default to [New] with no owner. *)

(* ── Parsing ─────────────────────────────────────────────────────────── *)

type parse_result = { states : t; errors : (int * string) list }

(* Parse one non-comment directive line into either an assignment or an error
   message. [reason] is the already-extracted quoted note (or [None]). *)
let parse_directive (before_reason : string) (reason : string option) :
    (assignment, string) result =
  match EP.split_ws before_reason with
  | "review" :: id :: state_tok :: fields -> (
      match review_state_of_string state_tok with
      | None -> Error ("review: unknown state " ^ state_tok)
      | Some state -> (
          let owner = ref None in
          let file_glob = ref None in
          let scope = ref None in
          let err = ref None in
          List.iter
            (fun f ->
              let take prefix =
                let n = String.length prefix in
                if String.length f >= n && String.sub f 0 n = prefix then
                  Some (String.sub f n (String.length f - n))
                else None
              in
              match take "owner=" with
              | Some v -> owner := Some v
              | None -> (
                  match take "file=" with
                  | Some v -> file_glob := Some v
                  | None -> (
                      match take "scope=" with
                      | Some v -> scope := Some v
                      | None -> err := Some ("review: unknown field " ^ f))))
            fields;
          let note = match reason with Some r -> r | None -> "" in
          match (!err, !owner) with
          | Some e, _ -> Error e
          | None, None -> Error "review: missing required owner="
          | None, Some o when String.trim o = "" ->
              Error "review: owner= must be non-empty"
          | None, Some o ->
              Ok
                {
                  rs_rule = id;
                  rs_file_glob = !file_glob;
                  rs_scope = !scope;
                  rs_state = state;
                  rs_owner = o;
                  rs_note = note;
                }))
  | "review" :: _ -> Error "review expects <rule-id> <state> owner=<name>"
  | d :: _ -> Error ("unknown directive: " ^ d)
  | [] -> Error "empty directive"

(** Parse the lines of a [.lpreview] file into a review-state set plus a list of
    [(lineno, message)] parse errors. Total: never raises. *)
let parse_lines (lines : string list) : parse_result =
  let assigns = ref [] in
  let errors = ref [] in
  List.iteri
    (fun idx raw ->
      let lineno = idx + 1 in
      (* Keep a '#' that is part of a reason="..." field; strip it otherwise. *)
      let has_reason = EP.find_substring raw "reason=" <> None in
      let line =
        if has_reason then raw
        else
          match String.index_opt raw '#' with
          | Some i -> String.sub raw 0 i
          | None -> raw
      in
      if String.trim line = "" then ()
      else
        let before_reason, reason = EP.extract_reason (String.trim line) in
        match parse_directive before_reason reason with
        | Ok a -> assigns := a :: !assigns
        | Error msg -> errors := (lineno, msg) :: !errors)
    lines;
  { states = { assignments = List.rev !assigns }; errors = List.rev !errors }

(** Load a review-state set from a file. Total: on a read error, returns
    {!empty} with the error recorded; never raises. *)
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
      { states = empty; errors = [ (0, "cannot read review states: " ^ msg) ] }
  | Ok content -> parse_lines (String.split_on_char '\n' content)

(* ── Application ─────────────────────────────────────────────────────── *)

let assignment_matches (a : assignment) ~(file : string) (id : string) : bool =
  a.rs_rule = id
  &&
  match a.rs_file_glob with
  | None -> true
  | Some g -> EP.glob_match g file || EP.glob_match g (Filename.basename file)

let scope_string (a : assignment) : string =
  let parts =
    (match a.rs_file_glob with Some g -> [ "file=" ^ g ] | None -> [])
    @ match a.rs_scope with Some s -> [ "scope=" ^ s ] | None -> []
  in
  match parts with [] -> "-" | _ -> String.concat ";" parts

(** [annotate st ~file results] pairs each result with its matching review-state
    assignment for the file at path [file]. The FIRST matching assignment wins
    (file-scoped assignments should therefore precede catch-all ones in the
    file). Results with no match are annotated [New] with no owner. Does not
    filter anything out. *)
let annotate (st : t) ~(file : string) (results : Validators.result list) :
    annotated list =
  List.map
    (fun (r : Validators.result) ->
      match
        List.find_opt (fun a -> assignment_matches a ~file r.id) st.assignments
      with
      | Some a ->
          {
            an_result = r;
            an_state = a.rs_state;
            an_owner = Some a.rs_owner;
            an_note = Some a.rs_note;
          }
      | None ->
          { an_result = r; an_state = New; an_owner = None; an_note = None })
    results

(** [apply ?hide st ~file results] annotates [results] with their review states
    and filters out any whose state is in [hide] (default [[Resolved]] — a
    resolved finding is hidden from normal output).

    Returns [(kept, audit)]:
    - [kept] is the annotated results to display (those whose state is not
      hidden).
    - [audit] is one {!review_audit} per finding that MATCHED an explicit
      assignment (regardless of whether it was hidden), so every ownership/state
      decision is accountable. *)
let apply ?(hide = [ Resolved ]) (st : t) ~(file : string)
    (results : Validators.result list) : annotated list * review_audit list =
  let audit = ref [] in
  let annotated = annotate st ~file results in
  List.iter
    (fun an ->
      match an.an_owner with
      | None -> ()
      | Some owner ->
          audit :=
            {
              ra_rule = an.an_result.id;
              ra_file = file;
              ra_state = an.an_state;
              ra_owner = owner;
              ra_scope =
                (match
                   List.find_opt
                     (fun a -> assignment_matches a ~file an.an_result.id)
                     st.assignments
                 with
                | Some a -> scope_string a
                | None -> "-");
              ra_note = (match an.an_note with Some n -> n | None -> "");
              ra_count = an.an_result.count;
            }
            :: !audit)
    annotated;
  let kept =
    List.filter (fun an -> not (List.mem an.an_state hide)) annotated
  in
  (kept, List.rev !audit)

(** Render one annotated result as a tab-separated line:
    [<state>\t<owner>\t<rule-id>\t<severity>\t<count>\t<message>]. The owner is
    ["-"] when none is assigned. Suitable for machine consumption by an editor
    frontend. *)
let annotated_to_string (an : annotated) : string =
  Printf.sprintf "%s\t%s\t%s\t%s\t%d\t%s"
    (review_state_to_string an.an_state)
    (match an.an_owner with Some o -> o | None -> "-")
    an.an_result.id
    (Validators.severity_to_string an.an_result.severity)
    an.an_result.count an.an_result.message

(** Render one review audit record as a tab-separated line:
    [REVIEW\t<rule-id>\t<state>\t<owner>\t<count>\t<scope>\t<note>]. *)
let review_audit_to_string (a : review_audit) : string =
  Printf.sprintf "REVIEW\t%s\t%s\t%s\t%d\t%s\t%s" a.ra_rule
    (review_state_to_string a.ra_state)
    a.ra_owner a.ra_count a.ra_scope a.ra_note

(* ── Batch editorial report ──────────────────────────────────────────── *)

type report = {
  total : int;  (** grand total of all firing counts across all files *)
  file_count : int;  (** number of files aggregated *)
  by_rule : (string * int) list;
      (** firing count summed per rule id, sorted by rule id ascending *)
  by_severity : (severity * int) list;
      (** firing count summed per severity (Error, Warning, Info order) *)
  by_file : (string * int) list;
      (** firing count summed per file, in the input file order *)
}
(** An aggregate editorial report over the findings of one or more files. Counts
    are sums of each result's [count] (i.e. firings), not the number of distinct
    rules. *)

(* Accumulate [delta] onto the association-list entry for [key] (assoc-list is
   small — rule/file cardinality is bounded — so linear update is fine). *)
let bump (tbl : (string * int) list ref) (key : string) (delta : int) : unit =
  let rec go = function
    | [] -> [ (key, delta) ]
    | (k, v) :: rest when k = key -> (k, v + delta) :: rest
    | kv :: rest -> kv :: go rest
  in
  tbl := go !tbl

(** [report files] aggregates the findings of a [(file, results)] list into a
    {!report}: total firings, per-rule, per-severity and per-file counts. The
    same file appearing twice is aggregated once per occurrence (both
    contribute). *)
let report (files : (string * Validators.result list) list) : report =
  let by_rule = ref [] in
  let by_file = ref [] in
  let sev =
    ref [ (Validators.Error, 0); (Validators.Warning, 0); (Validators.Info, 0) ]
  in
  let total = ref 0 in
  List.iter
    (fun (file, results) ->
      List.iter
        (fun (r : Validators.result) ->
          bump by_rule r.id r.count;
          bump by_file file r.count;
          sev :=
            List.map
              (fun (s, v) ->
                if s = r.severity then (s, v + r.count) else (s, v))
              !sev;
          total := !total + r.count)
        results)
    files;
  let by_rule_sorted =
    List.sort (fun (a, _) (b, _) -> String.compare a b) !by_rule
  in
  {
    total = !total;
    file_count = List.length files;
    by_rule = by_rule_sorted;
    by_severity = !sev;
    by_file = !by_file;
  }

(** Render a {!report} as a tab-separated, machine-readable block. Each line is
    one of: [# total\t<n>], [# files\t<n>], [RULE\t<id>\t<count>],
    [SEVERITY\t<severity>\t<count>], [FILE\t<path>\t<count>]. *)
let render_report_tsv (rep : report) : string =
  let b = Buffer.create 256 in
  Printf.bprintf b "# total\t%d\n" rep.total;
  Printf.bprintf b "# files\t%d\n" rep.file_count;
  List.iter (fun (id, n) -> Printf.bprintf b "RULE\t%s\t%d\n" id n) rep.by_rule;
  List.iter
    (fun (s, n) ->
      Printf.bprintf b "SEVERITY\t%s\t%d\n" (Validators.severity_to_string s) n)
    rep.by_severity;
  List.iter (fun (f, n) -> Printf.bprintf b "FILE\t%s\t%d\n" f n) rep.by_file;
  Buffer.contents b

(** Render a {!report} as a single-line JSON object suitable for editorial
    export:
    [{"total":N,"files":F,"by_rule":{..},"by_severity":{..},
    "by_file":{..}}].
    Strings are escaped via {!Yojson.Safe}. *)
let render_report_json (rep : report) : string =
  let obj assoc = `Assoc assoc in
  let counts_of pairs = obj (List.map (fun (k, v) -> (k, `Int v)) pairs) in
  let json =
    `Assoc
      [
        ("total", `Int rep.total);
        ("files", `Int rep.file_count);
        ("by_rule", counts_of rep.by_rule);
        ( "by_severity",
          counts_of
            (List.map
               (fun (s, v) -> (Validators.severity_to_string s, v))
               rep.by_severity) );
        ("by_file", counts_of rep.by_file);
      ]
  in
  Yojson.Safe.to_string json
