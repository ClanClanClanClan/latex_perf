(** Unit tests for [Editorial_review] (WS9 Stage 2).

    Covers the acceptance behaviours: 1. a resolved finding is hidden AND
    annotated, 2. an owner is recorded and surfaced, 3. the batch report
    aggregates counts correctly by rule / severity / file, 4. a malformed
    review-state file is reported (not crashed), 5. no assignment = default
    [New] state with unchanged result list. *)

open Printf
module ER = Latex_parse_lib.Editorial_review
module VC = Latex_parse_lib.Validators

let failures = ref 0

let check name cond =
  if cond then printf "ok   - %s\n" name
  else (
    incr failures;
    printf "FAIL - %s\n" name)

(* A small synthetic result set (rule-aggregated: id, severity, message,
   count). *)
let sample () : VC.result list =
  [
    VC.mk_result ~id:"TYPO-001" ~severity:VC.Warning ~message:"straight quote"
      ~count:3;
    VC.mk_result ~id:"SPC-016" ~severity:VC.Warning ~message:"space before ;"
      ~count:1;
    VC.mk_result ~id:"DELIM-009" ~severity:VC.Info ~message:"delimiter" ~count:2;
  ]

let ids rs = List.map (fun (an : ER.annotated) -> an.ER.an_result.VC.id) rs

let states_of_string s =
  let tmp = Filename.temp_file "lpreview_test" ".lpreview" in
  let oc = open_out tmp in
  output_string oc s;
  close_out oc;
  let pr = ER.load tmp in
  Sys.remove tmp;
  pr

let () =
  (* ── 1. resolved is hidden AND annotated ──────────────────────────── *)
  let { ER.states; errors } =
    states_of_string
      "review SPC-016 resolved owner=alice reason=\"fixed in PR 12\"\n"
  in
  check "resolved: no parse errors" (errors = []);
  (* annotate does NOT hide, so we can see the resolved annotation *)
  let ann = ER.annotate states ~file:"doc.tex" (sample ()) in
  let spc =
    List.find (fun (a : ER.annotated) -> a.ER.an_result.VC.id = "SPC-016") ann
  in
  check "resolved: SPC-016 annotated Resolved" (spc.ER.an_state = ER.Resolved);
  check "resolved: owner surfaced on annotation" (spc.ER.an_owner = Some "alice");
  (* apply DOES hide resolved by default *)
  let kept, audit = ER.apply states ~file:"doc.tex" (sample ()) in
  check "resolved: SPC-016 hidden from apply output"
    (not (List.mem "SPC-016" (ids kept)));
  check "resolved: other findings survive"
    (List.mem "TYPO-001" (ids kept) && List.mem "DELIM-009" (ids kept));
  check "resolved: exactly one audit record" (List.length audit = 1);
  (match audit with
  | [ a ] ->
      check "audit: rule id" (a.ER.ra_rule = "SPC-016");
      check "audit: owner recorded" (a.ER.ra_owner = "alice");
      check "audit: state recorded" (a.ER.ra_state = ER.Resolved);
      check "audit: note recorded" (a.ER.ra_note = "fixed in PR 12");
      check "audit: count carried" (a.ER.ra_count = 1);
      check "audit: renders as REVIEW line"
        (let s = ER.review_audit_to_string a in
         String.length s > 6 && String.sub s 0 6 = "REVIEW")
  | _ -> check "audit: exactly one record" false);

  (* ── 2. owner is recorded and surfaced (acknowledged, not hidden) ──── *)
  let { ER.states; _ } =
    states_of_string "review TYPO-001 acknowledged owner=bob\n"
  in
  let kept, _ = ER.apply states ~file:"doc.tex" (sample ()) in
  let typo =
    List.find (fun (a : ER.annotated) -> a.ER.an_result.VC.id = "TYPO-001") kept
  in
  check "owner: acknowledged finding stays visible"
    (List.mem "TYPO-001" (ids kept));
  check "owner: owner surfaced" (typo.ER.an_owner = Some "bob");
  check "owner: state is Acknowledged" (typo.ER.an_state = ER.Acknowledged);
  check "owner: rendered line surfaces owner+state"
    (let s = ER.annotated_to_string typo in
     let has sub =
       let n = String.length sub and m = String.length s in
       let rec go i =
         if i + n > m then false
         else if String.sub s i n = sub then true
         else go (i + 1)
       in
       go 0
     in
     has "bob" && has "acknowledged");

  (* ── file glob scoping: assignment only applies to matching file ───── *)
  let { ER.states; _ } =
    states_of_string
      "review SPC-016 resolved owner=carol file=other/*.tex reason=\"n/a\"\n"
  in
  let kept, audit = ER.apply states ~file:"chapters/doc.tex" (sample ()) in
  check "glob: non-matching file does NOT hide SPC-016"
    (List.mem "SPC-016" (ids kept));
  check "glob: non-matching file emits no audit" (audit = []);
  let kept2, audit2 = ER.apply states ~file:"other/x.tex" (sample ()) in
  check "glob: matching file hides SPC-016"
    (not (List.mem "SPC-016" (ids kept2)));
  check "glob: matching file emits audit" (List.length audit2 = 1);

  (* ── 3. batch report aggregates by rule / severity / file ─────────── *)
  let f1 =
    [
      VC.mk_result ~id:"TYPO-001" ~severity:VC.Warning ~message:"q" ~count:2;
      VC.mk_result ~id:"SPC-016" ~severity:VC.Warning ~message:"s" ~count:1;
      VC.mk_result ~id:"DELIM-009" ~severity:VC.Info ~message:"d" ~count:5;
    ]
  in
  let f2 =
    [
      VC.mk_result ~id:"TYPO-001" ~severity:VC.Warning ~message:"q" ~count:4;
      VC.mk_result ~id:"ENC-004" ~severity:VC.Error ~message:"e" ~count:3;
    ]
  in
  let rep = ER.report [ ("a.tex", f1); ("b.tex", f2) ] in
  check "report: file_count" (rep.ER.file_count = 2);
  check "report: grand total" (rep.ER.total = 2 + 1 + 5 + 4 + 3);
  check "report: by_rule TYPO-001 summed across files"
    (List.assoc "TYPO-001" rep.ER.by_rule = 6);
  check "report: by_rule DELIM-009" (List.assoc "DELIM-009" rep.ER.by_rule = 5);
  check "report: by_rule ENC-004" (List.assoc "ENC-004" rep.ER.by_rule = 3);
  check "report: by_rule sorted ascending"
    (List.map fst rep.ER.by_rule
    = [ "DELIM-009"; "ENC-004"; "SPC-016"; "TYPO-001" ]);
  check "report: by_severity Warning"
    (List.assoc VC.Warning rep.ER.by_severity = 2 + 1 + 4);
  check "report: by_severity Error" (List.assoc VC.Error rep.ER.by_severity = 3);
  check "report: by_severity Info" (List.assoc VC.Info rep.ER.by_severity = 5);
  check "report: by_file a.tex" (List.assoc "a.tex" rep.ER.by_file = 8);
  check "report: by_file b.tex" (List.assoc "b.tex" rep.ER.by_file = 7);
  check "report: by_file preserves input order"
    (List.map fst rep.ER.by_file = [ "a.tex"; "b.tex" ]);
  (* renderers are non-empty and machine-shaped *)
  let tsv = ER.render_report_tsv rep in
  check "report tsv: mentions total" (String.length tsv > 0);
  let json = ER.render_report_json rep in
  check "report json: parses back as an object"
    (match Yojson.Safe.from_string json with `Assoc _ -> true | _ -> false);
  check "report json: total field correct"
    (match Yojson.Safe.from_string json with
    | `Assoc kv -> List.assoc "total" kv = `Int 15
    | _ -> false);

  (* empty report is well-defined *)
  let empty_rep = ER.report [] in
  check "report: empty is zero"
    (empty_rep.ER.total = 0
    && empty_rep.ER.file_count = 0
    && empty_rep.ER.by_rule = []);

  (* ── 4. malformed statefile is reported, not crashed ──────────────── *)
  let { ER.errors; _ } =
    states_of_string "review TYPO-001 bogusstate owner=x\n"
  in
  check "malformed: unknown state reported" (errors <> []);
  let { ER.states; errors } = states_of_string "review TYPO-001 resolved\n" in
  check "malformed: missing owner reported" (errors <> []);
  check "malformed: missing owner yields no assignment"
    (states.ER.assignments = []);
  let { ER.errors; _ } = states_of_string "gibberish line here\n" in
  check "malformed: unknown directive reported" (errors <> []);
  let { ER.errors; _ } = ER.load "/no/such/review.lpreview" in
  check "malformed: missing file does not crash" (errors <> []);

  (* comments and blank lines are ignored *)
  let { ER.states; errors } =
    states_of_string
      "# a comment\n\nreview SPC-016 wontfix owner=dan reason=\"template\"\n"
  in
  check "comments: ignored, no errors" (errors = []);
  check "comments: one assignment parsed" (List.length states.ER.assignments = 1);

  (* ── 5. no assignment = default New, list unchanged ───────────────── *)
  let src = sample () in
  let kept, audit = ER.apply ER.empty ~file:"doc.tex" src in
  check "empty: ids unchanged"
    (ids kept = List.map (fun (r : VC.result) -> r.VC.id) src);
  check "empty: all default to New"
    (List.for_all (fun (a : ER.annotated) -> a.ER.an_state = ER.New) kept);
  check "empty: no owners" (List.for_all (fun a -> a.ER.an_owner = None) kept);
  check "empty: no audit records" (audit = []);

  (* round-trip: every state string parses back to itself *)
  check "state round-trip"
    (List.for_all
       (fun st ->
         ER.review_state_of_string (ER.review_state_to_string st) = Some st)
       [ ER.New; ER.Acknowledged; ER.Resolved; ER.Wontfix ]);

  if !failures = 0 then printf "\nAll editorial_review tests passed.\n"
  else (
    printf "\n%d editorial_review test(s) FAILED.\n" !failures;
    exit 1)
