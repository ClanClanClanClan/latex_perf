(** Unit tests for [Editorial_policy] (WS9 Stage 1).

    Covers the four acceptance behaviours: 1. a profile that disables a rule →
    that rule vanishes from output, 2. a severity override → the rule's severity
    changes, 3. a scoped waiver → only matching findings are suppressed AND an
    audit record is emitted, 4. the empty policy → output is unchanged
    (byte-identical result list). *)

open Printf
module EP = Latex_parse_lib.Editorial_policy
module VC = Latex_parse_lib.Validators

let failures = ref 0

let check name cond =
  if cond then printf "ok   - %s\n" name
  else (
    incr failures;
    printf "FAIL - %s\n" name)

(* A small synthetic result set. Results are rule-aggregated (id, severity,
   message, count); the policy layer operates on exactly this shape. *)
let sample () : VC.result list =
  [
    VC.mk_result ~id:"TYPO-001" ~severity:VC.Warning ~message:"straight quote"
      ~count:3;
    VC.mk_result ~id:"SPC-016" ~severity:VC.Warning ~message:"space before ;"
      ~count:1;
    VC.mk_result ~id:"DELIM-009" ~severity:VC.Info ~message:"delimiter" ~count:2;
  ]

let ids rs = List.map (fun (r : VC.result) -> r.VC.id) rs

let sev_of rs id =
  List.find_map
    (fun (r : VC.result) -> if r.VC.id = id then Some r.VC.severity else None)
    rs

(* Load a policy from an inline string via a temp file. *)
let policy_of_string s =
  let tmp = Filename.temp_file "lppolicy_test" ".lppolicy" in
  let oc = open_out tmp in
  output_string oc s;
  close_out oc;
  let pr = EP.load tmp in
  Sys.remove tmp;
  pr

let () =
  (* ── 1. disable removes the rule ──────────────────────────────────── *)
  let { EP.policy; errors } = policy_of_string "profile p\ndisable SPC-016\n" in
  check "disable: no parse errors" (errors = []);
  let kept, audit = EP.apply policy ~file:"doc.tex" (sample ()) in
  check "disable: SPC-016 vanishes" (not (List.mem "SPC-016" (ids kept)));
  check "disable: others remain"
    (List.mem "TYPO-001" (ids kept) && List.mem "DELIM-009" (ids kept));
  check "disable: no audit records (not a waiver)" (audit = []);

  (* enable overrides a disable for the same id *)
  let { EP.policy; _ } = policy_of_string "disable SPC-016\nenable SPC-016\n" in
  let kept, _ = EP.apply policy ~file:"doc.tex" (sample ()) in
  check "enable overrides disable" (List.mem "SPC-016" (ids kept));

  (* ── 2. severity override ─────────────────────────────────────────── *)
  let { EP.policy; errors } =
    policy_of_string "severity TYPO-001 error\nseverity DELIM-009 info\n"
  in
  check "severity: no parse errors" (errors = []);
  let kept, _ = EP.apply policy ~file:"doc.tex" (sample ()) in
  check "severity: TYPO-001 Warning→Error"
    (sev_of kept "TYPO-001" = Some VC.Error);
  check "severity: untouched rule keeps its severity"
    (sev_of kept "SPC-016" = Some VC.Warning);

  (* bad severity level is an error, not a crash *)
  let { EP.errors; _ } = policy_of_string "severity TYPO-001 bogus\n" in
  check "severity: bad level reported as error" (errors <> []);

  (* ── 3. scoped waiver: suppress + audit ───────────────────────────── *)
  let { EP.policy; errors } =
    policy_of_string
      "waive SPC-016 file=*.tex reason=\"template spacing, approved\"\n"
  in
  check "waiver: no parse errors" (errors = []);
  let kept, audit = EP.apply policy ~file:"chapters/doc.tex" (sample ()) in
  check "waiver: SPC-016 suppressed on matching file"
    (not (List.mem "SPC-016" (ids kept)));
  check "waiver: other findings survive"
    (List.mem "TYPO-001" (ids kept) && List.mem "DELIM-009" (ids kept));
  check "waiver: exactly one audit record" (List.length audit = 1);
  (match audit with
  | [ a ] ->
      check "waiver audit: rule id" (a.EP.a_rule = "SPC-016");
      check "waiver audit: reason recorded"
        (a.EP.a_reason = "template spacing, approved");
      check "waiver audit: count carried" (a.EP.a_count = 1);
      check "waiver audit: scope string mentions the glob"
        (a.EP.a_scope = "file=*.tex");
      check "waiver audit: renders as WAIVED line"
        (let s = EP.audit_record_to_string a in
         String.length s > 6 && String.sub s 0 6 = "WAIVED")
  | _ -> check "waiver audit: exactly one record" false);

  (* scoped waiver that does NOT match the file → no suppression, no audit *)
  let { EP.policy; _ } =
    policy_of_string
      "waive SPC-016 file=other/*.tex reason=\"only for other/\"\n"
  in
  let kept, audit = EP.apply policy ~file:"chapters/doc.tex" (sample ()) in
  check "waiver: non-matching glob does NOT suppress"
    (List.mem "SPC-016" (ids kept));
  check "waiver: non-matching glob emits no audit" (audit = []);

  (* a waive without a reason= is rejected (accountability) *)
  let { EP.policy; errors } = policy_of_string "waive SPC-016 file=*.tex\n" in
  check "waiver: missing reason is a parse error" (errors <> []);
  check "waiver: missing reason produces no waiver" (policy.EP.waivers = []);

  (* ── 4. empty policy = unchanged output ───────────────────────────── *)
  let src = sample () in
  let kept, audit = EP.apply EP.empty ~file:"doc.tex" src in
  check "empty policy: ids unchanged" (ids kept = ids src);
  check "empty policy: severities unchanged"
    (List.for_all2
       (fun (a : VC.result) (b : VC.result) -> a.VC.severity = b.VC.severity)
       kept src);
  check "empty policy: no audit records" (audit = []);

  (* ── loading a missing file is total ──────────────────────────────── *)
  let { EP.policy; errors } = EP.load "/no/such/policy.lppolicy" in
  check "load: missing file does not crash"
    (errors <> [] && policy.EP.name = "(none)");

  if !failures = 0 then printf "\nAll editorial_policy tests passed.\n"
  else (
    printf "\n%d editorial_policy test(s) FAILED.\n" !failures;
    exit 1)
