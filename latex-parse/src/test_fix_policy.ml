(** Unit tests for {!Latex_parse_lib.Fix_policy} — the default fixer's
    allow-list (OPEN-105, OPEN-110, OPEN-112).

    The allow-list is a claim that each listed rule's fix is safe on real
    papers. These tests cannot check that claim; they check the structural
    invariants that keep it honest. No id may appear twice. No rule measured in
    a break repair set may be in the default set, which is the tripwire. Every
    allow-listed id must be a real rule that actually produces a fix, both in
    the contract registry that [check_producer_coverage.py] reads and in the
    rule set the engine registers at runtime. *)

open Latex_parse_lib
open Test_helpers

let contracts_path () =
  let candidates =
    [
      "specs/rules/rule_contracts.json";
      "../../specs/rules/rule_contracts.json";
      "../../../specs/rules/rule_contracts.json";
    ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some p -> p
  | None ->
      Printf.eprintf "[fix-policy] FATAL: rule_contracts.json not found\n";
      exit 1

(* rule_id -> produces_fix, from the JSON mirror of the contract registry. *)
let contracts () =
  let open Yojson.Safe.Util in
  Yojson.Safe.from_file (contracts_path ())
  |> member "rules"
  |> to_list
  |> List.map (fun r ->
         ( r |> member "rule_id" |> to_string,
           match r |> member "produces_fix" with `Bool b -> b | _ -> false ))

let has_dup xs =
  let sorted = List.sort compare xs in
  let rec go = function a :: (b :: _ as tl) -> a = b || go tl | _ -> false in
  go sorted

let () =
  Unix.putenv "L0_VALIDATORS" "";
  run "default_allowlist has no duplicates" (fun tag ->
      expect (not (has_dup Fix_policy.default_allowlist)) tag);

  run "implicated has no duplicates and names 24 rules" (fun tag ->
      expect (not (has_dup Fix_policy.implicated)) (tag ^ ": no duplicates");
      expect
        (List.length Fix_policy.implicated = 24)
        (tag ^ ": 24 implicated rules"));

  (* The tripwire: a rule ever measured in a break repair set may never be
     applied by default. *)
  run "default_allowlist and implicated are disjoint" (fun tag ->
      let both =
        List.filter
          (fun id -> List.mem id Fix_policy.implicated)
          Fix_policy.default_allowlist
      in
      expect (both = []) (tag ^ ": overlap = " ^ String.concat "," both));

  run "in_default_set agrees with default_allowlist" (fun tag ->
      List.iter
        (fun id -> expect (Fix_policy.in_default_set id) (tag ^ ": " ^ id))
        Fix_policy.default_allowlist;
      List.iter
        (fun id ->
          expect (not (Fix_policy.in_default_set id)) (tag ^ ": not " ^ id))
        Fix_policy.implicated;
      expect (not (Fix_policy.in_default_set "")) (tag ^ ": not empty id"));

  let registry = contracts () in
  run "every allow-listed id is a registered fix producer" (fun tag ->
      List.iter
        (fun id ->
          match List.assoc_opt id registry with
          | Some true -> ()
          | Some false ->
              expect false (tag ^ ": " ^ id ^ " has produces_fix false")
          | None -> expect false (tag ^ ": " ^ id ^ " is not a known rule id"))
        Fix_policy.default_allowlist);

  run "every implicated id is a registered fix producer" (fun tag ->
      List.iter
        (fun id ->
          expect
            (List.assoc_opt id registry = Some true)
            (tag ^ ": " ^ id ^ " is a known fix producer"))
        Fix_policy.implicated);

  run "every allow-listed id is registered in the default rule set" (fun tag ->
      let ids =
        List.map (fun (r : Validators.rule) -> r.id) (Validators.get_rules ())
      in
      List.iter
        (fun id ->
          expect (List.mem id ids) (tag ^ ": " ^ id ^ " is registered"))
        Fix_policy.default_allowlist);

  finalise "fix-policy"
