(** Conflict tests: deterministic ordering when multiple VPD-catalogue
    validators fire on the same input text.

    These tests verify: 1. Multi-rule inputs produce results in deterministic
    order. 2. Severity ordering: Error > Warning > Info within a single run. 3.
    No duplicate rule IDs appear in a single run. 4. VPD catalogue coverage
    matches the expected count (80). *)

open Latex_parse_lib
open Test_helpers

let result_ids results = List.map (fun (r : Validators.result) -> r.id) results

let severity_rank sev =
  match sev with
  | Validators.Error -> 0
  | Validators.Warning -> 1
  | Validators.Info -> 2

(* Enable TYPO rules for the test run *)
let () = Unix.putenv "L0_VALIDATORS" "pilot"

(* ══════════════════════════════════════════════════════════════════════ §1
   Deterministic ordering — same input always yields same ID list
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* Run the same input 5 times and verify the result list is identical *)
  let src = "He said \"hello\" and used -- to separate items.  " in
  (* This input should trigger at least TYPO-001 (straight quotes) and TYPO-002
     (double hyphen). The trailing spaces at end of line may trigger TYPO-007 if
     interpreted as trailing whitespace. *)
  let baseline = result_ids (Validators.run_all src) in
  for i = 1 to 4 do
    let repeat = result_ids (Validators.run_all src) in
    run (Printf.sprintf "deterministic ordering pass %d" i) (fun tag ->
        expect (baseline = repeat) (tag ^ ": result order changed between runs"))
  done

(* ══════════════════════════════════════════════════════════════════════ §2
   Multi-rule fire — straight quotes + double hyphen
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  let src = "He said \"hello\" and used -- for a dash." in
  let results = Validators.run_all src in
  let ids = result_ids results in
  run "TYPO-001 fires on straight quotes" (fun tag ->
      expect (List.mem "TYPO-001" ids) (tag ^ ": TYPO-001 missing"));
  run "TYPO-002 fires on double hyphen" (fun tag ->
      expect (List.mem "TYPO-002" ids) (tag ^ ": TYPO-002 missing"))

(* ══════════════════════════════════════════════════════════════════════ §3 No
   duplicate rule IDs in a single run
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* A rich input that fires many rules *)
  let src =
    "He said \"hello\" and used -- for a dash.  \n\
     Also ... instead of \\ldots.\n\
     And e.g. without a backslash.\n"
  in
  let results = Validators.run_all src in
  let ids = result_ids results in
  let unique_ids = List.sort_uniq String.compare ids in
  run "no duplicate rule IDs" (fun tag ->
      expect
        (List.length ids = List.length unique_ids)
        (tag
        ^ Printf.sprintf ": found %d results but only %d unique IDs"
            (List.length ids) (List.length unique_ids)))

(* ══════════════════════════════════════════════════════════════════════ §4
   Severity ordering within family — Error before Warning before Info
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* Check that when we partition results by family prefix, within each family
     the severities are non-decreasing (Error <= Warning <= Info). *)
  let src =
    "He said \"hello\" and used -- for a dash.  \n\
     Also x---y is triple hyphen.  \n\
     12-point and 3--4 range.  \n"
  in
  let results = Validators.run_all src in
  (* Group results by 4-char prefix (e.g. "TYPO") *)
  let prefix_of id =
    try String.sub id 0 4 with Invalid_argument _ -> id
  in
  let families =
    List.sort_uniq String.compare
      (List.map (fun (r : Validators.result) -> prefix_of r.id) results)
  in
  List.iter
    (fun fam ->
      let fam_results =
        List.filter
          (fun (r : Validators.result) -> prefix_of r.id = fam)
          results
      in
      let ranks =
        List.map
          (fun (r : Validators.result) -> severity_rank r.severity)
          fam_results
      in
      (* Check non-decreasing *)
      let rec check_order = function
        | [] | [ _ ] -> true
        | a :: (b :: _ as rest) -> a <= b && check_order rest
      in
      run (Printf.sprintf "severity ordering within %s family" fam) (fun tag ->
          expect (check_order ranks)
            (tag ^ ": severity ordering violated in " ^ fam)))
    families

(* ══════════════════════════════════════════════════════════════════════ §5
   Cross-family multi-fire — TYPO + ENC rules
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* Input with both typographic and encoding issues. U+200B = zero-width space
     triggers ENC-007. Straight quotes for TYPO-001. *)
  let src = "He said \"hello\" with\xe2\x80\x8ba zero-width space." in
  let results = Validators.run_all src in
  let ids = result_ids results in
  let has_typo =
    List.exists
      (fun id -> String.length id >= 4 && String.sub id 0 4 = "TYPO")
      ids
  in
  let has_enc =
    List.exists
      (fun id -> String.length id >= 3 && String.sub id 0 3 = "ENC")
      ids
  in
  run "cross-family: TYPO rule fires" (fun tag ->
      expect has_typo (tag ^ ": expected at least one TYPO rule to fire"));
  run "cross-family: ENC rule fires" (fun tag ->
      expect has_enc (tag ^ ": expected at least one ENC rule to fire"))

(* ══════════════════════════════════════════════════════════════════════ §6 VPD
   catalogue count = 80
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  run "vpd_catalogue_count = 80" (fun tag ->
      expect
        (Validators.vpd_catalogue_count = 80)
        (tag
        ^ Printf.sprintf ": expected 80, got %d" Validators.vpd_catalogue_count
        ));

  (* Also verify rules_vpd_catalogue has the right length *)
  let actual_len = List.length Validators.rules_vpd_catalogue in
  run "rules_vpd_catalogue length = 80" (fun tag ->
      expect (actual_len = 80)
        (tag ^ Printf.sprintf ": expected 80 rules, got %d" actual_len))

(* ══════════════════════════════════════════════════════════════════════ §7
   Catalogue rule IDs are unique
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  let ids =
    List.map (fun (r : Validators.rule) -> r.id) Validators.rules_vpd_catalogue
  in
  let unique_ids = List.sort_uniq String.compare ids in
  run "catalogue rule IDs are unique" (fun tag ->
      expect
        (List.length ids = List.length unique_ids)
        (tag
        ^ Printf.sprintf ": %d rules but only %d unique IDs" (List.length ids)
            (List.length unique_ids)))

(* ══════════════════════════════════════════════════════════════════════ §8
   Stability under repeated catalogue traversal
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  let ids1 =
    List.map (fun (r : Validators.rule) -> r.id) Validators.rules_vpd_catalogue
  in
  let ids2 =
    List.map (fun (r : Validators.rule) -> r.id) Validators.rules_vpd_catalogue
  in
  run "catalogue traversal is stable" (fun tag ->
      expect (ids1 = ids2) (tag ^ ": catalogue changed between reads"))

(* ══════════════════════════════════════════════════════════════════════ §9
   Clean input triggers no TYPO rules
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  let src = "This is a clean sentence with no issues." in
  let results = Validators.run_all src in
  let typo_results =
    List.filter
      (fun (r : Validators.result) ->
        String.length r.id >= 4 && String.sub r.id 0 4 = "TYPO")
      results
  in
  run "clean input: no TYPO rules fire" (fun tag ->
      expect (typo_results = [])
        (tag
        ^ Printf.sprintf ": %d TYPO rules fired unexpectedly"
            (List.length typo_results)))

(* ══════════════════════════════════════════════════════════════════════ §10
   Clean input triggers no ENC rules
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* Pure ASCII, valid UTF-8, no encoding anomalies *)
  let src = "A perfectly normal paragraph with ASCII text only." in
  let results = Validators.run_all src in
  let enc_results =
    List.filter
      (fun (r : Validators.result) ->
        String.length r.id >= 3 && String.sub r.id 0 3 = "ENC")
      results
  in
  run "clean input: no ENC rules fire" (fun tag ->
      expect (enc_results = [])
        (tag
        ^ Printf.sprintf ": %d ENC rules fired unexpectedly"
            (List.length enc_results)))

(* ══════════════════════════════════════════════════════════════════════ §11
   Properly escaped LaTeX triggers no escaping rules
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* Well-formed LaTeX with no special characters *)
  let src = "This is a simple LaTeX document with no issues at all." in
  let results = Validators.run_all src in
  let typo_results =
    List.filter
      (fun (r : Validators.result) ->
        String.length r.id >= 4 && String.sub r.id 0 4 = "TYPO")
      results
  in
  run "escaped LaTeX: no TYPO rules fire" (fun tag ->
      expect (typo_results = [])
        (tag
        ^ Printf.sprintf ": %d TYPO rules fired on clean LaTeX"
            (List.length typo_results)))

(* ══════════════════════════════════════════════════════════════════════ §12
   Deferred rules never fire
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* TYPO-019, -020, -030, -031 are NLP stubs returning None *)
  let src =
    "He went to the store, he bought some milk.\n\
     I can not believe it\n\
     The colour of the aeroplane was grey.\n"
  in
  let results = Validators.run_all src in
  let deferred = [ "TYPO-019"; "TYPO-020"; "TYPO-030"; "TYPO-031" ] in
  List.iter
    (fun did ->
      let fired =
        List.exists (fun (r : Validators.result) -> r.id = did) results
      in
      run (Printf.sprintf "deferred %s does not fire" did) (fun tag ->
          expect (not fired) (tag ^ ": " ^ did ^ " should never fire")))
    deferred

(* ══════════════════════════════════════════════════════════════════════ §13
   Triple-fire input — at least 3 different rules
   ══════════════════════════════════════════════════════════════════════ *)

let () =
  (* Straight quotes + double hyphen + triple dots *)
  let src = "\"Hello\" -- he said... goodbye." in
  let results = Validators.run_all src in
  let ids = result_ids results in
  let unique_ids = List.sort_uniq String.compare ids in
  run "triple-fire: at least 3 rules" (fun tag ->
      expect
        (List.length unique_ids >= 3)
        (tag
        ^ Printf.sprintf ": only %d unique rules fired, expected >= 3"
            (List.length unique_ids)))

let () = finalise "conflict"
