(** PR #241 (p1.2, memo §4): verify that [Language_profile.Context] actually
    gates which rules fire. Previously [project_scope] was documented but never
    read; this test pins the runtime behaviour. *)

open Latex_parse_lib
open Test_helpers

let sample_tex =
  "\\documentclass{article}\n\
   \\begin{document}\n\
   This is a sentence with--double-hyphen and \"quotes\".\n\
   \\end{document}\n"

let count_results src = List.length (Validators.run_all src)

let () =
  (* Enable pilot validators so the TYPO family is loaded. *)
  Unix.putenv "L0_VALIDATORS" "pilot";
  (* 1. No profile set → baseline rule count. *)
  run "no profile ⇒ baseline" (fun tag ->
      Language_profile.Context.clear ();
      let n = count_results sample_tex in
      expect (n >= 1)
        (tag ^ ": baseline produced " ^ string_of_int n ^ " results"));

  (* 2. LP_Core profile ⇒ same count as baseline (lp_core_or_extended rules
     still fire). *)
  run "LP_Core ⇒ all rules fire" (fun tag ->
      Language_profile.Context.clear ();
      let baseline = count_results sample_tex in
      Language_profile.Context.set Language_profile.LP_Core;
      let with_core = count_results sample_tex in
      Language_profile.Context.clear ();
      expect (with_core = baseline)
        (tag
        ^ ": LP_Core count ("
        ^ string_of_int with_core
        ^ ") = baseline ("
        ^ string_of_int baseline
        ^ ")"));

  (* 3. LP_Foreign profile ⇒ strictly fewer rules fire (lp_core_or_extended
     rules are skipped; only Any_tier rules run). *)
  run "LP_Foreign ⇒ fewer rules fire" (fun tag ->
      Language_profile.Context.clear ();
      let baseline = count_results sample_tex in
      Language_profile.Context.set Language_profile.LP_Foreign;
      let with_foreign = count_results sample_tex in
      Language_profile.Context.clear ();
      expect (with_foreign < baseline)
        (tag
        ^ ": LP_Foreign count ("
        ^ string_of_int with_foreign
        ^ ") < baseline ("
        ^ string_of_int baseline
        ^ ")"));

  (* 4. Every rule in rules_class_c has Any_tier scope — log-dependent rules
     must fire across all tiers. *)
  run "Class C rules have Any_tier scope" (fun tag ->
      List.iter
        (fun (r : Validators.rule) ->
          match Rule_contract_loader.find_opt r.id with
          | Some c ->
              expect
                (c.project_scope = Rule_contract_loader.Any_tier)
                (tag ^ ": " ^ r.id ^ " should have Any_tier scope")
          | None -> expect false (tag ^ ": " ^ r.id ^ " missing from contracts"))
        Validators.rules_class_c);

  (* 5. PR #241 (p1.3): per-rule assertions. Counts alone don't prove the right
     rules got filtered. Lock down specific IDs: - A core TYPO rule
     (project_scope = lp_core_or_extended) must fire under LP_Core and NOT under
     LP_Foreign. - The build-log class-C rules (project_scope = any) must be
     AVAILABLE in every profile (they don't fire without a log but must be
     registered). *)
  let rule_ids src =
    List.map (fun (r : Validators.result) -> r.id) (Validators.run_all src)
  in
  let typo_triggering_src =
    "\\documentclass{article}\n\
     \\begin{document}\n\
     This is a long sentence with--double-hyphen that fires TYPO-002.\n\
     \\end{document}\n"
  in
  run "LP_Core fires TYPO-002 on double hyphen" (fun tag ->
      Language_profile.Context.clear ();
      Language_profile.Context.set Language_profile.LP_Core;
      let ids = rule_ids typo_triggering_src in
      Language_profile.Context.clear ();
      expect (List.mem "TYPO-002" ids) (tag ^ ": TYPO-002 present under LP_Core"));
  run "LP_Foreign suppresses TYPO-002" (fun tag ->
      Language_profile.Context.clear ();
      Language_profile.Context.set Language_profile.LP_Foreign;
      let ids = rule_ids typo_triggering_src in
      Language_profile.Context.clear ();
      expect
        (not (List.mem "TYPO-002" ids))
        (tag ^ ": TYPO-002 absent under LP_Foreign"));

  (* 6. No lp_core_or_extended rule may appear in run_all output under
     LP_Foreign — any leak is a tier-gating bug. *)
  run "LP_Foreign run_all yields no lp_core_or_extended rule" (fun tag ->
      Language_profile.Context.clear ();
      Language_profile.Context.set Language_profile.LP_Foreign;
      let ids = rule_ids typo_triggering_src in
      Language_profile.Context.clear ();
      let leaked =
        List.filter
          (fun id ->
            match Rule_contract_loader.find_opt id with
            | Some c ->
                c.project_scope = Rule_contract_loader.Lp_core_or_extended
            | None -> false)
          ids
      in
      expect (leaked = [])
        (tag
        ^ ": "
        ^ string_of_int (List.length leaked)
        ^ " lp_core_or_extended rule(s) fired under LP_Foreign: "
        ^ String.concat "," leaked));

  finalise "tier_gating"
