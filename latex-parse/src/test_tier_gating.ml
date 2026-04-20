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

  finalise "tier_gating"
