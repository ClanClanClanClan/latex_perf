(** Tests for PR #236 language contract (memo §4).

    Exercises tier classification on the fixture corpus and verifies that
    [Language_profile.classify_source] agrees with the specification. *)

open Latex_parse_lib
open Test_helpers

(* Locate repo root (same pattern as test_build_log_integration). *)
let repo_root =
  let exe_dir = Filename.dirname Sys.argv.(0) in
  let candidates =
    [
      Filename.concat exe_dir "../..";
      ".";
      Filename.concat exe_dir "../../..";
      Filename.concat exe_dir "../../../..";
    ]
  in
  try
    List.find
      (fun d ->
        Sys.file_exists
          (Filename.concat d "corpora/lint/language_profile/lp_core.tex"))
      candidates
  with Not_found -> "."

let read_fixture name =
  let path =
    Filename.concat repo_root
      (Filename.concat "corpora/lint/language_profile" name)
  in
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let tier_to_s = Language_profile.tier_to_string

let () =
  (* 1. LP-Core fixture classifies as LP_Core, no features. *)
  run "lp_core fixture classifies as LP_Core" (fun tag ->
      let src = read_fixture "lp_core.tex" in
      let tier, features = Language_profile.classify_source src in
      expect
        (tier = Language_profile.LP_Core)
        (tag ^ ": tier = " ^ tier_to_s tier);
      expect (features = [])
        (tag ^ ": " ^ string_of_int (List.length features) ^ " features"));

  (* 2. LP-Extended fixture classifies as LP_Extended with at least one
     forbidden-in-core feature. *)
  run "lp_extended fixture classifies as LP_Extended" (fun tag ->
      let src = read_fixture "lp_extended.tex" in
      let tier, features = Language_profile.classify_source src in
      expect
        (tier = Language_profile.LP_Extended)
        (tag ^ ": tier = " ^ tier_to_s tier);
      expect
        (List.length features >= 1)
        (tag ^ ": " ^ string_of_int (List.length features) ^ " features");
      expect
        (List.for_all
           (fun (f : Unsupported_feature.t) ->
             f.severity = Unsupported_feature.Forbidden_in_core)
           features)
        (tag ^ ": all features are Forbidden_in_core"));

  (* 3. LP-Foreign fixture classifies as LP_Foreign with at least one foreign
     trigger. *)
  run "lp_foreign fixture classifies as LP_Foreign" (fun tag ->
      let src = read_fixture "lp_foreign.tex" in
      let tier, features = Language_profile.classify_source src in
      expect
        (tier = Language_profile.LP_Foreign)
        (tag ^ ": tier = " ^ tier_to_s tier);
      expect
        (List.length features >= 1)
        (tag ^ ": " ^ string_of_int (List.length features) ^ " features");
      expect
        (List.for_all
           (fun (f : Unsupported_feature.t) ->
             f.severity = Unsupported_feature.Foreign_trigger)
           features)
        (tag ^ ": all features are Foreign_trigger"));

  (* 4. Totality: empty source → LP_Core with no features. *)
  run "empty source classifies as LP_Core" (fun tag ->
      let tier, features = Language_profile.classify_source "" in
      expect
        (tier = Language_profile.LP_Core)
        (tag ^ ": tier = " ^ tier_to_s tier);
      expect (features = []) (tag ^ ": no features"));

  (* 5. Foreign trigger dominates forbidden-in-core: document with both \def and
     \write18 classifies as LP_Foreign, not LP_Extended. *)
  run "foreign trigger dominates forbidden_in_core" (fun tag ->
      let src =
        "\\documentclass{article}\n\
         \\def\\x{y}\n\
         \\write18{echo hi}\n\
         \\begin{document}\\end{document}\n"
      in
      let tier, _ = Language_profile.classify_source src in
      expect
        (tier = Language_profile.LP_Foreign)
        (tag ^ ": tier = " ^ tier_to_s tier));

  (* 6. tier_of_string round-trip. *)
  run "tier_of_string round-trip" (fun tag ->
      let all =
        [
          Language_profile.LP_Core;
          Language_profile.LP_Extended;
          Language_profile.LP_Foreign;
        ]
      in
      List.iter
        (fun t ->
          let s = tier_to_s t in
          match Language_profile.tier_of_string s with
          | Some t' -> expect (t' = t) (tag ^ ": " ^ s ^ " round-trips")
          | None -> expect false (tag ^ ": failed to parse " ^ s))
        all);

  (* 7. tier_is_at_least is a partial order (LP_Core strongest). *)
  run "tier_is_at_least ordering" (fun tag ->
      expect
        (Language_profile.tier_is_at_least Language_profile.LP_Core
           Language_profile.LP_Extended)
        (tag ^ ": Core >= Extended");
      expect
        (Language_profile.tier_is_at_least Language_profile.LP_Extended
           Language_profile.LP_Foreign)
        (tag ^ ": Extended >= Foreign");
      expect
        (not
           (Language_profile.tier_is_at_least Language_profile.LP_Foreign
              Language_profile.LP_Core))
        (tag ^ ": Foreign not >= Core"));

  (* 8. Context set/get/clear. *)
  run "Context set/get/clear" (fun tag ->
      Language_profile.Context.clear ();
      expect
        (Language_profile.Context.get () = None)
        (tag ^ ": empty context returns None");
      Language_profile.Context.set Language_profile.LP_Extended;
      expect
        (Language_profile.Context.get () = Some Language_profile.LP_Extended)
        (tag ^ ": set and get LP_Extended");
      Language_profile.Context.clear ();
      expect
        (Language_profile.Context.get () = None)
        (tag ^ ": after clear returns None"));

  finalise "language_profile"
