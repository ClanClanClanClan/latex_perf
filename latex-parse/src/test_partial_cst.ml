(** Tests for WS5 partial document semantics. *)

open Latex_parse_lib
open Test_helpers

let mk_loc offset = { Parser_l2.line = 1; col = offset; offset }

let () =
  (* ── classify tests ────────────────────────────────────────────── *)
  run "no errors: Complete" (fun tag ->
      let pd = Partial_cst.classify "Hello world.\n\nSecond para." [] in
      expect (pd.confidence = Partial_cst.Complete) (tag ^ ": complete"));

  run "one error: Broken" (fun tag ->
      let src = "First paragraph.\n\nBroken {{{ here.\n\nThird paragraph." in
      let errors = [ ("Unclosed brace", mk_loc 25) ] in
      let pd = Partial_cst.classify src errors in
      expect (pd.confidence = Partial_cst.Broken) (tag ^ ": broken"));

  run "trust zones created" (fun tag ->
      let src = "Good para one.\n\nBad para {.\n\nGood para three." in
      let errors = [ ("Unclosed brace", mk_loc 20) ] in
      let pd = Partial_cst.classify src errors in
      expect (List.length pd.trust_zones >= 2) (tag ^ ": >= 2 zones"));

  run "error-free zones are Complete" (fun tag ->
      let src = "Good first.\n\nBroken {{.\n\nGood third." in
      let errors = [ ("Unclosed brace", mk_loc 18) ] in
      let pd = Partial_cst.classify src errors in
      let complete_zones =
        List.filter
          (fun z ->
            (z : Partial_cst.trust_zone).confidence = Partial_cst.Complete)
          pd.trust_zones
      in
      expect (complete_zones <> []) (tag ^ ": has Complete zones"));

  run "error zone is Broken" (fun tag ->
      let src = "Good first.\n\nBroken {{.\n\nGood third." in
      let errors = [ ("Unclosed brace", mk_loc 18) ] in
      let pd = Partial_cst.classify src errors in
      let broken_zones =
        List.filter
          (fun z ->
            (z : Partial_cst.trust_zone).confidence = Partial_cst.Broken)
          pd.trust_zones
      in
      expect (broken_zones <> []) (tag ^ ": has Broken zone"));

  run "holes match errors" (fun tag ->
      let errors = [ ("Error A", mk_loc 5); ("Error B", mk_loc 30) ] in
      let pd =
        Partial_cst.classify "Some text here.\n\nMore text there." errors
      in
      expect (List.length pd.holes = 2) (tag ^ ": 2 holes"));

  run "empty source: Complete" (fun tag ->
      let pd = Partial_cst.classify "" [] in
      expect (pd.confidence = Partial_cst.Complete) (tag ^ ": complete"));

  run "single paragraph all broken" (fun tag ->
      let pd =
        Partial_cst.classify "all one paragraph" [ ("Error", mk_loc 5) ]
      in
      expect (pd.confidence = Partial_cst.Broken) (tag ^ ": broken"));

  (* ── damage_radius tests ───────────────────────────────────────── *)
  run "damage_radius: error in second paragraph" (fun tag ->
      let src = "First paragraph.\n\nSecond paragraph.\n\nThird paragraph." in
      let start, end_ = Partial_cst.damage_radius ~error_pos:25 src in
      expect (start <= 25 && end_ >= 25) (tag ^ ": contains error pos");
      expect (start > 0) (tag ^ ": doesn't start at 0");
      expect (end_ < String.length src) (tag ^ ": doesn't cover all"));

  run "damage_radius: error at start" (fun tag ->
      let src = "Bad start.\n\nGood second." in
      let start, _ = Partial_cst.damage_radius ~error_pos:0 src in
      expect (start = 0) (tag ^ ": starts at 0"));

  (* ── confidence_to_string tests ────────────────────────────────── *)
  run "confidence_to_string" (fun tag ->
      expect
        (Partial_cst.confidence_to_string Complete = "complete")
        (tag ^ ": complete");
      expect
        (Partial_cst.confidence_to_string Partial = "partial")
        (tag ^ ": partial");
      expect
        (Partial_cst.confidence_to_string Broken = "broken")
        (tag ^ ": broken"));

  (* ── error_recovery tests ──────────────────────────────────────── *)
  run "find_recovery_points: paragraph break" (fun tag ->
      let src = "Error here.\n\nRecovery point." in
      let points = Error_recovery.find_recovery_points src 5 in
      expect (points <> []) (tag ^ ": found points");
      expect
        (List.exists (fun p -> p.Error_recovery.kind = "paragraph") points)
        (tag ^ ": paragraph break"));

  run "find_recovery_points: section command" (fun tag ->
      let src = "Error.\n\\section{Recovery}" in
      let points = Error_recovery.find_recovery_points src 3 in
      expect
        (List.exists (fun p -> p.Error_recovery.kind = "section") points)
        (tag ^ ": section"));

  run "is_repaired: fewer errors" (fun tag ->
      let old_errors = [ ("A", mk_loc 5); ("B", mk_loc 10) ] in
      let new_errors = [ ("A", mk_loc 5) ] in
      expect
        (Error_recovery.is_repaired ~old_errors ~new_errors)
        (tag ^ ": repaired"));

  run "is_repaired: same errors" (fun tag ->
      let errors = [ ("A", mk_loc 5) ] in
      expect
        (not (Error_recovery.is_repaired ~old_errors:errors ~new_errors:errors))
        (tag ^ ": not repaired"));

  run "is_repaired: more errors" (fun tag ->
      let old_errors = [ ("A", mk_loc 5) ] in
      let new_errors = [ ("A", mk_loc 5); ("B", mk_loc 10) ] in
      expect
        (not (Error_recovery.is_repaired ~old_errors ~new_errors))
        (tag ^ ": not repaired"));

  (* ── partial_context tests ─────────────────────────────────────── *)
  run "partial_context: set/get/clear" (fun tag ->
      let pd = Partial_cst.classify "test" [] in
      Partial_context.set pd;
      let has = Partial_context.get () <> None in
      Partial_context.clear ();
      let no = Partial_context.get () = None in
      expect has (tag ^ ": set");
      expect no (tag ^ ": cleared"));

  (* ── PRT validator tests ───────────────────────────────────────── *)
  run "PRT-001 fires on Broken document" (fun tag ->
      let pd =
        Partial_cst.classify "broken {{" [ ("Unclosed brace", mk_loc 7) ]
      in
      Partial_context.set pd;
      Fun.protect ~finally:Partial_context.clear (fun () ->
          let src = "broken {{ " ^ string_of_int (Random.int 999999) in
          let results = Validators.run_all src in
          let has_prt =
            List.exists
              (fun (r : Validators.result) -> r.id = "PRT-001")
              results
          in
          expect has_prt (tag ^ ": PRT-001 fires")));

  run "PRT-001 silent on Complete document" (fun tag ->
      let pd = Partial_cst.classify "good document" [] in
      Partial_context.set pd;
      Fun.protect ~finally:Partial_context.clear (fun () ->
          let src = "good document " ^ string_of_int (Random.int 999999) in
          let results = Validators.run_all src in
          let has_prt =
            List.exists
              (fun (r : Validators.result) -> r.id = "PRT-001")
              results
          in
          expect (not has_prt) (tag ^ ": PRT-001 silent")));

  run "PRT-001 silent without context" (fun tag ->
      Partial_context.clear ();
      let src = "no context " ^ string_of_int (Random.int 999999) in
      let results = Validators.run_all src in
      let has_prt =
        List.exists (fun (r : Validators.result) -> r.id = "PRT-001") results
      in
      expect (not has_prt) (tag ^ ": PRT-001 silent"))

let () = finalise "partial-cst"
