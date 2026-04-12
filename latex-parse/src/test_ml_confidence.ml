(** Test ML confidence integration. 10+ cases. *)

open Latex_parse_lib
open Test_helpers

let write_temp_json content =
  let path = Filename.temp_file "ml_conf_" ".json" in
  let oc = open_out path in
  output_string oc content;
  close_out oc;
  path

let () =
  (* ── load_ml_confidence_map ─────────────────────────────────── *)
  run "load valid JSON" (fun tag ->
      let path =
        write_temp_json
          {|{"TYPO-012": {"precision": 0.0, "weight": 0.0, "suppress": true},
             "TYPO-052": {"precision": 0.97, "weight": 0.97, "suppress": false}}|}
      in
      Fun.protect
        ~finally:(fun () -> Sys.remove path)
        (fun () ->
          let map = Evidence_scoring.load_ml_confidence_map path in
          expect (Hashtbl.length map = 2) (tag ^ ": 2 entries");
          match Hashtbl.find_opt map "TYPO-012" with
          | Some c ->
              expect c.suppress (tag ^ ": TYPO-012 suppressed");
              expect (c.weight = 0.0) (tag ^ ": weight=0")
          | None -> expect false (tag ^ ": TYPO-012 missing")));

  run "load missing file returns empty" (fun tag ->
      let map =
        Evidence_scoring.load_ml_confidence_map "/nonexistent/path.json"
      in
      expect (Hashtbl.length map = 0) (tag ^ ": empty"));

  run "load malformed JSON returns empty" (fun tag ->
      let path = write_temp_json "not json at all" in
      Fun.protect
        ~finally:(fun () -> Sys.remove path)
        (fun () ->
          let map = Evidence_scoring.load_ml_confidence_map path in
          expect (Hashtbl.length map = 0) (tag ^ ": empty on bad JSON")));

  run "load empty object returns empty" (fun tag ->
      let path = write_temp_json "{}" in
      Fun.protect
        ~finally:(fun () -> Sys.remove path)
        (fun () ->
          let map = Evidence_scoring.load_ml_confidence_map path in
          expect (Hashtbl.length map = 0) (tag ^ ": empty")));

  (* ── apply_ml_boost ─────────────────────────────────────────── *)
  let mk_scored id weight =
    {
      Evidence_scoring.id;
      severity = Validators_common.Info;
      message = "test";
      count = 1;
      confidence = Evidence_scoring.High;
      evidence_weight = weight;
    }
  in

  run "apply_ml_boost: suppress=true drops result" (fun tag ->
      let map = Hashtbl.create 4 in
      Hashtbl.replace map "TYPO-012"
        { Evidence_scoring.precision = 0.0; weight = 0.0; suppress = true };
      let results = [ mk_scored "TYPO-012" 1.0; mk_scored "TYPO-001" 1.0 ] in
      let boosted = Evidence_scoring.apply_ml_boost map results in
      expect (List.length boosted = 1) (tag ^ ": 1 result");
      expect ((List.hd boosted).id = "TYPO-001") (tag ^ ": kept TYPO-001"));

  run "apply_ml_boost: weight reduction" (fun tag ->
      let map = Hashtbl.create 4 in
      Hashtbl.replace map "TYPO-052"
        { Evidence_scoring.precision = 0.97; weight = 0.5; suppress = false };
      let results = [ mk_scored "TYPO-052" 1.0 ] in
      let boosted = Evidence_scoring.apply_ml_boost map results in
      expect (List.length boosted = 1) (tag ^ ": kept");
      let w = (List.hd boosted).evidence_weight in
      expect (w > 0.49 && w < 0.51) (tag ^ ": weight ~0.5"));

  run "apply_ml_boost: rule not in map unchanged" (fun tag ->
      let map = Hashtbl.create 4 in
      Hashtbl.replace map "TYPO-012"
        { Evidence_scoring.precision = 0.0; weight = 0.0; suppress = true };
      let results = [ mk_scored "ENC-001" 0.8 ] in
      let boosted = Evidence_scoring.apply_ml_boost map results in
      expect (List.length boosted = 1) (tag ^ ": kept");
      expect ((List.hd boosted).evidence_weight = 0.8) (tag ^ ": unchanged"));

  run "apply_ml_boost: empty map unchanged" (fun tag ->
      let map = Hashtbl.create 0 in
      let results = [ mk_scored "TYPO-001" 1.0; mk_scored "TYPO-012" 1.0 ] in
      let boosted = Evidence_scoring.apply_ml_boost map results in
      expect (List.length boosted = 2) (tag ^ ": all kept"));

  run "apply_ml_boost: multiple suppressions" (fun tag ->
      let map = Hashtbl.create 4 in
      Hashtbl.replace map "TYPO-012"
        { Evidence_scoring.precision = 0.0; weight = 0.0; suppress = true };
      Hashtbl.replace map "TYPO-056"
        { Evidence_scoring.precision = 0.0; weight = 0.0; suppress = true };
      let results =
        [
          mk_scored "TYPO-012" 1.0;
          mk_scored "TYPO-056" 1.0;
          mk_scored "TYPO-001" 1.0;
        ]
      in
      let boosted = Evidence_scoring.apply_ml_boost map results in
      expect (List.length boosted = 1) (tag ^ ": 2 suppressed");
      expect ((List.hd boosted).id = "TYPO-001") (tag ^ ": only TYPO-001"))

let () = finalise "ml-confidence"
