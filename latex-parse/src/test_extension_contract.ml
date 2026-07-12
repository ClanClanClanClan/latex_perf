(** Unit tests for [Extension_contract] (WS12 Stage 1). *)

open Latex_parse_lib
open Test_helpers
module E = Extension_contract

let manifest exts = Printf.sprintf {|{ "extensions": [ %s ] }|} exts

let ext ~name ~risk ~support ?(provides = "") ?(requires = "") () =
  Printf.sprintf
    {|{ "name": "%s", "risk": "%s", "support": "%s", "provides": [%s], "requires": [%s] }|}
    name risk support provides requires

let () =
  (* ── Ordering / boundary primitives ──────────────────────────── *)
  run "support ordering: supported > community > foreign" (fun tag ->
      expect
        (E.support_rank E.Supported > E.support_rank E.Community
        && E.support_rank E.Community > E.support_rank E.Foreign)
        (tag ^ ": ranks strictly ordered"));

  run "support_min never upgrades" (fun tag ->
      expect
        (E.support_min E.Supported E.Foreign = E.Foreign
        && E.support_min E.Community E.Supported = E.Community)
        (tag ^ ": min picks the weaker level"));

  run "max_support_for_risk caps by risk" (fun tag ->
      expect
        (E.max_support_for_risk E.Safe = E.Supported
        && E.max_support_for_risk E.Review = E.Community
        && E.max_support_for_risk E.Unsafe = E.Foreign)
        (tag ^ ": risk caps guarantee"));

  (* ── ACCEPTANCE: a foreign extension downgrades the level ─────── *)
  run "foreign extension downgrades the effective level" (fun tag ->
      match
        E.load_string
          (manifest
             (ext ~name:"minted" ~risk:"unsafe" ~support:"foreign"
                ~provides:{|"VERB-006"|} ()))
      with
      | Error m -> expect false (tag ^ ": load failed: " ^ m)
      | Ok cs -> (
          match E.evaluate ~base:E.Supported cs with
          | Error _ -> expect false (tag ^ ": unexpected rejection")
          | Ok eff ->
              expect
                (eff.effective = E.Foreign
                && List.length eff.entries = 1
                && (List.hd eff.entries).e_downgrade)
                (tag ^ ": effective dropped to foreign with downgrade flagged")));

  (* ── ACCEPTANCE: over-claim (supported + unsafe) is rejected ──── *)
  run "extension claiming supported with risk unsafe is rejected" (fun tag ->
      match
        E.load_string
          (manifest
             (ext ~name:"evil-pkg" ~risk:"unsafe" ~support:"supported" ()))
      with
      | Error m -> expect false (tag ^ ": load failed: " ^ m)
      | Ok cs -> (
          expect (E.over_claims (List.hd cs)) (tag ^ ": over_claims detected");
          match E.evaluate ~base:E.Supported cs with
          | Ok _ -> expect false (tag ^ ": should have been rejected")
          | Error rejs ->
              expect
                (List.length rejs = 1 && (List.hd rejs).r_name = "evil-pkg")
                (tag ^ ": one rejection naming the offender")));

  (* A review extension claiming supported is likewise rejected. *)
  run "review extension claiming supported is rejected" (fun tag ->
      match
        E.load_string
          (manifest (ext ~name:"beta" ~risk:"review" ~support:"supported" ()))
      with
      | Error m -> expect false (tag ^ ": load failed: " ^ m)
      | Ok cs -> (
          match E.evaluate ~base:E.Supported cs with
          | Ok _ -> expect false (tag ^ ": should have been rejected")
          | Error rejs -> expect (List.length rejs = 1) (tag ^ ": rejected")));

  (* ── ACCEPTANCE: a safe supported extension keeps the level ───── *)
  run "safe supported extension keeps the effective level" (fun tag ->
      match
        E.load_string
          (manifest
             (ext ~name:"babel-core" ~risk:"safe" ~support:"supported"
                ~requires:{|"babel"|} ()))
      with
      | Error m -> expect false (tag ^ ": load failed: " ^ m)
      | Ok cs -> (
          match E.evaluate ~base:E.Supported cs with
          | Error _ -> expect false (tag ^ ": unexpected rejection")
          | Ok eff ->
              expect
                (eff.effective = E.Supported
                && not (List.hd eff.entries).e_downgrade)
                (tag ^ ": level preserved, no downgrade")));

  (* Multiple extensions: effective = weakest accepted; foreign wins the min. *)
  run "effective support is the weakest accepted extension" (fun tag ->
      let m =
        manifest
          (String.concat ", "
             [
               ext ~name:"a" ~risk:"safe" ~support:"supported" ();
               ext ~name:"b" ~risk:"review" ~support:"community" ();
               ext ~name:"c" ~risk:"unsafe" ~support:"foreign" ();
             ])
      in
      match E.load_string m with
      | Error msg -> expect false (tag ^ ": load failed: " ^ msg)
      | Ok cs -> (
          match E.evaluate ~base:E.Supported cs with
          | Error _ -> expect false (tag ^ ": unexpected rejection")
          | Ok eff ->
              let downgraded =
                List.filter (fun (e : E.entry) -> e.e_downgrade) eff.entries
              in
              expect
                (eff.effective = E.Foreign && List.length downgraded = 2)
                (tag ^ ": min is foreign, two of three downgrade")));

  (* Reasons are machine-readable and non-empty for every entry. *)
  run "every entry carries a non-empty machine-readable reason" (fun tag ->
      match
        E.load_string
          (manifest (ext ~name:"x" ~risk:"review" ~support:"community" ()))
      with
      | Error m -> expect false (tag ^ ": load failed: " ^ m)
      | Ok cs -> (
          match E.evaluate ~base:E.Supported cs with
          | Error _ -> expect false (tag ^ ": unexpected rejection")
          | Ok eff ->
              let e = List.hd eff.entries in
              expect
                (String.length e.e_reason > 0 && e.e_downgrade)
                (tag ^ ": reason present: " ^ e.e_reason)));

  (* ── downgrades_below drives --strict ────────────────────────── *)
  run "downgrades_below detects sub-threshold effective support" (fun tag ->
      match
        E.load_string
          (manifest (ext ~name:"z" ~risk:"unsafe" ~support:"foreign" ()))
      with
      | Error m -> expect false (tag ^ ": load failed: " ^ m)
      | Ok cs -> (
          match E.evaluate ~base:E.Supported cs with
          | Error _ -> expect false (tag ^ ": unexpected rejection")
          | Ok eff ->
              expect
                (E.downgrades_below eff E.Supported
                && not (E.downgrades_below eff E.Foreign))
                (tag ^ ": below supported but not below foreign")));

  (* Empty manifest: effective equals base, no entries. *)
  run "empty manifest keeps base support with no entries" (fun tag ->
      match E.load_string (manifest "") with
      | Error m -> expect false (tag ^ ": load failed: " ^ m)
      | Ok cs -> (
          match E.evaluate ~base:E.Community cs with
          | Error _ -> expect false (tag ^ ": unexpected rejection")
          | Ok eff ->
              expect
                (eff.effective = E.Community && eff.entries = [])
                (tag ^ ": base unchanged")));

  (* ── ACCEPTANCE: a malformed manifest is reported, not crashed ── *)
  run "malformed JSON is reported not crashed" (fun tag ->
      match E.load_string "{ this is not json" with
      | Ok _ -> expect false (tag ^ ": should not parse")
      | Error msg -> expect (String.length msg > 0) (tag ^ ": " ^ msg));

  run "unknown risk value is reported" (fun tag ->
      match
        E.load_string
          (manifest (ext ~name:"q" ~risk:"medium" ~support:"community" ()))
      with
      | Ok _ -> expect false (tag ^ ": should reject unknown risk")
      | Error msg -> expect (String.length msg > 0) (tag ^ ": " ^ msg));

  run "unknown support value is reported" (fun tag ->
      match
        E.load_string
          (manifest (ext ~name:"q" ~risk:"safe" ~support:"blessed" ()))
      with
      | Ok _ -> expect false (tag ^ ": should reject unknown support")
      | Error msg -> expect (String.length msg > 0) (tag ^ ": " ^ msg));

  run "missing required field is reported" (fun tag ->
      match E.load_string {|{ "extensions": [ { "name": "nf" } ] }|} with
      | Ok _ -> expect false (tag ^ ": should reject missing risk/support")
      | Error msg -> expect (String.length msg > 0) (tag ^ ": " ^ msg));

  run "manifest without extensions list is reported" (fun tag ->
      match E.load_string {|{ "foo": 1 }|} with
      | Ok _ -> expect false (tag ^ ": should require extensions list")
      | Error msg -> expect (String.length msg > 0) (tag ^ ": " ^ msg));

  run "load_file on a missing file is reported not crashed" (fun tag ->
      match E.load_file "/nonexistent/no/such/manifest.json" with
      | Ok _ -> expect false (tag ^ ": should fail")
      | Error msg -> expect (String.length msg > 0) (tag ^ ": " ^ msg));

  finalise "extension-contract"
