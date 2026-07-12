(** Unit tests for [Extension_registry] (WS12 Stage 2: built-in contract
    registry + extension-provides API). *)

open Latex_parse_lib
open Test_helpers
module E = Extension_contract
module R = Extension_registry

let () =
  (* ── ACCEPTANCE: every built-in contract passes over_claims=false ── *)
  run "no built-in contract over-claims its risk" (fun tag ->
      expect
        (R.well_formed ()
        && not (List.exists (fun c -> E.over_claims c) R.builtin))
        (tag ^ ": every built-in is over-claim-free by construction"));

  (* The smart constructor structurally clamps support to the risk cap: even a
     deliberate over-claim is impossible to represent as a built-in. *)
  run "mk clamps an over-claiming support down to the risk cap" (fun tag ->
      let c =
        R.mk ~name:"clamp-me" ~provides:[] ~requires:[] ~risk:E.Unsafe
          ~support:E.Supported
      in
      expect
        (c.E.support = E.Foreign && not (E.over_claims c))
        (tag ^ ": unsafe+supported clamped to foreign"));

  (* ── Registry lookup by name ─────────────────────────────────────── *)
  run "lookup returns the contract for a known package" (fun tag ->
      match R.lookup "minted" with
      | None -> expect false (tag ^ ": minted should be registered")
      | Some c ->
          expect
            (c.E.ext_name = "minted"
            && c.E.risk = E.Unsafe
            && c.E.support = E.Foreign)
            (tag ^ ": minted is unsafe/foreign"));

  run "lookup returns a supported contract for a safe package" (fun tag ->
      match R.lookup "mhchem" with
      | None -> expect false (tag ^ ": mhchem should be registered")
      | Some c ->
          expect
            (c.E.risk = E.Safe && c.E.support = E.Supported)
            (tag ^ ": mhchem is safe/supported"));

  (* ── ACCEPTANCE: unknown name returns None ───────────────────────── *)
  run "lookup of an unknown extension returns None" (fun tag ->
      expect
        (R.lookup "no-such-package-xyz" = None)
        (tag ^ ": unknown name is not a declared contract"));

  (* ── Provides-lookup by rule-id / feature tag ────────────────────── *)
  run "providers_of finds the built-in providing a rule-id" (fun tag ->
      let ps = R.providers_of "CHEM-001" in
      expect
        (List.length ps = 1 && (List.hd ps).E.ext_name = "mhchem")
        (tag ^ ": CHEM-001 is provided by mhchem"));

  run "providers_of finds the built-in providing a feature tag" (fun tag ->
      let ps = R.providers_of "lstlisting" in
      expect
        (List.length ps = 1 && (List.hd ps).E.ext_name = "listings")
        (tag ^ ": lstlisting is provided by listings"));

  run "providers_of an unprovided tag is empty" (fun tag ->
      expect
        (R.providers_of "NOT-A-FEATURE" = [])
        (tag ^ ": no built-in provides an unknown feature"));

  (* ── Union of provides over a set of active extensions ───────────── *)
  run "provides_of_names unions provides of known extensions" (fun tag ->
      let u = R.provides_of_names [ "mhchem"; "biblatex" ] in
      expect
        (List.mem "CHEM-001" u
        && List.mem "BIB-011" u
        && List.mem "bibliography" u
        && List.mem "chem-equation" u)
        (tag ^ ": union covers both packages' provides"));

  run "provides_of_names ignores unknown names and de-duplicates" (fun tag ->
      let u = R.provides_of_names [ "mhchem"; "ghost-pkg"; "mhchem" ] in
      (* Sorted-unique: no duplicate CHEM-001 despite mhchem listed twice. *)
      let chem = List.filter (fun s -> s = "CHEM-001") u in
      expect
        (List.length chem = 1 && not (List.mem "ghost" u))
        (tag ^ ": unknowns contribute nothing, provides de-duplicated"));

  run "provides_of_names of no active extensions is empty" (fun tag ->
      expect (R.provides_of_names [] = []) (tag ^ ": empty set provides nothing"));

  (* ── contracts_of_names partitions known / unknown ───────────────── *)
  run "contracts_of_names partitions known and unknown names" (fun tag ->
      let known, unknown =
        R.contracts_of_names [ "tikz"; "mystery"; "listings" ]
      in
      expect
        (List.map (fun (c : E.contract) -> c.E.ext_name) known
         = [ "tikz"; "listings" ]
        && unknown = [ "mystery" ])
        (tag ^ ": tikz+listings known, mystery unknown"));

  (* ── INTEGRATION: effective support via Stage-1 evaluate ─────────── *)
  run "evaluate_names computes effective support of active extensions"
    (fun tag ->
      let res, unknown =
        R.evaluate_names ~base:E.Supported [ "mhchem"; "tikz"; "ghost" ]
      in
      match res with
      | Error _ -> expect false (tag ^ ": built-ins never reject")
      | Ok eff ->
          (* mhchem=Supported, tikz=Community => effective = Community. *)
          expect
            (eff.E.effective = E.Community && unknown = [ "ghost" ])
            (tag ^ ": effective is Community; ghost is unknown"));

  run "evaluate_names with a foreign built-in downgrades to foreign" (fun tag ->
      let res, _ =
        R.evaluate_names ~base:E.Supported [ "biblatex"; "minted" ]
      in
      match res with
      | Error _ -> expect false (tag ^ ": built-ins never reject")
      | Ok eff ->
          expect
            (eff.E.effective = E.Foreign)
            (tag ^ ": minted drags the guarantee to foreign"));

  run "evaluate_names over the whole registry never rejects" (fun tag ->
      let names = List.map (fun (c : E.contract) -> c.E.ext_name) R.builtin in
      let res, unknown = R.evaluate_names ~base:E.Supported names in
      match res with
      | Error _ -> expect false (tag ^ ": whole registry must evaluate cleanly")
      | Ok eff ->
          expect
            (eff.E.effective = E.Foreign && unknown = [])
            (tag ^ ": all recognised, effective is the weakest (foreign)"));

  finalise "extension-registry"
