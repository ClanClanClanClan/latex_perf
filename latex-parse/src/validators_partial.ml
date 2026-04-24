(* ══════════════════════════════════════════════════════════════════════
   Validators_partial — PRT-001, PRT-002

   Partial document validators. Read from Partial_context. Return None if no
   context is set or document is Complete.
   ══════════════════════════════════════════════════════════════════════ *)

open Validators_common

(* PRT-001: Document has parse errors — severity based on confidence *)
let r_prt_001 : rule =
  let run _s =
    match Partial_context.get () with
    | None -> None
    | Some pd -> (
        match pd.Partial_cst.confidence with
        | Partial_cst.Complete -> None
        | Partial_cst.Partial ->
            Some
              (mk_result ~id:"PRT-001" ~severity:Warning
                 ~message:
                   (Printf.sprintf
                      "Document has parse errors in %d region(s); some results \
                       may be incomplete"
                      (List.length pd.error_regions))
                 ~count:(List.length pd.error_regions))
        | Partial_cst.Broken ->
            Some
              (mk_result ~id:"PRT-001" ~severity:Error
                 ~message:
                   (Printf.sprintf
                      "Document has %d parse error(s); results in affected \
                       regions are unreliable"
                      (List.length pd.error_regions))
                 ~count:(List.length pd.error_regions)))
  in
  mk_rule "PRT-001" run

(* PRT-002: Error region spans multiple trust zones *)
let r_prt_002 : rule =
  let run _s =
    match Partial_context.get () with
    | None -> None
    | Some pd ->
        let broken_zones =
          List.filter
            (fun z ->
              (z : Partial_cst.trust_zone).confidence = Partial_cst.Broken)
            pd.trust_zones
        in
        let partial_zones =
          List.filter
            (fun z ->
              (z : Partial_cst.trust_zone).confidence = Partial_cst.Partial)
            pd.trust_zones
        in
        let cross_boundary =
          List.length broken_zones > 0 && List.length partial_zones > 0
        in
        if cross_boundary then
          Some
            (mk_result ~id:"PRT-002" ~severity:Info
               ~message:
                 (Printf.sprintf
                    "Parse errors affect %d zone(s) with %d adjacent partial \
                     zone(s)"
                    (List.length broken_zones)
                    (List.length partial_zones))
               ~count:(List.length broken_zones + List.length partial_zones))
        else None
  in
  mk_rule "PRT-002" run

let rules_partial : rule list = [ r_prt_001; r_prt_002 ]
