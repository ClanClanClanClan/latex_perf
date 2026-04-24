(* ══════════════════════════════════════════════════════════════════════
   Validators_project — PRJ-001 through PRJ-004

   Project-level validators. Read from Project_context. Return None if no
   project context is set (single-file mode).
   ══════════════════════════════════════════════════════════════════════ *)

open Validators_common

(* PRJ-001: Cycle in include graph *)
let r_prj_001 : rule =
  let run _s =
    match Project_context.get () with
    | None -> None
    | Some ps ->
        let cycles = ps.graph.Project_graph.cycles in
        if cycles <> [] then
          let paths =
            List.map (fun cycle -> String.concat " -> " cycle) cycles
          in
          Some
            (mk_result ~id:"PRJ-001" ~severity:Error
               ~message:
                 (Printf.sprintf "Cycle in include graph: %s"
                    (String.concat "; " paths))
               ~count:(List.length cycles))
        else None
  in
  mk_rule "PRJ-001" run

(* PRJ-002: Unresolved \input/\include path *)
let r_prj_002 : rule =
  let run _s =
    match Project_context.get () with
    | None -> None
    | Some ps ->
        let unresolved = ps.graph.Project_graph.unresolved in
        if unresolved <> [] then
          let paths =
            List.map
              (fun (src, raw) ->
                Printf.sprintf "%s: \\input{%s}" (Filename.basename src) raw)
              unresolved
          in
          Some
            (mk_result ~id:"PRJ-002" ~severity:Warning
               ~message:
                 (Printf.sprintf "Unresolved include path(s): %s"
                    (String.concat "; " paths))
               ~count:(List.length unresolved))
        else None
  in
  mk_rule "PRJ-002" run

(* PRJ-003: Cross-file undefined reference *)
let r_prj_003 : rule =
  let run _s =
    match Project_context.get () with
    | None -> None
    | Some ps ->
        let undef = ps.cross_file_undefined in
        if undef <> [] then
          let keys =
            List.map
              (fun (key, file) ->
                Printf.sprintf "\\ref{%s} in %s" key (Filename.basename file))
              undef
          in
          Some
            (mk_result ~id:"PRJ-003" ~severity:Warning
               ~message:
                 (Printf.sprintf "Cross-file undefined reference(s): %s"
                    (String.concat "; " keys))
               ~count:(List.length undef))
        else None
  in
  mk_rule "PRJ-003" run

(* PRJ-004: Cross-file duplicate label *)
let r_prj_004 : rule =
  let run _s =
    match Project_context.get () with
    | None -> None
    | Some ps ->
        let dups = ps.cross_file_duplicates in
        if dups <> [] then
          let descs =
            List.map
              (fun (key, files) ->
                Printf.sprintf "\\label{%s} in %s" key
                  (String.concat ", " (List.map Filename.basename files)))
              dups
          in
          Some
            (mk_result ~id:"PRJ-004" ~severity:Warning
               ~message:
                 (Printf.sprintf "Cross-file duplicate label(s): %s"
                    (String.concat "; " descs))
               ~count:(List.length dups))
        else None
  in
  mk_rule "PRJ-004" run

let rules_project : rule list = [ r_prj_001; r_prj_002; r_prj_003; r_prj_004 ]
