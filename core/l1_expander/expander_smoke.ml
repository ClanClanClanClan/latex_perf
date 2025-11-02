open L1_expander

let () =
  let inp =
    if Array.length Sys.argv > 1 then Sys.argv.(1)
    else "Before \\textbf{A \\emph{B} C} after"
  in
  let cfg =
    if Array.length Sys.argv > 2 then Catalogue_loader.load Sys.argv.(2)
    else Catalogue_loader.default
  in
  let expanded = Simple_expander.expand_fix_with cfg inp in
  let module V = Latex_parse_lib.Validators in
  let open Yojson.Safe in
  let validators_json =
    V.run_all expanded
    |> List.map (fun (r : V.result) ->
           let open V in
           let severity_str =
             match r.severity with
             | Error -> "error"
             | Warning -> "warning"
             | Info -> "info"
           in
           `Assoc
             [
               ("id", `String r.id);
               ("severity", `String severity_str);
               ("message", `String r.message);
               ("count", `Int r.count);
             ])
  in
  let payload =
    `Assoc
      [
        ("expanded", `String expanded);
        ("validators", `List validators_json);
      ]
  in
  to_string payload |> print_endline
