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
  let results = V.run_all expanded in
  let validators_json =
    List.map
      (fun (r : V.result) ->
        let open V in
        let { id; severity; message; count } = r in
        Yojson.Safe.(
          `Assoc
            [
              ("id", `String id);
              ( "severity",
                `String
                  (match severity with
                   | Error -> "error"
                   | Warning -> "warning"
                   | Info -> "info") );
              ("message", `String message);
              ("count", `Int count);
            ]))
      results
  in
  let payload =
    Yojson.Safe.(
      `Assoc
        [
          ("expanded", `String expanded);
          ("validators", `List validators_json);
        ])
  in
  Yojson.Safe.to_string payload |> print_endline
