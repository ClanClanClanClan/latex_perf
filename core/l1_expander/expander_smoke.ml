open L1_expander
module LP = L0_lexer.Latex_parse_lib
open LP

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
  let results = Validators.run_all expanded in
  let open Yojson.Safe in
  let j =
    `Assoc
      [
        ("expanded", `String expanded);
        ( "validators",
          `List
            (List.map
               (fun r ->
                 `Assoc
                   [
                     ("id", `String r.id);
                     ( "severity",
                       `String
                         (match r.severity with
                         | Error -> "error"
                         | Warning -> "warning"
                         | Info -> "info") );
                     ("message", `String r.message);
                     ("count", `Int r.count);
                   ])
               results) );
      ]
  in
  print_endline (Yojson.Safe.to_string j)
