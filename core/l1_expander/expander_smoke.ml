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
  let payload =
    Yojson.Safe.(
      `Assoc
        [
          ("expanded", `String expanded);
          ("validators", `List []);
        ])
  in
  Yojson.Safe.to_string payload |> print_endline
