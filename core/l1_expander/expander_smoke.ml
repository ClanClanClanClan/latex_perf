open L1_expander

let () =
  let inp = if Array.length Sys.argv > 1 then Sys.argv.(1)
            else "Before \\textbf{A \\emph{B} C} after" in
  let cfg = if Array.length Sys.argv > 2 then Catalogue_loader.load Sys.argv.(2)
            else Catalogue_loader.default in
  let expanded = Simple_expander.expand_fix_with cfg inp in
  let results = Latex_parse_lib.Validators.run_all expanded in
  let open Yojson.Safe in
  let j = `Assoc [
    ("expanded", `String expanded);
    ("validators",
      `List (List.map (fun r -> `Assoc [
        ("id", `String r.Latex_parse_lib.Validators.id);
        ("severity", `String (match r.Latex_parse_lib.Validators.severity with Error->"error"|Warning->"warning"));
        ("message", `String r.Latex_parse_lib.Validators.message);
        ("count", `Int r.Latex_parse_lib.Validators.count)
      ]) results))
  ] in
  print_endline (Yojson.Safe.to_string j)
