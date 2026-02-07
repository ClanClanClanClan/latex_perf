open Printf

let samples =
  [ "Plain words here"; "\\cmd{arg} text"; "{nested \\bfseries {bold}} text" ]

let () =
  let pass =
    List.for_all
      (fun s ->
        try
          let nodes = Latex_parse_lib.Parser_l2.parse s in
          ignore nodes;
          true
        with _ -> false)
      samples
  in
  if pass then (
    printf "[parser-l2] PASS %d cases\n%!" (List.length samples);
    exit 0)
  else exit 1
