open Printf
module P = Latex_parse_lib.Parser_l2

let cases = [
  "\\verb|a b \\]| tail";
  "\\verb*#x y z# end";
]

let () =
  let pass = ref true in
  List.iter (fun s ->
    try
      let n = P.parse s in
      let out = P.serialize n in
      if not (String.contains out '\\') || not (String.exists (fun c -> c='v') out) then (eprintf "[verb] serialize lacks verb: %S\n%!" out; pass := false)
    with _ -> (eprintf "[verb] parse FAIL: %S\n%!" s; pass := false)
  ) cases;
  if !pass then (printf "[verb] PASS %d cases\n%!" (List.length cases); exit 0) else exit 1

