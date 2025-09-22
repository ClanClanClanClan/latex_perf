open Printf
module P = Latex_parse_lib.Parser_l2

let cases = [
  ("( space after ( and before ) )", "(space after (and before))");
  ("[ list , with , spaces ]", "[list, with, spaces]");
  ("word , punctuation ! and ?", "word, punctuation! and?");
  ("{ group } and ( punct : test )", "{group} and (punct: test)");
  ("\\cmd{arg} , then text", "\\cmd{arg}, then text");
]

let () =
  let pass = ref true in
  List.iter (fun (inp, exp) ->
    try
      let n = P.parse inp in
      let got = P.serialize n in
      if got <> exp then (eprintf "[parser-norm] FAIL\n in: %S\n got: %S\n exp: %S\n%!" inp got exp; pass := false)
    with _ -> (eprintf "[parser-norm] parse FAIL: %S\n%!" inp; pass := false)
  ) cases;
  if !pass then (printf "[parser-norm] PASS %d cases\n%!" (List.length cases); exit 0) else exit 1
