open Printf

let cases = [
  ("no math here", "no math here");
  ("inline $a+b=c$ text", "inline  text");
  ("paren \\(x\\) text", "paren  text");
  ("brack \\[y\\] text", "brack  text");
  ("env \\begin{equation}E=mc^2\\end{equation} outside", "env  outside");
  ("env-star \\begin{align*}a&=b\\end{align*} outside", "env-star  outside");
  ("escaped dollar \\$100 inline", "escaped dollar \\$100 inline");
  ("nested \\[ \\text{ “quote” } \\] end", "nested  end");
]

let () =
  let open Latex_parse_lib.Validators in
  let fails = ref 0 in
  List.iter (fun (inp, exp) ->
    let got = strip_math_segments inp in
    if got <> exp then begin
      incr fails;
      eprintf "[strip-math] FAIL\n  in:  %S\n  got: %S\n  exp: %S\n%!" inp got exp
    end
  ) cases;
  if !fails = 0 then (printf "[strip-math] PASS %d cases\n%!" (List.length cases); exit 0)
  else exit 1

