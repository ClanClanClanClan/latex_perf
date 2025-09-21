open L1_expander

let cases = [
  "Before \\textbf{A \\emph{B} C} after", "Before A \\emph{B} C after";
  "\\textbf{X}", "X";
  "plain", "plain";
]

let () =
  List.iter (fun (inp,exp) ->
    let got = Simple_expander.expand_fix inp in
    if got <> exp then (prerr_endline ("[simple-expander] mismatch: expected '"^exp^"' got '"^got^"'"); exit 1)
  ) cases;
  print_endline "[simple-expander] OK"

