open Printf

module T = Latex_parse_lib.Tokenizer_lite

let check_spans s =
  let toks : T.tok list = T.tokenize s in
  let ok = ref true in
  let prev_e = ref 0 in
  List.iter (fun (t:T.tok) ->
    if t.s < !prev_e || t.e < t.s || t.e > String.length s then ok := false;
    prev_e := t.e
  ) toks;
  if !prev_e > String.length s then ok := false;
  if not !ok then eprintf "[tok-props] span check failed for: %S\n%!" s;
  !ok

let check_reconstruct s =
  let toks : T.tok list = T.tokenize s in
  let b = Buffer.create (String.length s) in
  List.iter (fun (t:T.tok) -> Buffer.add_substring b s t.s (t.e - t.s)) toks;
  let s' = Buffer.contents b in
  let ok = String.equal s s' in
  if not ok then eprintf "[tok-props] reconstruct failed for: %S -> %S\n%!" s s';
  ok

let samples = [
  "Simple words and spaces";
  "A -- dash and --- emdash";
  "\\command{arg} and text";
  "Quoted \"text\" 'here'";
  "Brackets ( [ { and } ] )";
  "Math $a+b$ and \\\(c+d\\\) and \\\[e+f\\\]";
]

let () =
  let pass = List.for_all (fun s -> check_spans s && check_reconstruct s) samples in
  if pass then (printf "[tok-props] PASS %d cases\n%!" (List.length samples); exit 0)
  else exit 1
