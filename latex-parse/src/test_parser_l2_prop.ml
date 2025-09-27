open Printf
module P = Latex_parse_lib.Parser_l2

let () = Random.self_init ()

let letters n =
  let b = Buffer.create n in
  for _ = 1 to n do
    Buffer.add_char b (Char.chr (97 + Random.int 26))
  done;
  Buffer.contents b

let gen_cmd () =
  let name = letters (3 + Random.int 4) in
  let nopts = Random.int 3 in
  let nargs = Random.int 3 in
  let opts =
    Array.init nopts (fun _ -> letters (1 + Random.int 5)) |> Array.to_list
  in
  let args =
    Array.init nargs (fun _ -> letters (1 + Random.int 6)) |> Array.to_list
  in
  (name, opts, args)

let render_cmd (name, opts, args) =
  let b = Buffer.create 32 in
  Buffer.add_char b '\\';
  Buffer.add_string b name;
  List.iter
    (fun o ->
      Buffer.add_char b '[';
      Buffer.add_string b o;
      Buffer.add_char b ']')
    opts;
  List.iter
    (fun a ->
      Buffer.add_char b '{';
      Buffer.add_string b a;
      Buffer.add_char b '}')
    args;
  Buffer.contents b

let gen_doc () =
  let parts = ref [] in
  let n = 3 + Random.int 5 in
  for _ = 1 to n do
    if Random.bool () then parts := letters (1 + Random.int 5) :: !parts
    else parts := render_cmd (gen_cmd ()) :: !parts
  done;
  String.concat " " (List.rev !parts)

let () =
  let trials = 100 in
  let pass = ref true in
  for _ = 1 to trials do
    let s = gen_doc () in
    try
      let n1 = P.parse s in
      let s1 = P.serialize n1 in
      let n2 = P.parse s1 in
      let s2 = P.serialize n2 in
      if String.trim s1 <> String.trim s2 then (
        eprintf "[parser2-prop] roundtrip FAIL: %S -> %S -> %S\n%!" s s1 s2;
        pass := false)
    with _ ->
      eprintf "[parser2-prop] parse FAIL: %S\n%!" s;
      pass := false
  done;
  if !pass then (
    printf "[parser2-prop] PASS %d trials\n%!" trials;
    exit 0)
  else exit 1
