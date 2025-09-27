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

let serialize_nodes = P.serialize

(* Simple transform: add a dummy empty optional arg [x] to commands lacking
   opts; remove later to compare. *)
let dummy_opt = "__l2_dummy_opt__"

let transform nodes =
  let add_opt c =
    if c.P.opts = [] then { c with P.opts = [ dummy_opt ] } else c
  in
  let rec go = function
    | [] -> []
    | P.Cmd c :: xs -> P.Cmd (add_opt c) :: go xs
    | P.Group g :: xs -> P.Group (go g) :: go xs
    | n :: xs -> n :: go xs
  in
  go nodes

let strip_dummy_opt s =
  (* remove sentinel optional arguments introduced by transform *)
  let target = "[" ^ dummy_opt ^ "]" in
  let tlen = String.length target in
  let buf = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if !i + tlen <= n && String.sub s !i tlen = target then i := !i + tlen
    else (
      Buffer.add_char buf (String.unsafe_get s !i);
      incr i)
  done;
  Buffer.contents buf

let () =
  let trials = 100 in
  let pass = ref true in
  for _ = 1 to trials do
    let s = gen_doc () in
    try
      let n1 = P.parse s in
      let s1 = serialize_nodes n1 in
      let n2 = transform n1 in
      let t1 = serialize_nodes n2 in
      let t1_stripped = strip_dummy_opt t1 in
      if String.trim s1 <> String.trim t1_stripped then (
        eprintf "[parser2-xform] FAIL: %S -> %S stripped %S\n%!" s s1
          t1_stripped;
        pass := false)
    with _ ->
      eprintf "[parser2-xform] parse FAIL: %S\n%!" s;
      pass := false
  done;
  if !pass then (
    printf "[parser2-xform] PASS %d trials\n%!" trials;
    exit 0)
  else exit 1
