open Printf
module P = Latex_parse_lib.Parser_l2

let seed =
  match Sys.getenv_opt "TEST_SEED" with
  | Some s -> int_of_string s
  | None -> 12345

let () = Random.init seed

let letters n =
  let b = Buffer.create n in
  for _ = 1 to n do
    Buffer.add_char b (Char.chr (97 + Random.int 26))
  done;
  Buffer.contents b

let gen_opt () =
  (* random letters with optional escaped sequences \\ and \] *)
  let b = Buffer.create 16 in
  let len = 1 + Random.int 6 in
  for _ = 1 to len do
    match Random.int 6 with
    | 0 -> Buffer.add_string b "\\\\"
    | 1 -> Buffer.add_string b "\\]"
    | _ -> Buffer.add_char b (Char.chr (97 + Random.int 26))
  done;
  Buffer.contents b

let gen_cmd () =
  let name = letters (3 + Random.int 4) in
  let nopts = 1 + Random.int 2 in
  let nargs = Random.int 2 in
  let opts = Array.init nopts (fun _ -> gen_opt ()) |> Array.to_list in
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

let check_one pass s =
  try
    let n1 = P.parse s in
    let s1 = P.serialize n1 in
    let n2 = P.parse s1 in
    let s2 = P.serialize n2 in
    if String.trim s1 <> String.trim s2 then (
      eprintf "[opts-esc] roundtrip FAIL: %S -> %S -> %S\n%!" s s1 s2;
      pass := false)
  with _ ->
    eprintf "[opts-esc] parse FAIL: %S\n%!" s;
    pass := false

let () =
  let trials = 1000 in
  let pass = ref true in
  (* --- explicit edge cases --- *)
  check_one pass "\\cmd[\\\\]";
  check_one pass "\\cmd[\\]]";
  check_one pass "\\cmd[]";
  check_one pass "\\cmd[a\\\\b\\]c]";
  check_one pass "\\cmd[\\\\][\\]]";
  check_one pass "\\cmd[\\\\\\]]";
  (* --- random trials --- *)
  for _ = 1 to trials do
    let s = gen_doc () in
    check_one pass s
  done;
  if !pass then (
    printf "[opts-esc] PASS %d trials (seed=%d)\n%!" trials seed;
    exit 0)
  else exit 1
