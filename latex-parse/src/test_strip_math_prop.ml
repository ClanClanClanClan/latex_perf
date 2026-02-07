open Printf

let () = Random.self_init ()

let gen_text () =
  let len = 1 + Random.int 6 in
  let buf = Buffer.create len in
  for _ = 1 to len do
    let c = Char.chr (97 + Random.int 26) in
    Buffer.add_char buf c
  done;
  Buffer.contents buf

let gen_case () =
  (* Build a sequence of Text and Math segments, then materialize with
     delimiters *)
  let segs = ref [] in
  let n = 3 + Random.int 4 in
  for _ = 1 to n do
    let is_math = Random.bool () in
    let t = gen_text () in
    segs := (is_math, t) :: !segs
  done;
  let segs = List.rev !segs in
  let s =
    let buf = Buffer.create 64 in
    List.iter
      (fun (m, t) ->
        if m then (
          match Random.int 4 with
          | 0 ->
              Buffer.add_char buf '$';
              Buffer.add_string buf t;
              Buffer.add_char buf '$'
          | 1 ->
              Buffer.add_string buf "\\(";
              Buffer.add_string buf t;
              Buffer.add_string buf "\\)"
          | 2 ->
              Buffer.add_string buf "\\[";
              Buffer.add_string buf t;
              Buffer.add_string buf "\\]"
          | _ ->
              Buffer.add_string buf "\\begin{equation}";
              Buffer.add_string buf t;
              Buffer.add_string buf "\\end{equation}")
        else (
          Buffer.add_string buf t;
          Buffer.add_char buf ' '))
      segs;
    Buffer.contents buf
  in
  let expected =
    String.concat " "
      (List.filter_map (fun (m, t) -> if m then None else Some t) segs)
  in
  (s, expected)

let () =
  let open Latex_parse_lib.Validators in
  let trials = 100 in
  let pass = ref true in
  for _ = 1 to trials do
    let s, exp = gen_case () in
    let got = strip_math_segments s in
    let got2 = strip_math_segments got in
    if got <> got2 then (
      eprintf "[strip-prop] idempotence FAIL: %S -> %S -> %S\n%!" s got got2;
      pass := false);
    if String.trim got <> String.trim exp then (
      eprintf "[strip-prop] preserve FAIL: %S -> %S (exp %S)\n%!" s got exp;
      pass := false)
  done;
  if !pass then (
    printf "[strip-prop] PASS %d trials\n%!" 100;
    exit 0)
  else exit 1
