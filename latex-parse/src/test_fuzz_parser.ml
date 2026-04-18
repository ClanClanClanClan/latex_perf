(** Grammar-aware parser fuzzing.

    Generates random LaTeX fragments and verifies Parser_l2.parse doesn't crash.
    Uses TEST_SEED for reproducibility and FUZZ_TRIALS for iteration count. *)

let seed =
  match Sys.getenv_opt "TEST_SEED" with
  | Some s -> int_of_string s
  | None -> 12345

let trials =
  match Sys.getenv_opt "FUZZ_TRIALS" with
  | Some s -> int_of_string s
  | None -> 5000

let () = Random.init seed
let random_char () = Char.chr (32 + Random.int 95)
let random_string n = String.init n (fun _ -> random_char ())

let gen_command () =
  let cmds =
    [|
      "\\textbf";
      "\\emph";
      "\\section";
      "\\ref";
      "\\label";
      "\\cite";
      "\\newcommand";
      "\\renewcommand";
      "\\usepackage";
      "\\input";
    |]
  in
  let cmd = cmds.(Random.int (Array.length cmds)) in
  if Random.bool () then cmd ^ "{" ^ random_string (1 + Random.int 10) ^ "}"
  else cmd

let gen_math_inline () = "$" ^ random_string (1 + Random.int 20) ^ "$"

let gen_math_display () =
  if Random.bool () then "\\[" ^ random_string (1 + Random.int 20) ^ "\\]"
  else "$$" ^ random_string (1 + Random.int 20) ^ "$$"

let gen_environment () =
  let envs = [| "itemize"; "enumerate"; "figure"; "table"; "align" |] in
  let env = envs.(Random.int (Array.length envs)) in
  "\\begin{"
  ^ env
  ^ "}\n"
  ^ random_string (5 + Random.int 30)
  ^ "\n\\end{"
  ^ env
  ^ "}"

let gen_nested_braces () =
  let depth = 1 + Random.int 5 in
  let s = random_string (1 + Random.int 10) in
  let rec wrap n s = if n <= 0 then s else wrap (n - 1) ("{" ^ s ^ "}") in
  wrap depth s

let gen_comment () = "% " ^ random_string (5 + Random.int 30) ^ "\n"
let gen_verb () = "\\verb|" ^ random_string (1 + Random.int 15) ^ "|"
let gen_text () = random_string (5 + Random.int 40)

let gen_fragment () =
  match Random.int 8 with
  | 0 -> gen_command ()
  | 1 -> gen_math_inline ()
  | 2 -> gen_math_display ()
  | 3 -> gen_environment ()
  | 4 -> gen_nested_braces ()
  | 5 -> gen_comment ()
  | 6 -> gen_verb ()
  | _ -> gen_text ()

let gen_doc () =
  let n = 3 + Random.int 8 in
  String.concat " " (List.init n (fun _ -> gen_fragment ()))

let () =
  Printf.printf "[fuzz-parser] seed=%d trials=%d\n%!" seed trials;
  let crashes = ref 0 in
  for i = 1 to trials do
    let src = gen_doc () in
    try ignore (Latex_parse_lib.Parser_l2.parse src)
    with exn ->
      incr crashes;
      if !crashes <= 5 then
        Printf.eprintf "[fuzz-parser] CRASH at trial %d: %s\ninput: %S\n%!" i
          (Printexc.to_string exn)
          (String.sub src 0 (min 100 (String.length src)))
  done;
  if !crashes > 0 then (
    Printf.eprintf "[fuzz-parser] FAIL: %d/%d crashes\n%!" !crashes trials;
    exit 1)
  else Printf.printf "[fuzz-parser] PASS %d trials (seed=%d)\n%!" trials seed
