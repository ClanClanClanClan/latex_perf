(** Parity test for the [mixed_paragraph_ranges] de-quadratication.

    That helper is shared by twelve MOD-* rules (validators_l1.ml:98-339) and it
    decides, per paragraph, whether the paragraph mixes legacy and modern font
    commands. It used to ask "does any command in the WHOLE document fall inside
    this paragraph?" once per paragraph — O(paragraphs x commands), measurably
    superlinear (the MOD family scaled 6.1-7.3x for 3x the bytes where the
    median rule scales 3.13x). It now assigns each command to its paragraph by
    binary search.

    A speedup that changes a verdict is a regression, not an optimisation, and
    twelve rules ride this one function. So this test keeps the ORIGINAL
    implementation verbatim as a reference oracle and asserts the shipped one
    agrees with it byte-for-byte on every input — the same tactic the repo uses
    for the Coq-extract/hand-mirror parity.

    The reference is deliberately a copy rather than a shared abstraction: if
    someone "simplifies" the shipped version into agreeing with a rewritten
    oracle, the test stops testing anything. *)

open Latex_parse_lib
open Latex_parse_lib.Validators_common
open Test_helpers

(* The pre-2026-08-02 implementation, verbatim. Do not refactor. *)
let reference (s : string) ~(legacy : string list) ~(modern : string list) :
    (int * int) list =
  let paras = split_into_paragraphs s in
  let pcs = Validators_context.get_post_commands () in
  let tokens = command_tokens s in
  let matches set value = List.exists (( = ) value) set in
  let ctx_has off len names =
    List.exists
      (fun (pc : Validators_context.post_command) ->
        pc.s >= off && pc.s < off + len && matches names pc.name)
      pcs
  in
  let tokens_have off len names =
    List.exists
      (fun (name, pos) -> pos >= off && pos < off + len && matches names name)
      tokens
  in
  let has_cmd off len names =
    ctx_has off len names || tokens_have off len names
  in
  let check_para off len = has_cmd off len legacy && has_cmd off len modern in
  let ranges = if paras = [] then [ (0, String.length s) ] else paras in
  List.filter (fun (off, len) -> check_para off len) ranges

(* The real MOD-002..007 sets, plus deliberately awkward ones. *)
let sets =
  [
    ([ "bf"; "it"; "tt" ], [ "textbf"; "textit"; "texttt" ]);
    ([ "bf" ], [ "bfseries" ]);
    ([], [ "textbf" ]) (* empty legacy: nothing can ever mix *);
    ([ "bf" ], []) (* empty modern *);
    ([ "bf" ], [ "bf" ]) (* same name in BOTH sets *);
    ([ "nosuchcmd" ], [ "alsomissing" ]);
  ]

let check name src =
  List.iteri
    (fun i (legacy, modern) ->
      let got = mixed_paragraph_ranges src ~legacy ~modern in
      let want = reference src ~legacy ~modern in
      run (Printf.sprintf "%s / set %d" name i) (fun tag ->
          expect (got = want)
            (Printf.sprintf "%s: shipped %s <> reference %s" tag
               (String.concat ";"
                  (List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) got))
               (String.concat ";"
                  (List.map (fun (a, b) -> Printf.sprintf "(%d,%d)" a b) want)))))
    sets

(* Deterministic pseudo-random documents: no Random.self_init, so a failure is
   reproducible. Mixes paragraph breaks, legacy/modern commands, commands in the
   gaps BETWEEN paragraphs, and comment/verbatim noise. *)
let gen seed =
  let st = Random.State.make [| seed |] in
  let b = Buffer.create 4096 in
  let cmds =
    [| "bf"; "it"; "tt"; "textbf"; "textit"; "texttt"; "emph"; "bfseries" |]
  in
  let n = 20 + Random.State.int st 120 in
  for _ = 1 to n do
    match Random.State.int st 8 with
    | 0 -> Buffer.add_string b "\n\n"
    | 1 -> Buffer.add_string b "\n"
    | 2 ->
        Buffer.add_char b '\\';
        Buffer.add_string b cmds.(Random.State.int st (Array.length cmds));
        Buffer.add_char b ' '
    | 3 -> Buffer.add_string b "% a comment line\n"
    | 4 -> Buffer.add_string b "\\begin{verbatim}\\bf\\end{verbatim}"
    | 5 -> Buffer.add_string b "some ordinary prose "
    | 6 -> Buffer.add_string b "$x^2$ "
    | _ -> Buffer.add_string b "word "
  done;
  Buffer.contents b

let () =
  (* ── Hand-built edge cases ─────────────────────────────────────────────── *)
  check "empty" "";
  check "no paragraphs" "\\bf and \\textbf on one line";
  check "single break" "\\bf here\n\n\\textbf there";
  check "mixing in one paragraph" "\\bf x \\textbf y\n\npara two";
  check "second paragraph mixes" "plain\n\n\\bf x \\textbf y";
  check "trailing blank lines" "\\bf a \\textbf b\n\n\n\n";
  check "leading blank lines" "\n\n\\bf a \\textbf b";
  check "command in the gap between paragraphs"
    "para one\n\n\\bf\n\npara \\textbf two";
  check "only legacy" "\\bf x\n\n\\bf y";
  check "only modern" "\\textbf x\n\n\\textbf y";

  (* ── Deterministic generated corpus ────────────────────────────────────── *)
  for seed = 1 to 60 do
    check (Printf.sprintf "generated/%d" seed) (gen seed)
  done;

  (* ── Real documents, which is where paragraph shapes get strange ───────── *)
  let read p =
    try
      let ic = open_in_bin p in
      Fun.protect
        ~finally:(fun () -> close_in_noerr ic)
        (fun () -> Some (really_input_string ic (in_channel_length ic)))
    with _ -> None
  in
  (* dune runs tests from inside _build, and `dune exec` from the project root,
     so neither a repo-relative nor a build-relative literal works for both.
     Walk up until the corpus is visible. *)
  let dir =
    let rec up d n =
      if n = 0 then "corpora/compile_check"
      else
        let c = Filename.concat d "corpora/compile_check" in
        if Sys.file_exists c && Sys.is_directory c then c
        else up (Filename.concat d Filename.parent_dir_name) (n - 1)
    in
    up "." 8
  in
  (match Sys.readdir dir with
  | files ->
      Array.sort compare files;
      Array.iter
        (fun f ->
          if Filename.check_suffix f ".tex" then
            match read (Filename.concat dir f) with
            | Some src -> check ("corpus/" ^ f) src
            | None -> ())
        files
  | exception _ ->
      (* Refuse to look green if the corpus could not be read at all: the
         generated cases alone are a weaker test than this file claims to be. *)
      run "corpus readable" (fun tag ->
          expect false (tag ^ ": could not read " ^ dir)));

  finalise "mixed-paragraph-parity"
