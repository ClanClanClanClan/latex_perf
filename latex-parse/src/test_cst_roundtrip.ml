(** Runtime byte-lossless round-trip test for [Cst_of_ast] (v26.2 PR B2).

    Walks a curated corpus and asserts [Cst.serialize (of_source src) = src] for
    every file. This is the B2a deliverable — the mandatory runtime guarantee
    per plan §3.2 ADR-005 round-trip scope.

    The structure-lossless claim (B2b) is corpus-tested separately in the
    subset-only list (see [docs/CST_ROUNDTRIP_SCOPE.md]).

    Corpus sources:
    - [corpora/lint/] — shipping lint fixtures (broad coverage)
    - [corpora/roundtrip/] — synthetic edge cases added in this PR

    Failure mode: each failing file produces one FAIL line; the suite exits
    nonzero if ANY byte-lossless check fails. *)

let repo_root = Sys.getcwd ()

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  Bytes.to_string buf

let is_tex f = Filename.check_suffix f ".tex"

let rec collect_tex dir acc =
  match Sys.readdir dir with
  | exception Sys_error _ -> acc
  | entries ->
      Array.fold_left
        (fun acc entry ->
          let path = Filename.concat dir entry in
          match (Unix.stat path).st_kind with
          | Unix.S_DIR -> collect_tex path acc
          | Unix.S_REG when is_tex entry -> path :: acc
          | _ -> acc
          | exception _ -> acc)
        acc entries

let check_byte_lossless (path : string) : bool =
  let src = read_file path in
  let cst = Latex_parse_lib.Cst_of_ast.of_source src in
  let ser = Latex_parse_lib.Cst.serialize cst in
  if ser = src then true
  else
    let n = String.length src and m = String.length ser in
    let first_diff =
      let lim = min n m in
      let rec go i =
        if i >= lim then lim
        else if String.unsafe_get src i <> String.unsafe_get ser i then i
        else go (i + 1)
      in
      go 0
    in
    Printf.eprintf
      "[cst-roundtrip] FAIL %s  src_len=%d  ser_len=%d  first_diff=%d\n" path n
      m first_diff;
    false

let () =
  let dirs_to_scan =
    List.filter
      (fun d -> Sys.file_exists d && Sys.is_directory d)
      [
        Filename.concat repo_root "corpora/roundtrip";
        Filename.concat repo_root "../../corpora/roundtrip";
        Filename.concat repo_root "corpora/lint";
        Filename.concat repo_root "../../corpora/lint";
      ]
  in
  let files = List.fold_left (fun acc d -> collect_tex d acc) [] dirs_to_scan in
  let files = List.sort_uniq compare files in
  if files = [] then (
    Printf.eprintf
      "[cst-roundtrip] FAIL: no .tex files found under corpora/roundtrip or \
       corpora/lint (cwd=%s)\n"
      repo_root;
    exit 2);
  let total = List.length files in
  let failures = ref 0 in
  List.iter
    (fun path -> if not (check_byte_lossless path) then incr failures)
    files;
  let ok = total - !failures in
  Printf.printf "[cst-roundtrip] byte-lossless: %d / %d files PASS\n" ok total;
  if !failures > 0 then (
    Printf.eprintf "[cst-roundtrip] FAIL: %d files lost bytes on round-trip\n"
      !failures;
    exit 2)
  else Printf.printf "[cst-roundtrip] PASS\n"
