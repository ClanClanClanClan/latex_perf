(** Regex-vs-AST PARITY GATE (Tier 2 Stage 2, V27_2 plan T2-Stage2).

    This is the deliverable that lets the deprecated regex label/ref/cite
    extractors be retired safely. For every file in [corpora/lint] it runs BOTH
    the old regex extractors —
      - [Validators_common.extract_labels_with_prefix ""]  (labels)
      - [Validators_common.extract_refs_with_prefix ""]    (refs)
      - the REF-008 `@[a-zA-Z]+{[ \t]*<key>` regex          (bib cites)
    and the new comment/verbatim-aware AST extractors —
      - [Ast_semantic_state.labels] / [refs] / [cites]
    and asserts they return the SAME (offset, key) set, with EXACTLY ONE class
    of permitted difference: a regex match whose token offset lies inside a
    [find_verbatim_comment_url_ranges] span (a `\label`/`\ref`/`@entry` written
    inside a comment / verbatim / `\verb` / url). Those are the intended
    false-match corrections — the AST drops them, the regex kept them. The gate
    prints every such correction so the divergence is auditable, and fails hard
    on any OTHER divergence (an AST match the regex missed, or a non-protected
    regex match the AST dropped).

    It also runs a self-test on a synthetic document that plants a real and a
    commented/verbatim label/ref/cite, proving (a) the corrections fire and
    (b) nothing else diverges.

    Wired into [scripts/tools/check_ast_parity.py] → pre_release_check. *)

open Latex_parse_lib

let fails = ref 0
let files_checked = ref 0
let total_corrections = ref 0

(* ── Corpus location (mirrors the other corpus tests). ─────────────── *)
let repo_root = Sys.getcwd ()

let lint_dir () =
  let candidates =
    [
      Filename.concat repo_root "corpora/lint";
      Filename.concat repo_root "../../corpora/lint";
      Filename.concat repo_root "../../../corpora/lint";
    ]
  in
  List.find_opt Sys.file_exists candidates

let read_all path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* Recursively list *.tex under a directory. *)
let rec tex_files dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.concat_map (fun name ->
         let p = Filename.concat dir name in
         if Sys.is_directory p then tex_files p
         else if Filename.check_suffix p ".tex" then [ p ]
         else [])

(* ── Old REF-008 @entry regex, reproduced verbatim from validators_l2. ── *)
let re_entry = Re_compat.regexp {|@[a-zA-Z]+{[ \t]*\([^, \t\n}]+\)|}

let old_cites (s : string) : (int * string) list =
  let out = ref [] in
  let i = ref 0 in
  (try
     while true do
       let mr, pos = Re_compat.search_forward re_entry s !i in
       let key = Re_compat.matched_group mr 1 s in
       out := (pos, key) :: !out;
       i := Re_compat.match_end mr
     done
   with Not_found -> ());
  List.rev !out

(* ── Set helpers. ──────────────────────────────────────────────────── *)
let sort_uniq = List.sort_uniq compare

let in_ranges ranges off =
  List.exists (fun (a, b) -> a <= off && off < b) ranges

(* Compare one extractor pair on one source. Returns the number of intended
   corrections, and records a failure (with diagnostics) on any unexpected
   divergence. [kind] labels the extractor for diagnostics. *)
let compare_one ~kind ~src ~old_pairs ~new_pairs : int =
  let protected = Validators_common.find_verbatim_comment_url_ranges src in
  let old_set = sort_uniq old_pairs in
  let new_set = sort_uniq new_pairs in
  (* corrections = old matches inside a protected span. *)
  let corrections =
    List.filter (fun (off, _) -> in_ranges protected off) old_set
  in
  let expected_new =
    List.filter (fun (off, _) -> not (in_ranges protected off)) old_set
  in
  if new_set <> sort_uniq expected_new then (
    incr fails;
    let missing =
      List.filter (fun x -> not (List.mem x new_set)) expected_new
    in
    let extra = List.filter (fun x -> not (List.mem x expected_new)) new_set in
    Printf.eprintf "[ast-parity] FAIL %s\n" kind;
    List.iter
      (fun (o, k) ->
        Printf.eprintf
          "    AST dropped a NON-protected regex match: off=%d key=%S\n" o k)
      missing;
    List.iter
      (fun (o, k) ->
        Printf.eprintf
          "    AST invented a match the regex did not have: off=%d key=%S\n" o k)
      extra;
    Printf.eprintf "%!");
  List.length corrections

let show_correction file kind (off, key) =
  Printf.printf
    "  correction [%s] %s: off=%d key=%S dropped (inside protected region)\n"
    kind (Filename.basename file) off key

let check_file file =
  incr files_checked;
  let src = read_all file in
  let protected = Validators_common.find_verbatim_comment_url_ranges src in
  (* labels *)
  let old_l =
    Validators_common.extract_labels_with_prefix "" src
    (* extract_*_with_prefix returns (off, prefix ^ key) = (off, full key) *)
  in
  let new_l =
    List.map
      (fun (l : Ast_semantic_state.label_entry) -> (l.off, l.key))
      (Ast_semantic_state.labels src)
  in
  total_corrections :=
    !total_corrections
    + compare_one ~kind:"labels" ~src ~old_pairs:old_l ~new_pairs:new_l;
  (* refs *)
  let old_r = Validators_common.extract_refs_with_prefix "" src in
  let new_r =
    List.map
      (fun (r : Ast_semantic_state.ref_entry) -> (r.off, r.key))
      (Ast_semantic_state.refs src)
  in
  total_corrections :=
    !total_corrections
    + compare_one ~kind:"refs" ~src ~old_pairs:old_r ~new_pairs:new_r;
  (* cites (bib @entry) *)
  let old_c = old_cites src in
  let new_c =
    List.map
      (fun (c : Ast_semantic_state.cite_entry) -> (c.off, c.key))
      (Ast_semantic_state.cites src)
  in
  total_corrections :=
    !total_corrections
    + compare_one ~kind:"cites" ~src ~old_pairs:old_c ~new_pairs:new_c;
  (* Print the corrections for auditability. *)
  List.iter
    (fun p ->
      if in_ranges protected (fst p) then show_correction file "labels" p)
    (sort_uniq old_l);
  List.iter
    (fun p -> if in_ranges protected (fst p) then show_correction file "refs" p)
    (sort_uniq old_r);
  List.iter
    (fun p ->
      if in_ranges protected (fst p) then show_correction file "cites" p)
    (sort_uniq old_c)

(* ── Self-test: a synthetic doc where the corrections MUST fire. ────── *)
let self_test () =
  let doc =
    String.concat "\n"
      [
        "\\documentclass{article}";
        "\\begin{document}";
        "\\label{fig:real} and \\ref{fig:real}.";
        (* real: kept *)
        "% \\label{fig:commented} \\ref{fig:commented}";
        (* comment: dropped *)
        "\\begin{verbatim}";
        "\\label{fig:verb} \\ref{fig:verb}";
        (* verbatim: dropped *)
        "@article{verbkey, title={x}}";
        (* verbatim: dropped *)
        "\\end{verbatim}";
        "@book{realkey, title={y}}";
        (* real bib: kept *)
        "\\end{document}";
      ]
  in
  let labels = Ast_semantic_state.labels doc in
  let refs = Ast_semantic_state.refs doc in
  let cites = Ast_semantic_state.cites doc in
  let check name cond =
    incr files_checked;
    if not cond then (
      incr fails;
      Printf.eprintf "[ast-parity] SELF-TEST FAIL: %s\n%!" name)
  in
  check "exactly one real label" (List.length labels = 1);
  check "the kept label is fig:real"
    (List.exists
       (fun (l : Ast_semantic_state.label_entry) -> l.key = "fig:real")
       labels);
  check "no commented/verbatim label leaked"
    (not
       (List.exists
          (fun (l : Ast_semantic_state.label_entry) ->
            l.key = "fig:commented" || l.key = "fig:verb")
          labels));
  check "exactly one real ref" (List.length refs = 1);
  check "the kept ref is fig:real"
    (List.exists
       (fun (r : Ast_semantic_state.ref_entry) -> r.key = "fig:real")
       refs);
  check "exactly one real bib cite" (List.length cites = 1);
  check "the kept cite is realkey"
    (List.exists
       (fun (c : Ast_semantic_state.cite_entry) -> c.key = "realkey")
       cites);
  check "no verbatim bib key leaked"
    (not
       (List.exists
          (fun (c : Ast_semantic_state.cite_entry) -> c.key = "verbkey")
          cites));
  (* And parity itself holds on the synthetic doc: 4 corrections total (1 label
     + 1 ref in comment, 1 label + 1 ref + ... in verbatim). We do not hard-code
     the exact count here — check_file already asserts the set algebra; this
     just runs it through the same machinery. *)
  let old_l = Validators_common.extract_labels_with_prefix "" doc in
  let new_l =
    List.map (fun (l : Ast_semantic_state.label_entry) -> (l.off, l.key)) labels
  in
  ignore
    (compare_one ~kind:"self:labels" ~src:doc ~old_pairs:old_l ~new_pairs:new_l);
  let old_r = Validators_common.extract_refs_with_prefix "" doc in
  let new_r =
    List.map (fun (r : Ast_semantic_state.ref_entry) -> (r.off, r.key)) refs
  in
  ignore
    (compare_one ~kind:"self:refs" ~src:doc ~old_pairs:old_r ~new_pairs:new_r);
  let old_c = old_cites doc in
  let new_c =
    List.map (fun (c : Ast_semantic_state.cite_entry) -> (c.off, c.key)) cites
  in
  ignore
    (compare_one ~kind:"self:cites" ~src:doc ~old_pairs:old_c ~new_pairs:new_c)

let () =
  Printf.printf "[ast-parity] regex-vs-AST label/ref/cite parity gate\n%!";
  self_test ();
  (match lint_dir () with
  | None ->
      Printf.eprintf "[ast-parity] FATAL: corpora/lint not found (cwd=%s)\n%!"
        repo_root;
      exit 1
  | Some dir ->
      let files = List.sort compare (tex_files dir) in
      List.iter check_file files);
  Printf.printf
    "[ast-parity] checked %d unit(s); %d protected-region correction(s) total\n\
     %!"
    !files_checked !total_corrections;
  if !fails = 0 then (
    Printf.printf "[ast-parity] PASS\n%!";
    exit 0)
  else (
    Printf.eprintf "[ast-parity] %d FAILURE(S)\n%!" !fails;
    exit 1)
