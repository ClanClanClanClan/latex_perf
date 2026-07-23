(** Differential PARITY sweep for the VERIFIED bytes->body_token front-end.

    Two independent implementations of the SAME function must agree, token for
    token, on every input:

    - [Compile_evidence.extract_body] — the ORIGINAL hand-written OCaml
      extractor (labels/refs via [Ast_semantic_state], feature scan via
      [detect_body_features]).
    - [Compile_evidence.extract_body_verified] — the Coq-EXTRACTED front-end
      [Body_token_frontend_extracted.body_of_source], mapped 1:1 back to the
      runtime surface types.

    The Coq theorem [compile_safe_of_source] proves the extracted front-end
    sound; this test is the empirical cross-check that the extracted code and
    the hand OCaml compute IDENTICAL body-token streams. ANY inequality is a
    real divergence between the proven model and the runtime path and MUST be
    surfaced — assertions are never weakened to force a pass.

    Structure mirrors [test_compile_evidence.ml] (hand-rolled exit-code tests,
    corpus located relative to [Sys.getcwd ()]). *)

open Latex_parse_lib
open Test_helpers
module CE = Compile_evidence

(* ── Stack headroom ──────────────────────────────────────────────────── We run
   the ENTIRE test body inside a systhread worker (OCaml POSIX threads get their
   own large system stack) as defensive headroom for the extracted front-end's
   per-byte non-tail recursion (scan_from / contains_b / firstn / skipn / app /
   map, as extracted). This changes NO assertion; it only supplies stack.
   [finalise] calls [exit] on failure, which terminates the whole process from
   within the worker.

   ⚠ KNOWN DEFECT (surfaced by this gate, 2026-07): the extracted module
   [Body_token_frontend_extracted] currently DOES NOT INITIALISE at run time.
   Its top-level [let two30 = Nat.pow 2 30] (and the fnv_basis/fnv_prime
   constants) evaluate 2^30 in UNARY Peano arithmetic — [Nat.add]/[Nat.mul]/
   [Nat.pow] were NOT realised as native integer ops, only the [succ]/[0]
   constructors were (ExtrOcamlNatInt). Materialising ~10^9 [succ] cells at
   module load overflows the native stack (and hangs bytecode for minutes)
   BEFORE any test code runs — this also breaks the pre-existing
   [test_compile_evidence]. So [extract_body_verified] is presently unrunnable
   and this parity gate cannot pass. Fix belongs in the extraction directives
   (Extract Constant Nat.pow/mul/add => native), not in this test. The gate is
   left in place, unweakened, so the divergence stays visible. *)

(* ── Corpus location (mirrors the other corpus tests). ─────────────── *)
let repo_root = Sys.getcwd ()

let corpus_dir sub =
  let candidates =
    [
      Filename.concat repo_root ("corpora/" ^ sub);
      Filename.concat repo_root ("../../corpora/" ^ sub);
      Filename.concat repo_root ("../../../corpora/" ^ sub);
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
  |> List.sort compare
  |> List.concat_map (fun name ->
         let p = Filename.concat dir name in
         if Sys.is_directory p then tex_files p
         else if Filename.check_suffix p ".tex" then [ p ]
         else [])

(* ── Pretty-printing of body tokens for diagnostics. ────────────────── *)
let feat_str : CE.feature -> string = CE.feature_to_string

let tok_str : CE.body_token -> string = function
  | CE.BT_text -> "BT_text"
  | CE.BT_label_def n -> Printf.sprintf "BT_label_def(%d)" n
  | CE.BT_label_ref n -> Printf.sprintf "BT_label_ref(%d)" n
  | CE.BT_needs_feature f -> Printf.sprintf "BT_needs_feature(%s)" (feat_str f)

let toks_str l = "[" ^ String.concat "; " (List.map tok_str l) ^ "]"

(* First differing index between two token lists (or None if equal-prefix and
   one is a prefix of the other of unequal length -> reports the length gap). *)
let first_diff (a : CE.body_token list) (b : CE.body_token list) : string =
  let rec go i a b =
    match (a, b) with
    | [], [] -> "(no element diff; lists equal)"
    | x :: _, [] -> Printf.sprintf "at %d: verified=%s hand=<end>" i (tok_str x)
    | [], y :: _ -> Printf.sprintf "at %d: verified=<end> hand=%s" i (tok_str y)
    | x :: xs, y :: ys ->
        if x = y then go (i + 1) xs ys
        else
          Printf.sprintf "at %d: verified=%s hand=%s" i (tok_str x) (tok_str y)
  in
  go 0 a b

(* The differential core: verified MUST equal hand, as exact lists. Records a
   failure with the filename/label and the first differing token on any
   divergence; returns true iff they matched. *)
let mismatches = ref []

let check_parity ~(label : string) ~(src : string) : bool =
  let v = CE.extract_body_verified src in
  let h = CE.extract_body src in
  incr cases;
  if v = h then true
  else (
    incr fails;
    let msg =
      Printf.sprintf "%s: verified != hand\n  verified=%s\n  hand    =%s\n  %s"
        label (toks_str v) (toks_str h) (first_diff v h)
    in
    mismatches := msg :: !mismatches;
    Printf.eprintf "MISMATCH %s\n%!" msg;
    false)

let run_all_tests () =
  (* ── (1) PARITY SWEEP over the real corpora ───────────────────────── *)
  let files =
    List.concat_map
      (fun sub ->
        match corpus_dir sub with Some d -> tex_files d | None -> [])
      [ "lint"; "compile_check" ]
  in
  if files = [] then (
    Printf.eprintf
      "[body-token-frontend] FATAL: no corpus .tex found (cwd=%s)\n%!" repo_root;
    incr fails)
  else
    List.iter
      (fun path ->
        let src = read_all path in
        ignore (check_parity ~label:("corpus:" ^ path) ~src))
      files;
  Printf.printf "[body-token-frontend] parity-swept %d corpus files\n%!"
    (List.length files);

  (* ── (2) Adversarial fixtures ─────────────────────────────────────── *)

  (* Helper: parity AND an exact structural expectation on the shared result. *)
  let check_struct ~label ~src ~(expected : CE.body_token list) =
    let parity_ok = check_parity ~label ~src in
    (* structural claim asserted against the VERIFIED path (parity already
       guarantees the hand path is identical when parity_ok). *)
    let v = CE.extract_body_verified src in
    run (label ^ ": structure") (fun tag ->
        expect (v = expected)
          (Printf.sprintf "%s: expected %s got %s" tag (toks_str expected)
             (toks_str v)));
    parity_ok
  in

  (* The nested-token / two-pass trap: `\label{a\ref{b}}`. The outer label key
     is the raw bytes up to the FIRST closing brace => "a\ref{b" ; the inner
     `\ref{b}` is a genuine ref of key "b". BOTH must appear. Document order:
     the \label opens first, so its def is emitted first; then the ref. *)
  let id_lab_a_ref_b = CE.label_id "a\\ref{b" in
  let id_ref_b = CE.label_id "b" in
  ignore
    (check_struct ~label:"nested \\label{a\\ref{b}}" ~src:"\\label{a\\ref{b}}"
       ~expected:
         [
           CE.BT_label_def id_lab_a_ref_b; CE.BT_label_ref id_ref_b; CE.BT_text;
         ]);

  (* Comment-protected label => no def (just the text marker). *)
  ignore
    (check_struct ~label:"comment-protected %\\label{x}" ~src:"%\\label{x}\n"
       ~expected:[ CE.BT_text ]);

  (* Verbatim-protected label => no def. *)
  ignore
    (check_struct ~label:"verbatim \\verb|\\label{x}|" ~src:"\\verb|\\label{x}|"
       ~expected:[ CE.BT_text ]);

  (* Unclosed \label{x at EOF => no emit (no closing brace). *)
  ignore
    (check_struct ~label:"unclosed \\label{x at EOF" ~src:"\\label{x"
       ~expected:[ CE.BT_text ]);

  (* Empty string => no BT_text (String.trim = ""). *)
  ignore (check_struct ~label:"empty string" ~src:"" ~expected:[]);

  (* Whitespace-only => no BT_text. *)
  ignore (check_struct ~label:"whitespace-only" ~src:"   \n\t  \n" ~expected:[]);

  (* Multibyte UTF-8 label key => byte-level FNV parity. Just assert parity plus
     that a def is present with the FNV of the exact UTF-8 bytes. *)
  let utf8_key = "\195\169q:1" (* "éq:1" *) in
  ignore
    (check_struct ~label:"multibyte \\label{éq:1}"
       ~src:("\\label{" ^ utf8_key ^ "}")
       ~expected:[ CE.BT_label_def (CE.label_id utf8_key); CE.BT_text ]);

  (* Each of the five ref commands: \ref \eqref \autoref \cref \Cref. *)
  List.iter
    (fun cmd ->
      let src = "\\label{k}\\" ^ cmd ^ "{k}" in
      let id_k = CE.label_id "k" in
      ignore
        (check_struct
           ~label:(Printf.sprintf "ref command \\%s" cmd)
           ~src
           ~expected:[ CE.BT_label_def id_k; CE.BT_label_ref id_k; CE.BT_text ]))
    [ "ref"; "eqref"; "autoref"; "cref"; "Cref" ];

  (* `\label {x}` with a space before the brace: BOTH paths must AGREE, whatever
     they do. We do not prescribe the outcome — pure parity assertion. *)
  ignore
    (check_parity ~label:"\\label {x} space-before-brace" ~src:"\\label {x}");

  (* The five feature needles together => identical BT_needs_feature ORDER.
     detect_body_features tests in this fixed order: fontspec(Opentype),
     unicode-math/setmathfont(Unicode_math), luacode(Lua_scripting),
     CJK(Japanese_cjk), inputenc(UTF8_inputenc). *)
  let feat_src =
    "\\usepackage{fontspec}\n\
     \\setmathfont{X}\n\
     \\usepackage{luacode}\n\
     \\usepackage{CJK}\n\
     \\usepackage[utf8]{inputenc}\n\
     Body text.\n"
  in
  ignore
    (check_struct ~label:"five feature needles" ~src:feat_src
       ~expected:
         [
           CE.BT_needs_feature CE.Opentype_fonts;
           CE.BT_needs_feature CE.Unicode_math;
           CE.BT_needs_feature CE.Lua_scripting;
           CE.BT_needs_feature CE.Japanese_cjk;
           CE.BT_needs_feature CE.UTF8_inputenc;
           CE.BT_text;
         ]);

  (* ── (3) ANTI-STUB: 2 labels + 1 ref => exactly 3 non-BT_text tokens + a
     BT_text (guards against the extracted path silently returning []). ── *)
  let stub_src = "\\label{p}\\label{q}\\ref{p} body\n" in
  ignore (check_parity ~label:"anti-stub 2 labels + 1 ref" ~src:stub_src);
  run "anti-stub: exactly 3 non-text tokens + BT_text" (fun tag ->
      let v = CE.extract_body_verified stub_src in
      let non_text =
        List.filter (function CE.BT_text -> false | _ -> true) v
      in
      let has_text = List.mem CE.BT_text v in
      expect
        (List.length non_text = 3 && has_text)
        (Printf.sprintf "%s: expected 3 non-text + BT_text, got %s" tag
           (toks_str v)));

  finalise "body-token-frontend"

(* Run the whole body on a systhread worker: OCaml's POSIX threads get their own
   large system stack, independent of the (macOS-capped, ~64 MB) main-thread
   RLIMIT_STACK — enough headroom for the extracted front-end's per-byte
   non-tail recursion over the largest corpus documents. This changes NO
   assertion; it only supplies stack. [finalise] calls [exit] on failure, which
   terminates the whole process from within the worker. *)
let () =
  let t = Thread.create run_all_tests () in
  Thread.join t
