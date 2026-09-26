(** Tests for the ADR-012 verdict type, its renderer, the strict-tier boundary
    scan, and the M0 compile-check surface.

    The load-bearing test is the first one: only a [Proven_] verdict may ever
    render the word PROVEN. It scans every line of the rendering of every
    constructor, including user data that itself contains the word. *)

open Latex_parse_lib
open Test_helpers

let contains s sub =
  let ls = String.length s and lsub = String.length sub in
  let rec go i =
    if i + lsub > ls then false
    else if String.sub s i lsub = sub then true
    else go (i + 1)
  in
  lsub = 0 || go 0

let starts_with s p =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

(* The reason scrape of scripts/tools/diff_real_roots.py. *)
let scrape_re = Re.compile (Re.Perl.re "\\b(T\\d|[A-Z]{2,8}-\\d{3})\\b")

let boundary ?where construct nudge =
  {
    Verdict.b_kind = "def";
    b_where = where;
    b_construct = construct;
    b_nudge = nudge;
  }

let adversarial = "PROVEN"

let heuristic_samples ~data =
  let b = boundary ~where:(data ^ ".tex:3") ("\\" ^ data) ("rewrite " ^ data) in
  [
    Verdict.Likely_ok { basis = "premise-certified"; why_not_strict = [ b ] };
    Verdict.Likely_ok { basis = data; why_not_strict = [ b; b; b; b; b ] };
    Verdict.Likely_fail
      {
        reasons =
          [
            Compile_contract.T0_parse_fails { file = data; message = data };
            Compile_contract.T5_rule_violations [ data ];
          ];
        why_not_strict = [ b; Verdict.m0_boundary ];
      };
    Verdict.Likely_fail { reasons = []; why_not_strict = [] };
    Verdict.Foreign
      {
        construct = "\\" ^ data;
        where = Some (data ^ ":1");
        why_not_strict = [ b ];
      };
    Verdict.Foreign { construct = data; where = None; why_not_strict = [] };
    Verdict.Pending { predicted = `Ready; missing = [ data ] };
    Verdict.Pending { predicted = `Not_ready; missing = [] };
  ]

let proven_samples =
  Verdict.Proven_ready
    { contract = "1a2b3c4d5e"; pin = "pin"; decider = "decide" }
  :: List.map
       (fun r ->
         Verdict.Proven_not_ready
           {
             reason = r;
             message = "\\frac is math-only, used in text mode";
             loc = { Verdict.file = "main.tex"; line = 42; col = 7 };
             rule = "R";
             probe = "P-MODE/frac";
             contract = "1a2b3c4d";
           })
       Verdict.all_fatal_reasons

let () =
  run "only Proven_* can render the reserved word (adversarial user data)"
    (fun tag ->
      List.iter
        (fun data ->
          List.iter
            (fun v ->
              expect (not (Verdict.is_proven v)) (tag ^ ": sample is heuristic");
              let lines = Verdict.render v in
              List.iter
                (fun l ->
                  expect
                    (not (contains l Verdict.reserved_word))
                    (tag ^ ": non-proven line renders the reserved word: " ^ l))
                lines;
              expect
                (not (contains (Verdict.kind_token v) Verdict.reserved_word))
                (tag ^ ": kind token");
              expect
                (not (contains (Verdict.headline v) Verdict.reserved_word))
                (tag ^ ": headline"))
            (heuristic_samples ~data))
        [ adversarial; "x PROVEN y"; "PROVENPROVEN"; "plain"; "" ]);

  run "every non-proven headline says it is not a proof" (fun tag ->
      List.iter
        (fun v ->
          expect
            (contains (Verdict.headline v) "not a proof")
            (tag ^ ": " ^ Verdict.headline v);
          expect (Verdict.tier_token v <> "proven") (tag ^ ": tier token"))
        (heuristic_samples ~data:"plain"));

  run "non-proven fixed text never says proven in any case" (fun tag ->
      List.iter
        (fun v ->
          List.iter
            (fun l ->
              expect
                (not (contains (String.lowercase_ascii l) "proven"))
                (tag ^ ": " ^ l))
            (Verdict.render v))
        (heuristic_samples ~data:"plain"));

  run "Proven_* renders PROVEN, the E-code and the proven tier" (fun tag ->
      List.iter
        (fun v ->
          expect (Verdict.is_proven v) (tag ^ ": is_proven");
          let lines = Verdict.render v in
          expect (List.length lines = 1) (tag ^ ": one line");
          let l = List.hd lines in
          expect (contains l Verdict.reserved_word) (tag ^ ": " ^ l);
          expect (starts_with l "TIER\tproven\tPROVEN-") (tag ^ ": tokens " ^ l);
          match v with
          | Verdict.Proven_not_ready { reason; _ } ->
              expect
                (contains l ("[" ^ Verdict.e_code reason ^ ","))
                (tag ^ ": E-code in " ^ l)
          | _ -> ())
        proven_samples);

  run "the TIER line has four tab fields and at most three why-not-strict lines"
    (fun tag ->
      List.iter
        (fun v ->
          match Verdict.render v with
          | [] -> expect false (tag ^ ": empty rendering")
          | first :: rest ->
              expect
                (List.length (String.split_on_char '\t' first) = 4)
                (tag ^ ": " ^ first);
              expect
                (List.length rest <= Verdict.max_why_not_strict)
                (tag ^ ": too many why-not-strict lines");
              List.iter
                (fun l ->
                  expect (starts_with l "  why not strict: ") (tag ^ ": " ^ l);
                  (* Not a frozen reason line: bench_compile_check.sh greps '^
                     T[0-5]' and regrade_sample.py keeps lines that start with
                     T0..T5 after stripping. *)
                  expect (not (starts_with (String.trim l) "T")) (tag ^ ": " ^ l))
                rest)
        (heuristic_samples ~data:"plain" @ proven_samples));

  run "fixed heuristic text carries no scrape token" (fun tag ->
      List.iter
        (fun v ->
          List.iter
            (fun l ->
              expect
                (not (Re.execp scrape_re l))
                (tag ^ ": scrape token in " ^ l))
            (Verdict.render v))
        (heuristic_samples ~data:"plain"));

  run "defang rewrites every occurrence" (fun tag ->
      expect (Verdict.defang "aPROVENbPROVEN" = "aProvenbProven") tag;
      expect (Verdict.defang "" = "") tag;
      expect (Verdict.defang "PROVE" = "PROVE") tag);

  run "--require-proof exit code is 4" (fun tag ->
      expect (Verdict.require_proof_exit = 4) tag)

(* ── Strict_boundary ─────────────────────────────────────────────── *)

let ids fs = List.map (fun (f : Strict_boundary.finding) -> f.id) fs
let cats fs = List.map (fun (f : Strict_boundary.finding) -> f.category) fs

let () =
  run "def nudge rewrites a plain \\def to \\newcommand" (fun tag ->
      let src = "x\n\\def\\R{\\mathbb R}\n" in
      match Strict_boundary.def_nudge src 2 with
      | Some n ->
          expect (contains n "\\newcommand{\\R}{\\mathbb R}") (tag ^ ": " ^ n)
      | None -> expect false (tag ^ ": no nudge"));

  run "def nudge with undelimited parameters gives an arity" (fun tag ->
      match Strict_boundary.def_nudge "\\def\\f#1#2{#1+#2}" 0 with
      | Some n ->
          expect (contains n "\\newcommand{\\f}[2]{#1+#2}") (tag ^ ": " ^ n)
      | None -> expect false tag);

  run "def nudge refuses a delimited parameter text" (fun tag ->
      match Strict_boundary.def_nudge "\\def\\f#1.{#1}" 0 with
      | Some n -> expect (contains n "delimited") (tag ^ ": " ^ n)
      | None -> expect false tag);

  run "scan finds def with its line and count" (fun tag ->
      let fs =
        Strict_boundary.scan_file ~display:"m.tex"
          "a\nb\n\\def\\x{1}\n\\def\\y{2}\n"
      in
      match
        List.find_opt
          (fun (f : Strict_boundary.finding) -> f.id = "arbitrary_def")
          fs
      with
      | Some f ->
          expect (f.line = 3) (tag ^ ": line");
          expect (f.count = 2) (tag ^ ": count");
          expect (f.category = "def") (tag ^ ": category")
      | None -> expect false (tag ^ ": missing"));

  run "a commented construct is not reported" (fun tag ->
      let fs =
        Strict_boundary.scan_file ~display:"m.tex" "% \\def\\x{1}\nx\n"
      in
      expect (fs = []) (tag ^ ": " ^ String.concat "," (ids fs)));

  run "line numbers survive a multi-line comment before the construct"
    (fun tag ->
      let fs =
        Strict_boundary.scan_file ~display:"m.tex"
          "% a\n\
           % b\n\
           \\begin{verbatim}\n\
           \\def\n\
           \\end{verbatim}\n\
           \\newif\\iffoo\n"
      in
      (* \newif\iffoo is two findings: the definer and the conditional name it
         creates. The \def inside the verbatim block is none. *)
      expect
        (ids fs = [ "newif"; "if_other" ])
        (tag ^ ": " ^ String.concat "," (ids fs));
      List.iter
        (fun (f : Strict_boundary.finding) ->
          expect (f.line = 6) (tag ^ ": line " ^ string_of_int f.line))
        fs);

  run "bare \\@ and \\iff are not boundary constructs" (fun tag ->
      let fs =
        Strict_boundary.scan_file ~display:"m.tex" "e.g.\\@ and $a \\iff b$\n"
      in
      expect (fs = []) (tag ^ ": " ^ String.concat "," (ids fs)));

  run "the A.1.4 additions are reported" (fun tag ->
      let src =
        "\\makeatletter\\@foo\\expandafter\\x\\ifthenelse{}{}{}\\whiledo\n\
         \\ExplSyntaxOn\\NewDocumentCommand\\write\\ifpdf\\catcode\n"
      in
      let cs = cats (Strict_boundary.scan_file ~display:"m.tex" src) in
      List.iter
        (fun c -> expect (List.mem c cs) (tag ^ ": missing category " ^ c))
        [
          "atletter";
          "expandafter";
          "conditional";
          "loop";
          "expl3";
          "xparse";
          "write";
          "foreign";
        ]);

  run "style files are reported, not scanned" (fun tag ->
      let fs =
        Strict_boundary.scan_files ~base_dir:"/p"
          [ ("/p/main.tex", "x"); ("/p/my.cls", "\\def\\x{}\\catcode") ]
      in
      expect (ids fs = [ "local_cls" ]) (tag ^ ": " ^ String.concat "," (ids fs));
      match fs with
      | [ f ] -> expect (f.file = "my.cls") (tag ^ ": display " ^ f.file)
      | _ -> ());

  run "why_not_strict ends with the M0 reason and has at most three" (fun tag ->
      let fs =
        Strict_boundary.scan_file ~display:"m.tex"
          "\\def\\x{}\\let\\a\\b\\catcode\\ifx\n"
      in
      let w = Strict_boundary.why_not_strict fs in
      expect (List.length w = 3) (tag ^ ": length");
      expect (List.nth w 2 = Verdict.m0_boundary) (tag ^ ": M0 last");
      expect ((List.hd w).b_kind = "foreign") (tag ^ ": foreign first");
      expect
        (Strict_boundary.why_not_strict [] = [ Verdict.m0_boundary ])
        (tag ^ ": empty scan gives only M0"))

(* ── Closure scope and the CLI surface ───────────────────────────── *)

let exe = Filename.concat (Filename.dirname Sys.argv.(0)) "validators_cli.exe"

let run_cli args =
  let cmd =
    String.concat " " (List.map Filename.quote (exe :: args)) ^ " 2>/dev/null"
  in
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_string buf (input_line ic);
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  let code =
    match Unix.close_process_in ic with Unix.WEXITED c -> c | _ -> -1
  in
  (Buffer.contents buf, code)

let tmpdir () =
  let d = Filename.temp_file "test_verdict_" "" in
  Sys.remove d;
  Sys.mkdir d 0o755;
  d

let write dir name content =
  let p = Filename.concat dir name in
  let oc = open_out_bin p in
  output_string oc content;
  close_out oc;
  p

let lines s = String.split_on_char '\n' s |> List.filter (fun l -> l <> "")

(* Check the frozen surface of one --compile-check output and return the tier
   line's fields. *)
let check_surface tag out code =
  let ls = lines out in
  let token_lines =
    List.filter
      (fun l -> starts_with l "READY\t" || starts_with l "NOT-READY\t")
      ls
  in
  expect (List.length token_lines = 1) (tag ^ ": exactly one token line");
  let tok = match token_lines with l :: _ -> l | [] -> "" in
  expect
    ((code = 0 && starts_with tok "READY\t")
    || (code = 1 && starts_with tok "NOT-READY\t"))
    (tag ^ ": exit code matches the token line");
  let model = List.filter (fun l -> starts_with l "MODEL-CONNECTED\t") ls in
  expect (List.length model = 1) (tag ^ ": one MODEL-CONNECTED line");
  (match model with
  | l :: _ -> (
      match String.split_on_char '\t' l with
      | _ :: st :: tier :: _ ->
          expect
            (st = "PREMISE-CERTIFIED" || st = "PREMISE-REJECTED")
            (tag ^ ": frozen state token " ^ st);
          expect (starts_with tier "tier=") (tag ^ ": tier= field")
      | _ -> expect false (tag ^ ": malformed MODEL-CONNECTED"))
  | [] -> ());
  expect (not (contains out "PROVEN")) (tag ^ ": M0 output never says PROVEN");
  let idx p =
    let rec go i = function
      | [] -> -1
      | l :: r -> if p l then i else go (i + 1) r
    in
    go 0 ls
  in
  let i_tok = idx (fun l -> l = tok)
  and i_tier = idx (fun l -> starts_with l "TIER\t") in
  expect
    (i_tier > i_tok && i_tok >= 0)
    (tag ^ ": the TIER line follows the token line");
  match List.find_opt (fun l -> starts_with l "TIER\t") ls with
  | Some l -> String.split_on_char '\t' l
  | None ->
      expect false (tag ^ ": no TIER line");
      []

let () =
  run "closure scan sees a \\def in an \\input child (not only the root)"
    (fun tag ->
      let d = tmpdir () in
      let root =
        write d "main.tex"
          "\\documentclass{article}\n\
           \\begin{document}\n\
           \\input{child}\n\
           \\end{document}\n"
      in
      ignore (write d "child.tex" "Text.\n\n\\def\\R{\\mathbb R}\n");
      ignore (write d "mine.sty" "\\def\\x{}\n");
      let src =
        let ic = open_in_bin root in
        let s = really_input_string ic (in_channel_length ic) in
        close_in ic;
        s
      in
      match Project_model.of_root root with
      | Error _ -> expect false (tag ^ ": setup")
      | Ok proj ->
          let fs = Strict_boundary.scan proj ~root_src:src in
          let child =
            List.find_opt
              (fun (f : Strict_boundary.finding) -> f.file = "child.tex")
              fs
          in
          (match child with
          | Some f ->
              expect (f.id = "arbitrary_def") (tag ^ ": id");
              expect (f.line = 3) (tag ^ ": line")
          | None -> expect false (tag ^ ": child \\def not found"));
          (* mine.sty is not loaded, so it is not in the closure. *)
          expect
            (not
               (List.exists
                  (fun (f : Strict_boundary.finding) -> f.file = "mine.sty")
                  fs))
            (tag ^ ": unloaded style file is not reported"));

  run "CLI: READY document keeps its frozen tokens and gains a heuristic tier"
    (fun tag ->
      let d = tmpdir () in
      let p =
        write d "ok.tex"
          "\\documentclass{article}\n\
           \\def\\R{\\mathbb R}\n\
           \\begin{document}\n\
           Hello.\n\
           \\end{document}\n"
      in
      let out, code = run_cli [ "--compile-check"; p ] in
      expect (code = 0) (tag ^ ": exit 0");
      match check_surface tag out code with
      | [ _; tier; kind; head ] ->
          expect (tier = "heuristic") (tag ^ ": tier " ^ tier);
          expect (kind = "LIKELY-OK") (tag ^ ": kind " ^ kind);
          expect
            (contains head "LIKELY OK (heuristic; premise-certified)")
            (tag ^ ": headline " ^ head);
          expect
            (contains out "\\newcommand{\\R}{\\mathbb R}")
            (tag ^ ": def nudge shown")
      | _ -> expect false (tag ^ ": tier line fields"));

  run "CLI: an LP-Foreign document renders FOREIGN, not a parse failure"
    (fun tag ->
      let d = tmpdir () in
      let p =
        write d "f.tex"
          "\\documentclass{article}\n\
           \\begin{document}\n\
           \\catcode`\\@=11\n\
           x\n\
           \\end{document}\n"
      in
      let out, code = run_cli [ "--compile-check"; p ] in
      expect (code = 1) (tag ^ ": exit 1 unchanged");
      (match check_surface tag out code with
      | [ _; tier; kind; _ ] ->
          expect (tier = "foreign") (tag ^ ": tier " ^ tier);
          expect (kind = "FOREIGN") (tag ^ ": kind " ^ kind)
      | _ -> expect false (tag ^ ": tier line"));
      expect (contains out "  T0 LP-Foreign construct(s) in ") (tag ^ ": reason");
      expect
        (not (contains out "T0 parse fails"))
        (tag ^ ": not a parse failure"));

  run "CLI: --require-proof exits 4 in every argument order (M0)" (fun tag ->
      let d = tmpdir () in
      let p =
        write d "ok.tex"
          "\\documentclass{article}\n\
           \\begin{document}\n\
           Hello.\n\
           \\end{document}\n"
      in
      List.iter
        (fun args ->
          let _, code = run_cli args in
          expect (code = 4) (tag ^ ": " ^ String.concat " " args))
        [
          [ "--compile-check"; "--require-proof"; p ];
          [ "--require-proof"; "--compile-check"; p ];
          [ "--compile-check"; p; "--require-proof" ];
        ];
      let _, code = run_cli [ "--compile-check"; p ] in
      expect (code = 0) (tag ^ ": without the flag the exit code is unchanged"))

(* ── The standing battery (corpora/strict_battery) ──────────────── *)

let battery_dir = "../../corpora/strict_battery"

let () =
  run "battery: every document renders heuristic, never PROVEN, in M0"
    (fun tag ->
      let files =
        if Sys.file_exists battery_dir then
          Sys.readdir battery_dir
          |> Array.to_list
          |> List.filter (fun f -> Filename.check_suffix f ".tex")
          |> List.sort compare
        else []
      in
      expect (List.length files >= 12) (tag ^ ": at least 12 battery documents");
      List.iter
        (fun f ->
          let p = Filename.concat battery_dir f in
          let out, code = run_cli [ "--compile-check"; p ] in
          (match check_surface (tag ^ " " ^ f) out code with
          | [ _; tier; kind; _ ] ->
              expect (tier = "heuristic") (tag ^ " " ^ f ^ ": tier " ^ tier);
              expect
                ((code = 0 && kind = "LIKELY-OK")
                || (code = 1 && kind = "LIKELY-FAIL"))
                (tag ^ " " ^ f ^ ": kind " ^ kind)
          | _ -> expect false (tag ^ " " ^ f ^ ": tier line"));
          let _, rp = run_cli [ "--compile-check"; "--require-proof"; p ] in
          expect (rp = 4) (tag ^ " " ^ f ^ ": --require-proof exits 4"))
        files)

let () = finalise "verdict"
