(** Pre-compile readiness contract. See [compile_contract.mli]. *)

type reason =
  | T0_parse_fails of { file : string; message : string }
  | T1_expansion_fails of string
  | T2_project_not_closed of [ `Cycle_in_build_graph | `Missing_file of string ]
  | T3_profile_incompatible of { feature : string; profile : string }
  | T4_semantic_incoherent of
      [ `Duplicate_labels of string list | `Missing_bib_entries of string list ]
  | T5_rule_violations of string list
  | T_structural_fatal of string list
  | T_input_too_large of int
  | T_artefact_fatal of { file : string; message : string }

type ready_check_result = Ready | NotReady of reason list

(* Feature→profile compatibility table. Mirrors the data in
   specs/v26/compilation_profiles.yaml but encoded here for runtime access
   without a yaml dep. *)
let feature_compatible (feature : Project_model.declared_feature)
    (engine : Project_model.engine_profile) : bool =
  let open Project_model in
  match (feature, engine) with
  (* UTF8_inputenc works everywhere except ptex_uptex (uses its own enc) *)
  | UTF8_inputenc, Ptex_uptex -> false
  | UTF8_inputenc, _ -> true
  (* UTF8_direct requires xe/lua *)
  | UTF8_direct, (Xelatex | Lualatex) -> true
  | UTF8_direct, _ -> false
  (* Unicode math requires unicode-aware engine *)
  | Unicode_math, (Xelatex | Lualatex) -> true
  | Unicode_math, _ -> false
  (* OpenType fonts need xelatex or lualatex *)
  | Opentype_fonts, (Xelatex | Lualatex) -> true
  | Opentype_fonts, _ -> false
  (* Lua scripting: only lualatex *)
  | Lua_scripting, Lualatex -> true
  | Lua_scripting, _ -> false
  (* Japanese CJK: only ptex_uptex in v26.2 scope *)
  | Japanese_cjk, Ptex_uptex -> true
  | Japanese_cjk, _ -> false
  (* Everything else is universally supported in v26.2 *)
  | _, _ -> true

let t3_check (proj : Project_model.t) : reason list =
  let engine = proj.Project_model.engine in
  List.filter_map
    (fun feat ->
      if feature_compatible feat engine then None
      else
        Some
          (T3_profile_incompatible
             {
               feature = Project_model.feature_to_string feat;
               profile = Project_model.engine_to_string engine;
             }))
    proj.Project_model.declared_features

let t2_check (proj : Project_model.t) : reason list =
  let g = Build_graph.of_project proj in
  let missing =
    List.filter_map
      (fun (f : Project_model.file_entry) ->
        (* v27.1.62 (R7-4): a DIRECTORY satisfies [Sys.file_exists] but kpathsea
           cannot \input it — pdflatex fatals "File not found". Require a
           non-directory (regular file / symlink-to-file). Guarded so
           [is_directory] is only reached when the path exists. *)
        if Sys.file_exists f.path && not (Sys.is_directory f.path) then None
        else Some f.path)
      (Project_model.all_files proj)
  in
  let rs =
    if missing = [] then []
    else List.map (fun p -> T2_project_not_closed (`Missing_file p)) missing
  in
  (* [Build_graph.is_acyclic] only sees ARTEFACT edges (tex→aux→pdf), which are
     acyclic by construction. An \input/\include CYCLE (a→b→a) closes through a
     child the single-level [of_root] never scans, so it needs a recursive
     source-level pass. pdflatex fatals on such a cycle ("TeX capacity exceeded
     [text input levels]"). R7-4. *)
  let root_path = (Project_model.root_file proj).path in
  if
    (not (Build_graph.is_acyclic g))
    || Project_model.has_include_cycle root_path
  then T2_project_not_closed `Cycle_in_build_graph :: rs
  else rs

(* T4 IS NO LONGER A BLOCKING PREMISE (OPEN-008).

   [t4_check] reported exactly ONE condition — duplicate \label names read from
   the .aux — and a duplicate label is NOT a compile failure. Measured against
   the pinned oracle (pdfTeX 3.141592653-2.6-1.40.29) under BOTH protocols:

   \section{One}\label{same} \section{Two}\label{same} \ref{same}
   -interaction=nonstopmode -halt-on-error -> rc 0, PDF produced
   -interaction=nonstopmode -> rc 0, PDF produced log: LaTeX Warning: Label
   `same' multiply defined.

   A WARNING. The check was rejecting documents pdflatex accepts: on the
   200-paper real corpus (corpora/real_roots) T4 was the ONLY blocking reason
   for NINE documents and all nine compile.

   The deeper reason it was never licensed: [project_wf_dec_sound] is
   ONE-DIRECTIONAL. dec = true IMPLIES compile_safe; dec = false implies
   NOTHING. So an unmet nodup premise never justified a REJECTION — it only
   failed to justify a certification. Treating "the model cannot certify this"
   as "this will not compile" is the inversion this removes.

   The [T4_semantic_incoherent] constructor and its renderer are KEPT: they are
   exported in the .mli, and the aux-coherence idea is sound if it is ever aimed
   at something pdflatex actually rejects. Nothing constructs it today.
   `Missing_bib_entries was ALWAYS unreachable — no code ever built it. *)

(* T0 (v27.1.52): parser acceptance + language-profile gate, run against the
   real root source. Two independent failure modes, both genuine:

   1. LP-Foreign: [Language_profile.classify_source] demotes the document to the
   LP-Foreign tier (e.g. \write18/shell-escape, \directlua, arbitrary \catcode
   surgery). Such constructs leave the supported subset entirely, so no
   compile-readiness promise can be made — NOT-READY.

   2. Parse failure: [Parser_l2.parse_located] records a hard structural error
   (unclosed inline/display/paren math, unclosed environment, \end without a
   matching \begin, unclosed \verb, nesting-depth blow-up). The first such
   error's message + byte offset is surfaced verbatim.

   Scope honesty: the L2 recursive-descent parser is error-RECOVERING, so a
   [parse_located] with zero errors means "no error the parser detected", not
   "provably well-formed". Structural faults the parser does not itself flag —
   most notably an unbalanced brace group, which it silently closes at EOF — are
   caught by T5 (DELIM-001) instead. T0 and T5 are therefore complementary. *)
(* T0 core, parametrised by the parse error list so callers can supply a parse
   they already performed (the fast kernel parses exactly once and shares the
   result between T0 and T5's PRT context). [parse_errors] is only consulted on
   the LP_Core/LP_Extended branch — on LP_Foreign we short-circuit before any
   parse would be needed. *)
let t0_check_with_errors ~(source : string)
    ~(parse_errors : (string * Parser_l2.loc) list) (proj : Project_model.t) :
    reason list =
  let file = (Project_model.root_file proj).path in
  match Language_profile.classify_source source with
  | Language_profile.LP_Foreign, feats ->
      let describe (f : Unsupported_feature.t) =
        Printf.sprintf "%s (line %d)" f.message f.line
      in
      let msg =
        match feats with
        | [] -> "document uses LP-Foreign constructs (unsupported subset)"
        | fs ->
            "LP-Foreign construct(s): "
            ^ String.concat "; " (List.map describe fs)
      in
      [ T0_parse_fails { file; message = msg } ]
  | (LP_Core | LP_Extended), _ -> (
      match List.rev parse_errors with
      | [] -> []
      | (msg, (loc : Parser_l2.loc)) :: _ ->
          [
            T0_parse_fails
              {
                file;
                message =
                  Printf.sprintf "%s (line %d, offset %d)" msg loc.line
                    loc.offset;
              };
          ])

let t0_check ~(source : string) (proj : Project_model.t) : reason list =
  let _nodes, parse_errors = Parser_l2.parse_located source in
  (* OPEN-010: same exoneration as the fast path — see the note there. *)
  let parse_errors =
    Validators.exonerate_benign_end_in_group ~source parse_errors
  in
  t0_check_with_errors ~source ~parse_errors proj

(* T1: not runtime-checked at this layer. Bounded-macro-registry determinism /
   acyclicity is enforced by [User_macro_registry] at analysis time; a dedicated
   T1 runtime probe is v26.3+ territory. Kept as a no-op so the readiness result
   never silently claims a T1 property it did not verify. *)
let t1_check (_ : Project_model.t) : reason list = []

(* T5 (v27.1.52): rule safety — run the full validator set on the real source
   and flag any COMPILE-BLOCKING diagnostic that fired at [Error] severity.

   "Compile-blocking" is deliberately NARROWER than "Error severity": many
   Error-level rules are completeness/style faults that pdflatex compiles
   through anyway (e.g. DOC-001 "missing \maketitle"). Flagging every Error
   would make a clean article NOT-READY. The compile-blocking set is the rule
   families whose firing corresponds to a structural fault the engine cannot
   recover from:

   - DELIM-* mismatched / extra / stray braces & delimiters - ENC-* invalid byte
   / encoding faults that break tokenization - PRT-* parse-reliability rules
   (fire only when the L2 parser itself recorded a hard error, i.e. the T0 parse
   surface)

   Any Error result whose id begins with one of these prefixes is reported. This
   set is intentionally conservative: a false NOT-READY (over-flagging) is safe;
   a false READY on a genuinely broken document is not.

   NOTE (differential validation, scripts/tools/diff_compile_check.sh):
   DELIM-001 ("Unmatched delimiters { … }") over-triggers on a BARE unclosed
   open group ([{x\end{document}]), which pdflatex auto-closes and compiles — a
   false NOT-READY. It was tempting to exclude DELIM-001, BUT the same rule also
   fires on an unclosed group swallowed by a MACRO ARGUMENT
   ([\textbf{oops\end{document}]), which genuinely FAILS (the \end{document} is
   consumed into the argument). DELIM-001 cannot cheaply distinguish the two,
   and a false READY on the fatal case is the dangerous direction — so DELIM-001
   STAYS compile-blocking. The bare-[{x] over-rejection is an accepted SAFE
   false-NOT-READY.

   SINGLE SOURCE OF TRUTH (v27.1.60 audit hardening): the compile-blocking
   predicate lives in [Validators.is_compile_blocking] (backed by
   [Validators.compile_blocking_ids] — an explicit id list since v27.1.63, not a
   prefix test, so a rule can no longer name itself into the compile verdict).
   We delegate to it rather than keep a private copy, so any future id-level
   compile-blocking promotion or demotion there is picked up here automatically
   instead of being a silent no-op. *)

let t5_check ~(source : string) (_ : Project_model.t) : reason list =
  let results = Validators.run_all source in
  let blocking =
    List.filter_map
      (fun (r : Validators.result) ->
        if r.severity = Validators.Error && Validators.is_compile_blocking r.id
        then Some r.id
        else None)
      results
  in
  match blocking with [] -> [] | ids -> [ T5_rule_violations ids ]

(* FAST T5 (v27.1.59): run ONLY the compile-blocking rules via
   [Validators.run_compile_blocking] instead of all ~641 rules, then keep the
   same Error-severity + prefix filter. This is verdict-identical to [t5_check]
   for the compile-blocking set (see [Validators.run_subset]'s equivalence
   argument): the subset reproduces the one piece of shared context those rules
   read (Partial_context, from the SHARED single parse we thread in via
   [parse_errors]), and _resolve_conflicts never affects this subset. Reason
   constructors/messages are byte-identical to the full path. *)
let t5_check_fast ~(source : string)
    ~(parse_errors : (string * Parser_l2.loc) list) (_ : Project_model.t) :
    reason list =
  let results = Validators.run_compile_blocking ~parse_errors source in
  let blocking =
    List.filter_map
      (fun (r : Validators.result) ->
        if r.severity = Validators.Error && Validators.is_compile_blocking r.id
        then Some r.id
        else None)
      results
  in
  match blocking with [] -> [] | ids -> [ T5_rule_violations ids ]

(* Structural-fatal compile-gate (v27.1.60): precise, comment/verbatim-aware
   detectors that fire IFF pdflatex genuinely fails with no output PDF on the
   targeted deterministic-structural conditions (double super/subscript in math,
   misplaced alignment tab &, no \documentclass, \usepackage after
   \begin{document}). Pure function of the source, so it is byte-identical on
   the fast and full branches (fast==full parity holds trivially). This is the
   soundness spine of --compile-check: catching these closes the false-READY
   holes (e.g. $a^b^c$) that the imprecise ADVISORY lint rules could not. *)
let structural_fatal_check ~(source : string) ~(closure_source : string)
    ~(self_collision : string option) : reason list =
  let reasons =
    Compile_gate_checks.structural_fatal_reasons source
    @ (match self_collision with Some m -> [ m ] | None -> [])
    (* The thmtools shared-counter detector (OPEN-002) runs on the
       CLOSURE-RESOLVED source, because the load and the declarations routinely
       live in different files. It is kept OUT of [structural_fatal_reasons] so
       it runs exactly once, on the right string; on a single-file project the
       closure source IS the root source, so nothing changes there. *)
    @ (match
         Compile_gate_checks.thmtools_counter_collision_fatal closure_source
       with
      | Some m -> [ m ]
      | None -> [])
    @
    (* The tabu text-mode detector (OPEN-031) also runs on the closure:
       2507.10809v1's five text-mode envs live in an \input child (C-32). *)
    match Compile_gate_checks.tabu_textmode_fatal closure_source with
    | Some m -> [ m ]
    | None -> []
  in
  match reasons with [] -> [] | reasons -> [ T_structural_fatal reasons ]

(* Closure-resolved source: the root with each LIVE `\input{..}`/`\include{..}`
   replaced in place by its child's contents, recursively. Built for detectors
   whose pattern spans files (the thmtools load in `preamble.tex`, the
   declarations in the root — 6 of the OPEN-002 rule's first-derivation false
   negatives were exactly this shape).

   SOUND BY DEGRADATION, in the same sense as [has_include_cycle]: comments/
   verbatim/urls are blanked before scanning for directives (a commented `%
   \input foo` — the tcilatex trap — must not splice), an unresolvable or
   non-existent child leaves the directive text in place, a visited-set stops
   cycles, and fuel bounds pathological fan-out. Every failure mode collapses to
   "less inlining", which for the consuming detector means UNDER-detection — the
   status-quo false-READY, never a phantom fire.

   ZERO IO on single-file projects: if the blanked root contains no live
   directive, the root string is returned untouched — so the benchmarked
   readiness paths, whose inputs are single files, never pay for this. *)
(* The closure walk, generalised (v27.1.64, SC detector): one pre-order pass
   yielding SEGMENTS of (file_key, raw_text) in TeX's reading order, consumed
   two ways — concatenated into the spliced string for the thmtools detector
   ([read_closure_source], unchanged public behaviour), and scanned per-file for
   the self-collision detector ([closure_self_collision]).

   Splices, in addition to the original live `\input{..}`/`\include{..}`: *
   LOCAL `.sty` loaded by `\usepackage`/`\RequirePackage` (comma lists honoured
   — only names with a local `<name>.sty` splice; the DIRECTIVE TEXT IS KEPT and
   the file content inserted after it, so other names in the same list, and
   position-sensitive consumers, are unaffected); * a LOCAL `.cls` named by
   `\documentclass`. 4 of the SC rule's 10 corpus true positives are reachable
   only through a local .sty (icml2025.sty's `\RequirePackage{algorithm}`), and
   4 residual `\c@` fatals of the thmtools detector are cls/sty-mediated — this
   closes both.

   Same soundness-by-degradation as before: directives found on a
   comment-blanked mask (a commented `% \input foo` cannot splice), visited set,
   fuel (files/depth), unresolvable child leaves the text alone; every failure
   mode is less inlining = under-detection. Fast path unchanged: a root with no
   live directive costs zero IO. *)
let closure_segments (proj : Project_model.t) ~(root_src : string) :
    (string * string) list =
  let max_files = 48 and max_depth = 6 in
  let base_dir = Filename.dirname (Project_model.root_file proj).path in
  let visited = Hashtbl.create 8 in
  let files_read = ref 0 in
  let blank src =
    let b = Bytes.of_string src in
    List.iter
      (fun (a, e) ->
        for k = a to e - 1 do
          if k >= 0 && k < Bytes.length b then Bytes.set b k ' '
        done)
      (Validators_common.find_verbatim_comment_url_ranges src);
    Bytes.unsafe_to_string b
  in
  let read_file p =
    try
      let ic = open_in_bin p in
      Fun.protect
        ~finally:(fun () -> close_in_noerr ic)
        (fun () -> Some (really_input_string ic (in_channel_length ic)))
    with Sys_error _ -> None
  in
  let resolve_with exts raw =
    let raw = String.trim raw in
    if raw = "" || String.contains raw '\\' then None
    else
      let cands =
        if List.exists (fun e -> Filename.check_suffix raw e) exts then [ raw ]
        else List.map (fun e -> raw ^ e) exts
      in
      List.find_map
        (fun c ->
          let p = Filename.concat base_dir c in
          if Sys.file_exists p && not (Sys.is_directory p) then Some p else None)
        cands
  in
  let segs = ref [] in
  let push key text = if text <> "" then segs := (key, text) :: !segs in
  let claim path =
    if (not (Hashtbl.mem visited path)) && !files_read < max_files then (
      Hashtbl.replace visited path ();
      incr files_read;
      read_file path)
    else None
  in
  (* Read a brace group on the MASK starting at '{' at [j]; returns (raw_inner,
     past). Flat — a nested '{' inside a filename is not LaTeX. *)
  let group_at src masked j =
    let n = String.length masked in
    if j >= n || masked.[j] <> '{' then None
    else
      let k = ref (j + 1) in
      while !k < n && masked.[!k] <> '}' do
        incr k
      done;
      if !k >= n then None
      else Some (String.sub src (j + 1) (!k - j - 1), !k + 1)
  in
  let rec walk depth key src =
    if depth > max_depth then push key src
    else
      let masked = blank src in
      let n = String.length masked in
      let last = ref 0 in
      let i = ref 0 in
      while !i < n do
        let pos = !i in
        let starts pfx =
          let pl = String.length pfx in
          pos + pl <= n && String.sub masked pos pl = pfx
        in
        (* replace-style: \input{x} / \include{x} *)
        let replace_cl =
          if starts "\\input{" then Some 7
          else if starts "\\include{" then Some 9
          else None
        in
        (* keep-style: \usepackage[..]{a,b} / \RequirePackage /
           \documentclass *)
        let keep_kind =
          if starts "\\usepackage" then Some (11, [ ".sty" ])
          else if starts "\\RequirePackage" then Some (15, [ ".sty" ])
          else if starts "\\documentclass" then Some (14, [ ".cls" ])
          else None
        in
        match (replace_cl, keep_kind) with
        | Some cl, _ -> (
            let j = ref (pos + cl) in
            while !j < n && masked.[!j] <> '}' do
              incr j
            done;
            if !j >= n then i := pos + 1
            else
              let raw = String.sub src (pos + cl) (!j - pos - cl) in
              match resolve_with [ ".tex" ] raw with
              | Some path -> (
                  match claim path with
                  | Some child ->
                      push key (String.sub src !last (pos - !last));
                      walk (depth + 1) path child;
                      last := !j + 1;
                      i := !j + 1
                  | None -> i := !j)
              | None -> i := !j)
        | None, Some (cl, exts) -> (
            (* skip optional [..] on the mask, then the {names} group *)
            let j = ref (pos + cl) in
            while
              !j < n
              && (masked.[!j] = ' '
                 || masked.[!j] = '\t'
                 || masked.[!j] = '\n'
                 || masked.[!j] = '\r')
            do
              incr j
            done;
            if !j < n && masked.[!j] = '[' then
              while !j < n && masked.[!j] <> ']' do
                incr j
              done;
            if !j < n && masked.[!j] = ']' then incr j;
            while
              !j < n
              && (masked.[!j] = ' '
                 || masked.[!j] = '\t'
                 || masked.[!j] = '\n'
                 || masked.[!j] = '\r')
            do
              incr j
            done;
            match group_at src masked !j with
            | Some (names, past) ->
                let locals =
                  String.split_on_char ',' names
                  |> List.filter_map (resolve_with exts)
                in
                if locals = [] then i := past
                else (
                  (* KEEP the directive text, splice each local file after. *)
                  push key (String.sub src !last (past - !last));
                  List.iter
                    (fun path ->
                      match claim path with
                      | Some child -> walk (depth + 1) path child
                      | None -> ())
                    locals;
                  last := past;
                  i := past)
            | None -> i := pos + 1)
        | None, None -> incr i
      done;
      push key (String.sub src !last (String.length src - !last))
  in
  (* Fast path: nothing resolvable in the blanked root ⇒ one segment, no IO
     beyond the (cheap) local-file existence probes at directive sites. *)
  walk 0 "<root>" root_src;
  List.rev !segs

let read_closure_source (proj : Project_model.t) ~(root_src : string) : string =
  match closure_segments proj ~root_src with
  | [ (_, only) ] -> only
  | segs -> String.concat "\n" (List.map snd segs)

(* The SC (self-collision) verdict over the closure: scan each segment with ITS
   FILE's carried scanner state — per-file depths, splice-order events — exactly
   the contract [sc_scan_segment] documents. Segments are
   comment/verbatim/url-blanked here because the scanner itself is range-naive;
   a guard or declaration inside a comment must not count. *)
let closure_self_collision (proj : Project_model.t) ~(root_src : string) :
    string option =
  let blank src =
    let b = Bytes.of_string src in
    List.iter
      (fun (a, e) ->
        for k = a to e - 1 do
          if k >= 0 && k < Bytes.length b then Bytes.set b k ' '
        done)
      (Validators_common.find_verbatim_comment_url_ranges src);
    Bytes.unsafe_to_string b
  in
  let states : (string, Compile_gate_checks.sc_state) Hashtbl.t =
    Hashtbl.create 8
  in
  let events = ref [] in
  List.iter
    (fun (key, seg) ->
      let st =
        Option.value
          (Hashtbl.find_opt states key)
          ~default:Compile_gate_checks.sc_initial
      in
      let st', evs = Compile_gate_checks.sc_scan_segment st (blank seg) in
      Hashtbl.replace states key st';
      events := !events @ [ evs ])
    (closure_segments proj ~root_src);
  Compile_gate_checks.self_collision_verdict (List.concat !events)

(* Read the root .tex source for T0/T5 if the caller did not supply it. On a
   read failure we surface a T0 reason rather than silently passing. *)
let read_root_source (proj : Project_model.t) : (string, string) result =
  let path = (Project_model.root_file proj).path in
  try
    let ic = open_in_bin path in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () -> Ok (really_input_string ic (in_channel_length ic)))
  with Sys_error msg -> Error msg

let check_ready_to_compile ?(fast = true) ?aux_path ?source
    (proj : Project_model.t) (_profile : Build_profile.t) : ready_check_result =
  let source_result =
    match source with Some s -> Ok s | None -> read_root_source proj
  in
  (* Structural-fatal reasons are a pure function of the (closure-resolved)
     source and are computed ONCE, the SAME way on both the fast and full
     branches — fast==full parity is therefore preserved trivially. *)
  let tsf =
    match source_result with
    | Ok src ->
        let closure_source = read_closure_source proj ~root_src:src in
        let self_collision = closure_self_collision proj ~root_src:src in
        structural_fatal_check ~source:src ~closure_source ~self_collision
    | Error _ -> []
  in
  let t0, t5 =
    match source_result with
    | Ok src ->
        if fast then
          (* FAST readiness kernel (v27.1.59): parse ONCE and share the parse
             error list between T0's structural-error check and T5's PRT
             context, and run ONLY the 36 compile-blocking rules.
             Verdict-identical to the full path below. *)
          let _nodes, parse_errors = Parser_l2.parse_located src in
          (* OPEN-010: the SAME benign end-in-group exoneration as the full path
             (run_all/run_subset filter internally) — fast==full parity depends
             on filtering here too. *)
          let parse_errors =
            Validators.exonerate_benign_end_in_group ~source:src parse_errors
          in
          ( t0_check_with_errors ~source:src ~parse_errors proj,
            t5_check_fast ~source:src ~parse_errors proj )
        else
          (* FULL path: original behaviour — T0 parses independently and T5 runs
             every registered rule then filters. Kept as the safety fallback and
             the differential/correctness-gate reference. *)
          (t0_check ~source:src proj, t5_check ~source:src proj)
    | Error msg ->
        ( [
            T0_parse_fails
              { file = (Project_model.root_file proj).path; message = msg };
          ],
          [] )
  in
  (* v27.1.62 (Bug 3): above the validator input-size cap, [run_all]/
     [run_subset] silently return no compile-blocking results, so T5 and the
     structural-fatal gate would pass VACUOUSLY — an 11 MB document with an
     unbalanced \left( would be judged READY. Emit a conservative NOT-READY
     above the cap instead. This can only ADD a NOT-READY, never a
     false-READY. *)
  let tcap =
    match source_result with
    | Ok src when String.length src > Validators.max_input_bytes ->
        [ T_input_too_large (String.length src) ]
    | _ -> []
  in
  (* v27.1.62 (R7-5): sibling ARTEFACTS pdflatex reads as LaTeX — the [.aux]
     (from a previous run, read at \begin{document}) and the [.bbl] (read at
     \bibliography{..}). An unclosed brace group in either is the deterministic
     "! File ended while scanning" fatal, invisible to a check that only reads
     the root .tex. A valid tool-generated artefact is always balanced, so this
     can only ADD a NOT-READY. *)
  let read_file_opt p =
    try
      let ic = open_in_bin p in
      Fun.protect
        ~finally:(fun () -> close_in_noerr ic)
        (fun () -> Some (really_input_string ic (in_channel_length ic)))
    with Sys_error _ -> None
  in
  let artefact_fatal file kind =
    if Sys.file_exists file && not (Sys.is_directory file) then
      match read_file_opt file with
      | Some content when Compile_gate_checks.unbalanced_open_brace content ->
          [
            T_artefact_fatal
              {
                file;
                message =
                  Printf.sprintf
                    "unbalanced { in %s (corrupt/truncated): ! File ended \
                     while scanning"
                    kind;
              };
          ]
      | _ -> []
    else []
  in
  let tartefact =
    let aux_r =
      match aux_path with Some p -> artefact_fatal p ".aux" | None -> []
    in
    let bbl_r =
      match source_result with
      | Ok src when Compile_gate_checks.source_uses_bibliography src ->
          let bbl =
            Filename.remove_extension (Project_model.root_file proj).path
            ^ ".bbl"
          in
          artefact_fatal bbl ".bbl"
      | _ -> []
    in
    aux_r @ bbl_r
  in
  let reasons =
    t0
    @ t1_check proj
    @ t2_check proj
    @ t3_check proj
    @ t5
    @ tsf
    @ tcap
    @ tartefact
  in
  if reasons = [] then Ready else NotReady reasons

let reason_to_string = function
  | T0_parse_fails { file; message } ->
      Printf.sprintf "T0 parse fails in %s: %s" file message
  | T1_expansion_fails msg -> Printf.sprintf "T1 expansion fails: %s" msg
  | T2_project_not_closed `Cycle_in_build_graph ->
      "T2 project not closed: cycle in build graph"
  | T2_project_not_closed (`Missing_file p) ->
      Printf.sprintf "T2 project not closed: missing file %s" p
  | T3_profile_incompatible { feature; profile } ->
      Printf.sprintf
        "T3 profile incompatible: feature %s not supported by profile %s"
        feature profile
  | T4_semantic_incoherent (`Duplicate_labels ds) ->
      Printf.sprintf "T4 semantic incoherent: duplicate labels [%s]"
        (String.concat "; " ds)
  | T4_semantic_incoherent (`Missing_bib_entries es) ->
      Printf.sprintf "T4 semantic incoherent: missing bib entries [%s]"
        (String.concat "; " es)
  | T5_rule_violations ids ->
      Printf.sprintf "T5 rule violations: [%s]" (String.concat "; " ids)
  | T_structural_fatal reasons ->
      Printf.sprintf "structural-fatal (will not compile): [%s]"
        (String.concat "; " reasons)
  | T_artefact_fatal { file; message } ->
      Printf.sprintf "artefact-fatal (%s): %s" file message
  | T_input_too_large n ->
      Printf.sprintf
        "input too large (%d bytes > %d cap): compile-blocking checks cannot \
         run — conservative NOT-READY"
        n Validators.max_input_bytes
