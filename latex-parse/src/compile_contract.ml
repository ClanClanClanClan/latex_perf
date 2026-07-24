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
  if not (Build_graph.is_acyclic g) then
    T2_project_not_closed `Cycle_in_build_graph :: rs
  else rs

(* T4: if aux exists, use parsed labels to check uniqueness and that cited keys
   resolve. Otherwise fall back to no-check (source-only label analysis is v26.3
   territory). *)
let t4_check ?aux_path (_proj : Project_model.t) : reason list =
  match aux_path with
  | None -> []
  | Some path -> (
      match Aux_state.of_file path with
      | Error _ -> [] (* Can't check; don't fail *)
      | Ok aux ->
          let rs = [] in
          let rs =
            if Aux_state.labels_unique aux then rs
            else
              (* Find the actual duplicates to report. *)
              let counts = Hashtbl.create 16 in
              List.iter
                (fun (l : Aux_state.label_entry) ->
                  let c =
                    try Hashtbl.find counts l.name with Not_found -> 0
                  in
                  Hashtbl.replace counts l.name (c + 1))
                aux.labels;
              let dups =
                Hashtbl.fold
                  (fun name c acc -> if c > 1 then name :: acc else acc)
                  counts []
              in
              T4_semantic_incoherent (`Duplicate_labels dups) :: rs
          in
          rs)

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
   [Validators.compile_blocking_prefixes]). We delegate to it rather than keep a
   private copy, so any future id-level compile-blocking promotion there is
   picked up here automatically instead of being a silent no-op. *)

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
let structural_fatal_check ~(source : string) : reason list =
  match Compile_gate_checks.structural_fatal_reasons source with
  | [] -> []
  | reasons -> [ T_structural_fatal reasons ]

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
  (* Structural-fatal reasons are a pure function of the source and are computed
     the SAME way on both the fast and full branches — fast==full parity is
     therefore preserved trivially. *)
  let tsf =
    match source_result with
    | Ok src -> structural_fatal_check ~source:src
    | Error _ -> []
  in
  let t0, t5 =
    match source_result with
    | Ok src ->
        if fast then
          (* FAST readiness kernel (v27.1.59): parse ONCE and share the parse
             error list between T0's structural-error check and T5's PRT
             context, and run ONLY the 37 compile-blocking rules.
             Verdict-identical to the full path below. *)
          let _nodes, parse_errors = Parser_l2.parse_located src in
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
  let reasons =
    t0
    @ t1_check proj
    @ t2_check proj
    @ t3_check proj
    @ t4_check ?aux_path proj
    @ t5
    @ tsf
    @ tcap
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
  | T_input_too_large n ->
      Printf.sprintf
        "input too large (%d bytes > %d cap): compile-blocking checks cannot \
         run — conservative NOT-READY"
        n Validators.max_input_bytes
