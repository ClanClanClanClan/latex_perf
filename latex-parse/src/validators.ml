(* ══════════════════════════════════════════════════════════════════════
   Validators — LaTeX Perfectionist v25 rule engine
   ══════════════════════════════════════════════════════════════════════

   Naming convention for rule bindings:

   L0 rules : r_<family>_<NNN> e.g. r_typo_001, r_enc_003, r_spc_010 L1+ rules :
   l1_<family>_<NNN>_rule e.g. l1_delim_001_rule, l1_math_055_rule

   The L0 prefix was established in the initial rule batch (W01–W24); the L1
   prefix was added when the L1 layer shipped (W25–W36) to distinguish
   higher-layer rules that depend on macro expansion. Both conventions are
   intentional — a mechanical rename would risk breaking cross-references in Coq
   proofs, golden files, and specs.

   PERF NOTE (W102 audit): ~219 Re_compat.regexp calls are inside `let run`
   closures and recompile on every invocation. Hoisting them before the closure
   would avoid recompilation. Current p95=2.8ms vs 20ms gate (86% headroom), so
   this is not urgent. A future refactor should move `let re = Re_compat.regexp
   ... in` bindings before the `let run s =` line in each rule where possible.
   ══════════════════════════════════════════════════════════════════════ *)

include Validators_common
include Validators_l0
include Validators_l2
include Validators_l4_style
include Validators_l3_file
include Validators_l1
include Validators_l1_expl3
include Validators_project
include Validators_partial

(* Extend rules_class_c with TIKZ-002 from validators_l3_file (log-dependent) *)
let rules_class_c = rules_class_c @ [ r_tikz_002 ]

(* PR #241 (memo §11): split rules_style by execution_class from
   rule_contracts.yaml. STYLE-* rules are Class D (advisory) and must not appear
   on the keystroke-critical hot path. The rules_style list from
   validators_l4_style.ml also contains Class B locale rules (CE, TH, IB, LANG
   families) which MUST stay on the hot path. *)
let rules_class_d : rule list =
  List.filter
    (fun (r : rule) ->
      match Rule_contract_loader.find_opt r.id with
      | Some c -> c.execution_class = Rule_contract_loader.D
      | None -> false)
    rules_style

let rules_style_hot_path : rule list =
  List.filter
    (fun (r : rule) ->
      match Rule_contract_loader.find_opt r.id with
      | Some c -> c.execution_class <> Rule_contract_loader.D
      | None -> true (* unclassified rules default to hot-path, safer *))
    rules_style

(* Combined ENC + CHAR + SPC + VERB + CJK + CMD + MATH + LOCALE + new TYPO
   rules.

   PR #241 (memo §11): uses rules_style_hot_path (the B locale subset of
   rules_style) rather than rules_style directly. Class D rules are in
   rules_class_d and reachable only via [run_with_policy] with a policy that
   enables Class D. `proofs/ExecutionClasses.v::hot_path_excludes_cd` is now
   honoured by the runtime. *)
let rules_enc_char_spc : rule list =
  rules_enc
  @ rules_char
  @ rules_spc
  @ rules_verb
  @ rules_cjk
  @ rules_cmd
  @ [ r_typo_062; r_math_083 ]
  @ rules_locale
  @ rules_stragglers
  @ rules_l2_approx
  @ rules_l2_parser_actual
  @ rules_style_hot_path
  @ rules_l3_file
  @ rules_l1_expl3
  @ rules_user_macro
  @ rules_project
  @ rules_partial

(* ── VPD-catalogue: all 80 rules with VPD pattern annotations ──────── *)
(* This list enumerates every rule that has a corresponding entry in
   vpd_patterns.json and a soundness theorem in RegexFamily.v. Implementations
   may be hand-written or VPD-generated; the catalogue certifies that each
   rule's check function belongs to a VPD pattern family. *)
let rules_vpd_catalogue : rule list =
  (* This list is referenced by vpd_catalogue_count below and by the conflict
     test suite. It certifies that 80 rules have VPD pattern annotations and
     formal soundness proofs. *)
  [
    (* TYPO family — 56 rules *)
    r_typo_001;
    r_typo_002;
    r_typo_003;
    r_typo_004;
    r_typo_005;
    r_typo_006;
    r_typo_007;
    r_typo_008;
    r_typo_009;
    r_typo_010;
    r_typo_011;
    r_typo_012;
    r_typo_013;
    r_typo_014;
    r_typo_015;
    r_typo_016;
    r_typo_017;
    r_typo_018;
    r_typo_021;
    r_typo_022;
    r_typo_023;
    r_typo_024;
    r_typo_025;
    r_typo_026;
    r_typo_027;
    r_typo_028;
    r_typo_029;
    r_typo_030;
    r_typo_032;
    r_typo_033;
    r_typo_034;
    r_typo_035;
    r_typo_036;
    r_typo_037;
    r_typo_038;
    r_typo_039;
    r_typo_040;
    r_typo_041;
    r_typo_042;
    r_typo_043;
    r_typo_045;
    r_typo_046;
    r_typo_047;
    r_typo_048;
    r_typo_049;
    r_typo_051;
    r_typo_052;
    r_typo_053;
    r_typo_054;
    r_typo_055;
    r_typo_056;
    r_typo_057;
    r_typo_058;
    r_typo_061;
    r_typo_062;
    r_typo_063;
    (* ENC family — 24 rules *)
    r_enc_001;
    r_enc_002;
    r_enc_003;
    r_enc_004;
    r_enc_005;
    r_enc_006;
    r_enc_007;
    r_enc_008;
    r_enc_009;
    r_enc_010;
    r_enc_011;
    r_enc_012;
    r_enc_013;
    r_enc_014;
    r_enc_015;
    r_enc_016;
    r_enc_017;
    r_enc_018;
    r_enc_019;
    r_enc_020;
    r_enc_021;
    r_enc_022;
    r_enc_023;
    r_enc_024;
  ]

let vpd_catalogue_count = List.length rules_vpd_catalogue

(* ── Generation tracking (spec §5) ───────────────────────────────── *)

let _run_generation = Atomic.make 0

(* DAG validation deferred until precondition_of_rule_id is defined. PR #241
   (p1.1-#6): _dag_topo_order global ref removed. The build_dag result's
   topo_order is currently unused on the hot path; v26.2
   incremental-invalidation work (memo §9 three-plane planes) will consume it at
   that point, computing it locally from [Validator_dag.build_dag]. *)
let _dag_validated = ref false
let _dag_validate_fn : (rule list -> unit) ref = ref (fun _ -> ())

(** PR #241 (p1.2): tier gating per memo §4. When the active [Language_profile]
    tier is LP_Foreign, skip every rule whose contract declares
    [project_scope = Lp_core_or_extended]. Rules marked [Any_tier] (e.g. the
    build-coupled log rules) still fire across all tiers. LP_Core and
    LP_Extended documents get the full rule set. *)
let _filter_by_tier (rules : rule list) : rule list =
  match Language_profile.Context.get () with
  | Some Language_profile.LP_Foreign ->
      List.filter
        (fun (r : rule) ->
          match Rule_contract_loader.find_opt r.id with
          | Some c -> c.project_scope = Rule_contract_loader.Any_tier
          | None -> true)
        rules
  | _ -> rules

let get_rules () : rule list =
  let base =
    match Sys.getenv_opt "L0_VALIDATORS" with
    | Some ("1" | "true" | "pilot" | "PILOT") ->
        rules_pilot @ rules_vpd_gen @ rules_enc_char_spc @ rules_l1
    | _ -> rules_basic @ rules_enc_char_spc @ rules_l1
  in
  if not !_dag_validated then (
    _dag_validated := true;
    !_dag_validate_fn base);
  (* PR #241 (p1.1-#6): preserve original list order for deterministic severity
     ordering within families. Incremental / scheduled callers that want
     edge-driven ordering compute the topo order locally via
     [Validator_dag.build_dag].

     PR #241 (p1.2): after DAG validation, apply tier gating (memo §4). DAG
     validation runs against the unfiltered list so metadata consistency is
     enforced even for rules that won't fire in the current tier. *)
  _filter_by_tier base

(** Run all enabled validators on [src] and return fired results.

    @requires For L1 rules that inspect post-expansion commands,
    [Validators_context.set_post_commands] must have been called for the
    current thread beforehand.  If it has not been set, those rules
    silently return [None] (safe but incomplete). *)
let max_input_bytes = 10 * 1024 * 1024 (* 10 MiB — safety guard *)

let run_all (src : string) : result list =
  (* Input size guard — prevent OOM/slowdown on huge files *)
  if String.length src > max_input_bytes then (
    Printf.eprintf
      "[validators] WARNING: input size %d bytes exceeds %d byte limit; \
       truncating\n\
       %!"
      (String.length src) max_input_bytes;
    [
      {
        id = "INTERNAL-001";
        severity = Warning;
        message =
          Printf.sprintf
            "Input truncated: %d bytes exceeds %d byte safety limit"
            (String.length src) max_input_bytes;
        count = 1;
      };
    ])
  else
    (* Check cache first (spec W19) *)
    let rules = get_rules () in
    let cache = Cache_key.global () in
    let cache_key =
      Cache_key.compute_key ~source:src ~validator_count:(List.length rules)
        ~language:"auto"
    in
    match Cache_key.lookup cache cache_key with
    | Some cached_results -> cached_results
    | None ->
        (* Increment generation counter + build snapshot per spec §5 *)
        let gen = Atomic.fetch_and_add _run_generation 1 in
        let parent_ver =
          Layer_sync.mk_version ~gen ~parent_gen:(max 0 (gen - 1))
        in
        let child_ver = Layer_sync.advance parent_ver in
        let snap =
          Layer_sync.create_snapshot
            [
              { Layer_sync.layer = L0; version = parent_ver; data = "lexer" };
              { Layer_sync.layer = L1; version = child_ver; data = "expander" };
            ]
        in
        if not (Layer_sync.is_consistent snap) then
          Printf.eprintf
            "[validators] WARNING: snapshot inconsistency at gen %d\n%!" gen;
        (* Build semantic state for L3 validators (spec W53-57) *)
        let sem = Semantic_state.analyze src in
        Semantic_state.set_state sem;
        (* Build partial document state for PRT validators (WS5) *)
        let _parse_nodes, parse_errors = Parser_l2.parse_located src in
        let pdoc = Partial_cst.classify src parse_errors in
        Partial_context.set pdoc;
        (* Publish events to bus (spec W62) — subscribers consume deltas *)
        let bus = Event_bus.global () in
        (* Register one-shot subscribers for this run *)
        let label_count = ref 0 in
        let ref_count = ref 0 in
        let env_count = ref 0 in
        Event_bus.subscribe bus "_run_label_counter" (function
          | Event_bus.LabelDefined _ -> incr label_count
          | _ -> ());
        Event_bus.subscribe bus "_run_ref_counter" (function
          | Event_bus.RefUsed _ -> incr ref_count
          | _ -> ());
        Event_bus.subscribe bus "_run_env_counter" (function
          | Event_bus.EnvironmentOpened _ -> incr env_count
          | _ -> ());
        Event_bus.scan_and_publish bus src;
        (* Unsubscribe after scan *)
        Event_bus.unsubscribe bus "_run_label_counter";
        Event_bus.unsubscribe bus "_run_ref_counter";
        Event_bus.unsubscribe bus "_run_env_counter";
        (* Record event counts in metrics *)
        Validators_metrics.record ~id:"_bus_labels" ~count:!label_count
          ~dur_ms:0.0;
        Validators_metrics.record ~id:"_bus_refs" ~count:!ref_count ~dur_ms:0.0;
        Validators_metrics.record ~id:"_bus_envs" ~count:!env_count ~dur_ms:0.0;
        let rec go acc = function
          | [] -> List.rev acc
          | r :: rs ->
              let t0 = Unix.gettimeofday () in
              let acc =
                match r.run src with
                | Some res ->
                    let t1 = Unix.gettimeofday () in
                    let dur_ms = (t1 -. t0) *. 1000.0 in
                    Validators_metrics.record ~id:res.id ~count:res.count
                      ~dur_ms;
                    res :: acc
                | None -> acc
              in
              go acc rs
        in
        let results = go [] rules in
        Partial_context.clear ();
        Cache_key.store cache cache_key results;
        results

(** Like {!run_all} but returns scored results with confidence levels. Uses VPD
    catalogue for confidence assignment (spec W75). *)
let _ml_confidence_map :
    (string, Evidence_scoring.ml_rule_confidence) Hashtbl.t lazy_t =
  lazy
    (match Sys.getenv_opt "LP_ML_CONFIDENCE_MAP" with
    | Some p when Sys.file_exists p -> Evidence_scoring.load_ml_confidence_map p
    | _ -> Hashtbl.create 0)

let run_all_scored ?(config = Evidence_scoring.default_config) (src : string) :
    Evidence_scoring.scored_result list =
  let results = run_all src in
  let vpd_ids = List.map (fun r -> r.id) rules_vpd_catalogue in
  let scored =
    List.map (fun r -> Evidence_scoring.score_result r vpd_ids) results
  in
  let ml_map = Lazy.force _ml_confidence_map in
  let scored = Evidence_scoring.apply_ml_boost ml_map scored in
  Evidence_scoring.filter_by_config config scored

(* ── Class C (build-coupled) execution path ──────────────────────── *)

let run_class_c (src : string) : result list =
  let rec go acc = function
    | [] -> List.rev acc
    | r :: rs ->
        let acc = match r.run src with Some res -> res :: acc | None -> acc in
        go acc rs
  in
  go [] rules_class_c

let run_with_build (src : string) : result list =
  let ab = run_all src in
  let c = run_class_c src in
  ab @ c

(* PR #241 (memo §11): execute Class D rules explicitly. Not in run_all. *)
let run_class_d (src : string) : result list =
  let rec go acc = function
    | [] -> List.rev acc
    | (r : rule) :: rs ->
        let acc' =
          match r.run src with Some res -> res :: acc | None -> acc
        in
        go acc' rs
  in
  go [] rules_class_d

let run_with_policy (policy : Execution_policy.t) (src : string) : result list =
  let ab = if policy.enable_a || policy.enable_b then run_all src else [] in
  let c = if policy.enable_c then run_class_c src else [] in
  let d = if policy.enable_d then run_class_d src else [] in
  ab @ c @ d

(** Filter rules by detected or explicit language. Universal rules (languages =
    []) always run. Locale rules run only if their language list includes the
    detected lang. *)
let filter_by_language (rules : rule list) (lang : string) : rule list =
  List.filter (fun r -> r.languages = [] || List.mem lang r.languages) rules

(** Run all rules with language gating. If [lang] is [Some "fr"], only universal
    \+ French rules run. If [lang] is [None], auto-detect from document content. *)
let run_all_for_language (src : string) (lang : string option) : result list =
  let detected =
    match lang with Some l -> l | None -> Language_detect.detect_language src
  in
  let rules = filter_by_language (get_rules ()) detected in
  let rec go acc = function
    | [] -> List.rev acc
    | r :: rs ->
        let t0 = Unix.gettimeofday () in
        let acc =
          match r.run src with
          | Some res ->
              let t1 = Unix.gettimeofday () in
              let dur_ms = (t1 -. t0) *. 1000.0 in
              Validators_metrics.record ~id:res.id ~count:res.count ~dur_ms;
              res :: acc
          | None -> acc
        in
        go acc rs
  in
  go [] rules

(* NOTE: run_all_parallel was removed in W102 audit (PR #180). The OCaml Str
   module uses global C-level mutable state for match results, making it unsafe
   for concurrent Domain execution. A mutex would serialize all regex work,
   defeating parallelism. Sequential run_all achieves p95=2.8ms vs 20ms gate
   (86% headroom), so parallelism is unnecessary. Re-add when project migrates
   from Str to thread-safe Re library. *)

let run_all_with_timings (src : string) :
    result list * float * (string * float) list =
  let rules = get_rules () in
  let timings = ref [] in
  let t0 = Unix.gettimeofday () in
  let rec exec acc = function
    | [] -> List.rev acc
    | r :: rs ->
        let t_rule0 = Unix.gettimeofday () in
        let acc' =
          match r.run src with
          | Some res ->
              let t_rule1 = Unix.gettimeofday () in
              let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
              timings := (r.id, dur_ms) :: !timings;
              Validators_metrics.record ~id:res.id ~count:res.count ~dur_ms;
              res :: acc
          | None ->
              let t_rule1 = Unix.gettimeofday () in
              let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
              timings := (r.id, dur_ms) :: !timings;
              acc
        in
        exec acc' rs
  in
  let results = exec [] rules in
  let t1 = Unix.gettimeofday () in
  (results, (t1 -. t0) *. 1000.0, List.rev !timings)

(* ── Layer lookup: table-driven precondition mapping ──────────────── *)

let _layer_tbl : (string, layer) Hashtbl.t =
  let tbl = Hashtbl.create 128 in
  let add ly ids = List.iter (fun id -> Hashtbl.replace tbl id ly) ids in
  (* L0 overrides (rules whose prefix would default to L1) *)
  add L0 [ "MATH-083" ];
  (* L1 overrides (rules whose prefix would default to L0) *)
  add L1
    [
      "TYPO-059";
      "CMD-001";
      "CMD-003";
      "CMD-007";
      "CMD-010";
      "CJK-008";
      "CJK-015";
    ];
  (* L2 overrides *)
  add L2
    [
      "MATH-023";
      "MATH-024";
      "MATH-032";
      "MATH-054";
      "MATH-062";
      "MATH-063";
      "MATH-075";
      "MATH-080";
      "MATH-100";
      "FONT-005";
      "FONT-006";
      "FONT-007";
      "FONT-008";
      "REF-008";
      "REF-010";
      "CMD-012";
      "CMD-014";
      "DOC-001";
      "DOC-002";
      "DOC-003";
      "DOC-004";
      "TAB-003";
      "TAB-006";
      "TAB-007";
      "TAB-008";
      "TAB-009";
      "TAB-010";
      "TAB-011";
      "TAB-012";
      "TAB-013";
      "TAB-014";
      "TAB-015";
      "TAB-016";
      "PKG-007";
      "PKG-008";
      "PKG-009";
      "PKG-010";
      "PKG-011";
      "PKG-012";
      "PKG-013";
      "PKG-014";
      "PKG-015";
      "PKG-016";
      "PKG-017";
      "PKG-018";
      "PKG-019";
      "PKG-020";
      "PKG-021";
      "PKG-022";
      "PKG-023";
      "PKG-024";
      "PKG-025";
      "LANG-001";
      "LANG-002";
      "LANG-004";
      "LANG-006";
      "LANG-007";
      "LANG-013";
      "TIKZ-001";
      "TIKZ-003";
      "TIKZ-004";
      "TIKZ-005";
      "TIKZ-006";
      "TIKZ-007";
      "TIKZ-009";
      "TIKZ-010";
      "FIG-010";
      "FIG-012";
      "FIG-013";
      "FIG-014";
      "FIG-017";
      "FIG-019";
      "FIG-022";
      "FIG-024";
      "FIG-025";
      "COL-006";
      "LAY-015";
      "LAY-020";
      "LAY-022";
      "LAY-024";
      "META-001";
      "META-002";
      "RTL-005";
      "PDF-010";
      "BIB-002";
      "BIB-003";
      "BIB-004";
      "BIB-005";
      "BIB-006";
      "BIB-008";
      "BIB-009";
      "BIB-010";
      "BIB-011";
      "BIB-012";
      "BIB-015";
      "BIB-016";
      "L3-008";
      "L3-010";
    ];
  add L2
    [
      "BIB-001";
      "BIB-007";
      "BIB-013";
      "BIB-014";
      "BIB-017";
      "FONT-002";
      "FONT-003";
      "FONT-010";
      "FONT-013";
      "RTL-001";
      "RTL-002";
      "META-003";
      "META-004";
      "DOC-005";
      "REF-012";
      "PDF-005";
      "FONT-009";
      "FONT-011";
      "FONT-012";
      "CHEM-010";
      "LANG-009";
      "LANG-010";
      "CJK-009";
      "CJK-011";
      "CJK-013";
      "LANG-005";
      "LANG-008";
      (* Phase 6: L3-approx batch 2 *)
      "PKG-003";
      "PKG-006";
      "CJK-003";
      "CJK-005";
      "CJK-012";
      "CJK-016";
      "MATH-076";
      "MATH-103";
      "TAB-004";
      "FIG-008";
      "FIG-011";
      "LAY-005";
      "LAY-013";
      (* Phase 7: LAY text-analysis only; log-dependent rules in
         rules_class_c *)
      "LAY-001";
      "LAY-002";
      "LAY-003";
      "LAY-004";
      "LAY-006";
      "LAY-007";
      "LAY-009";
      "LAY-011";
      "LAY-014";
      "LAY-016";
      "LAY-017";
      "LAY-018";
      "LAY-021";
      "MATH-026";
      "MATH-027";
      (* Phase 8: more approximable *)
      "MATH-089";
      "FIG-005";
      "FIG-015";
      "FIG-018";
      "FIG-020";
      "LAY-008";
      "LAY-010";
      "LAY-012";
      "LAY-019";
      "LAY-023";
    ];
  (* L3 overrides: external file analysis rules *)
  add L3
    [
      "FIG-004";
      "FIG-006";
      "FIG-016";
      "FIG-021";
      "COL-001";
      "COL-002";
      "COL-003";
      "COL-005";
      "PDF-006";
      "PDF-007";
      "PDF-008";
      "PDF-009";
      "PDF-011";
      "PDF-012";
      "COL-004";
      "COL-007";
      "TIKZ-002";
      "TIKZ-008";
      "CJK-007";
    ];
  tbl

let _prefix_layers : (string * layer) list =
  [
    ("TYPO-", L0);
    ("ENC-", L0);
    ("CHAR-", L0);
    ("SPC-", L0);
    ("CMD-", L0);
    ("CJK-", L0);
    ("VERB-", L0);
    ("MOD-", L1);
    ("EXP-", L1);
    ("DELIM-", L1);
    ("SCRIPT-", L1);
    ("MATH-", L1);
    ("REF-", L1);
    ("CHEM-", L1);
    ("FONT-", L1);
    ("RTL-", L1);
    ("PT-", L1);
    ("L3-", L1);
    ("STYLE-", L4);
    ("CE-", L4);
    ("IB-", L4);
    ("LANG-", L4);
    ("TH-", L0);
  ]

let precondition_of_rule_id (id : string) : layer =
  match Hashtbl.find_opt _layer_tbl id with
  | Some ly -> ly
  | None ->
      let rec find = function
        | [] -> L0
        | (pfx, ly) :: rest ->
            if
              String.length id >= String.length pfx
              && String.sub id 0 (String.length pfx) = pfx
            then ly
            else find rest
      in
      find _prefix_layers

let allow_for_layer (id : string) (ly : layer) : bool =
  match (precondition_of_rule_id id, ly) with
  | L0, L0 -> true
  | L1, L1 -> true
  | L2, L2 -> true
  | L3, L3 -> true
  | L4, L4 -> true
  | _ -> false

let run_all_with_timings_for_layer (src : string) (ly : layer) :
    result list * float * (string * float) list =
  let rules = get_rules () in
  let timings = ref [] in
  let t0 = Unix.gettimeofday () in
  let rec exec acc = function
    | [] -> List.rev acc
    | r :: rs ->
        let t_rule0 = Unix.gettimeofday () in
        let acc' =
          if allow_for_layer r.id ly then (
            match r.run src with
            | Some res ->
                let t_rule1 = Unix.gettimeofday () in
                let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
                timings := (r.id, dur_ms) :: !timings;
                Validators_metrics.record ~id:res.id ~count:res.count ~dur_ms;
                res :: acc
            | None ->
                let t_rule1 = Unix.gettimeofday () in
                let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
                timings := (r.id, dur_ms) :: !timings;
                acc)
          else
            let t_rule1 = Unix.gettimeofday () in
            let dur_ms = (t_rule1 -. t_rule0) *. 1000.0 in
            timings := (r.id, dur_ms) :: !timings;
            acc
        in
        exec acc' rs
  in
  let results = exec [] rules in
  let t1 = Unix.gettimeofday () in
  (results, (t1 -. t0) *. 1000.0, List.rev !timings)

(* ── Wire DAG validation (spec §6.1) ─────────────────────────────── *)
(* Deferred initialization: precondition_of_rule_id is now defined *)
let () =
  _dag_validate_fn :=
    fun rules ->
      (* Deduplicate rules by ID before DAG construction *)
      let seen = Hashtbl.create 256 in
      let unique_rules =
        List.filter
          (fun r ->
            if Hashtbl.mem seen r.id then false
            else (
              Hashtbl.replace seen r.id ();
              true))
          rules
      in
      (* PR #241 (p1.1-#4): no silent fallback to default_meta. If a catalogued
         rule is missing from rule_contracts.yaml, fail loudly at startup so the
         CI drift gate's invariant is enforced at runtime too.

         Internal utility "rules" (e.g. "no_tabs", "unmatched_braces",
         "DOC-STRUCT") that don't follow the FAMILY-NNN public rule-id
         convention are skipped from the check — they are infrastructure
         markers, not part of the public rule catalogue. *)
      let is_catalogue_id id =
        let n = String.length id in
        let has_dash = String.contains id '-' in
        let is_upper_family =
          n >= 3
          &&
          let c = id.[0] in
          c >= 'A' && c <= 'Z'
        in
        has_dash && is_upper_family && not (String.equal id "DOC-STRUCT")
      in
      let missing = ref [] in
      let metas =
        List.filter_map
          (fun r ->
            match Rule_contract_loader.find_opt r.id with
            | Some c -> Some (Rule_contract_loader.to_validator_meta c)
            | None when is_catalogue_id r.id ->
                missing := r.id :: !missing;
                None
            | None ->
                (* Internal utility: give it a default meta so the DAG still
                   contains it, but it isn't part of the public catalogue so the
                   drift check doesn't fire. Deprecated alert is silenced here —
                   this is the intended remaining use of [default_meta]. *)
                Some
                  ((Validator_dag.default_meta [@alert "-deprecated"]) r.id
                     (match precondition_of_rule_id r.id with
                     | L0 -> Validator_dag.L0
                     | L1 -> Validator_dag.L1
                     | L2 -> Validator_dag.L2
                     | L3 -> Validator_dag.L3
                     | L4 -> Validator_dag.L4)))
          unique_rules
      in
      if !missing <> [] then
        failwith
          (Printf.sprintf
             "[validators] %d catalogued rule(s) registered but missing from \
              specs/rules/rule_contracts.yaml; first few: %s. Regenerate with \
              scripts/tools/generate_rule_contracts.py."
             (List.length !missing)
             (String.concat ","
                (List.filteri (fun i _ -> i < 5) (List.rev !missing))));
      match Validator_dag.build_dag metas with
      | Ok _dag ->
          (* PR #241 (p1.1-#6): topo_order no longer stored globally. Callers
             that need an edge-driven invalidation order compute it at the use
             site via [Validator_dag.build_dag]. *)
          let conflicts = Validator_dag.detect_conflicts metas in
          if conflicts <> [] then
            Printf.eprintf
              "[validators] WARNING: %d conflict(s) in validator DAG\n%!"
              (List.length conflicts)
      | Error msg ->
          Printf.eprintf "[validators] WARNING: DAG cycle: %s\n%!" msg

(* ── Incremental validation (spec W111-120) ────────────────────── *)

let _prev_snapshot : Chunk_store.snapshot option ref = ref None
let _chunk_cache : Chunk_store.chunk_cache = Chunk_store.create_cache ()

let _is_cross_chunk_rule (r : rule) : bool =
  match precondition_of_rule_id r.id with L3 | L4 -> true | _ -> false

let _resolve_old_snap prev_src =
  match (!_prev_snapshot, prev_src) with
  | Some cached, _ -> Some cached
  | None, Some ps -> Some (Chunk_store.create_snapshot ps)
  | None, None -> None

let run_all_incremental ?(prev_src : string option) (src : string) : result list
    =
  let new_snap = Chunk_store.create_snapshot src in
  let dirty_indices =
    match _resolve_old_snap prev_src with
    | None -> List.init (Array.length new_snap.chunks) Fun.id
    | Some os -> Invalidation.compute ~old_snap:os ~new_snap
  in
  _prev_snapshot := Some new_snap;
  (* Per-chunk rules: only re-run dirty chunks *)
  let chunk_results =
    Array.to_list
      (Array.mapi
         (fun i (chunk : Chunk_store.chunk) ->
           if List.mem i dirty_indices then (
             let rules = get_rules () in
             let chunk_rules =
               List.filter (fun r -> not (_is_cross_chunk_rule r)) rules
             in
             let res =
               List.filter_map (fun r -> r.run chunk.content) chunk_rules
             in
             Chunk_store.store_chunk _chunk_cache chunk.Chunk_store.id res;
             res)
           else
             match
               Chunk_store.lookup_chunk _chunk_cache chunk.Chunk_store.id
             with
             | Some cached -> cached
             | None ->
                 let rules = get_rules () in
                 let chunk_rules =
                   List.filter (fun r -> not (_is_cross_chunk_rule r)) rules
                 in
                 let res =
                   List.filter_map (fun r -> r.run chunk.content) chunk_rules
                 in
                 Chunk_store.store_chunk _chunk_cache chunk.Chunk_store.id res;
                 res)
         new_snap.chunks)
  in
  (* Cross-chunk rules: always run on full source *)
  let rules = get_rules () in
  let cross_rules = List.filter _is_cross_chunk_rule rules in
  let cross_results = List.filter_map (fun r -> r.run src) cross_rules in
  List.concat chunk_results @ cross_results

(* ── EDF-scheduled incremental validation ──────────────────────── *)

let _scheduler = Edf_scheduler.create ~capacity:4096 ()

let run_all_scheduled ?(edit_pos = 0) ?(prev_src : string option) (src : string)
    : result list =
  let new_snap = Chunk_store.create_snapshot src in
  let dirty_indices =
    match _resolve_old_snap prev_src with
    | None -> List.init (Array.length new_snap.chunks) Fun.id
    | Some os -> Invalidation.compute ~old_snap:os ~new_snap
  in
  _prev_snapshot := Some new_snap;
  let rules = get_rules () in
  let chunk_rules = List.filter (fun r -> not (_is_cross_chunk_rule r)) rules in
  (* Submit tasks for dirty chunks *)
  let tasks =
    List.concat_map
      (fun i ->
        let chunk = new_snap.chunks.(i) in
        let layers = [ 0; 1; 2 ] in
        List.map
          (fun layer_id ->
            let priority =
              Edf_scheduler.compute_priority ~edit_pos ~chunk_start:chunk.start
                ~layer_id
            in
            let layer_rules =
              List.filter
                (fun r ->
                  let rl =
                    match precondition_of_rule_id r.id with
                    | L0 -> 0
                    | L1 -> 1
                    | L2 -> 2
                    | L3 -> 3
                    | L4 -> 4
                  in
                  rl = layer_id)
                chunk_rules
            in
            {
              Edf_scheduler.task_id = Printf.sprintf "chunk%d-L%d" i layer_id;
              layer_id;
              chunk_id = chunk.Chunk_store.id;
              priority;
              work =
                (fun () ->
                  let res =
                    List.filter_map (fun r -> r.run chunk.content) layer_rules
                  in
                  Chunk_store.store_chunk _chunk_cache chunk.Chunk_store.id res;
                  res);
            })
          layers)
      dirty_indices
  in
  Edf_scheduler.submit_batch _scheduler tasks;
  let scheduled_results = Edf_scheduler.drain _scheduler in
  (* Cached results for clean chunks *)
  let cached_results =
    Array.to_list new_snap.chunks
    |> List.mapi (fun i chunk ->
           if List.mem i dirty_indices then []
           else
             match
               Chunk_store.lookup_chunk _chunk_cache chunk.Chunk_store.id
             with
             | Some r -> r
             | None -> [])
    |> List.concat
  in
  (* Cross-chunk rules on full source *)
  let cross_rules = List.filter _is_cross_chunk_rule rules in
  let cross_results = List.filter_map (fun r -> r.run src) cross_rules in
  scheduled_results @ cached_results @ cross_results
