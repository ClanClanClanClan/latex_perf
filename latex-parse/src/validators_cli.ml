open Printf

let read_all path =
  try
    let ic = open_in_bin path in
    let buf = really_input_string ic (in_channel_length ic) in
    close_in ic;
    buf
  with Sys_error msg ->
    eprintf "Error: %s\n" msg;
    exit 1

let parse_layer = function
  | "l0" -> Latex_parse_lib.Validators.L0
  | "l1" -> Latex_parse_lib.Validators.L1
  | "l2" -> Latex_parse_lib.Validators.L2
  | "l3" -> Latex_parse_lib.Validators.L3
  | "l4" -> Latex_parse_lib.Validators.L4
  | _ -> Latex_parse_lib.Validators.L0

(* ── Shared setup helpers ────────────────────────────────────────── *)

let setup_file_context ~base_dir ~tex_path ~src =
  let file_ctx =
    Latex_parse_lib.File_analyzer.analyze_files ~base_dir ~tex_path ~source:src
      ()
  in
  Latex_parse_lib.File_context.set_file_context file_ctx

let setup_command_spans src =
  let module T = Latex_parse_lib.Tokenizer_lite in
  let toks = T.tokenize src in
  let n = String.length src in
  let cmd_spans =
    List.fold_left
      (fun acc (t : T.tok) ->
        match t.kind with
        | T.Command ->
            let i' = t.s + 1 in
            let k = ref i' in
            while
              !k < n
              &&
              let ch = String.unsafe_get src !k in
              (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
            do
              incr k
            done;
            if !k > i' then
              ({
                 Latex_parse_lib.Validators_context.name =
                   String.sub src i' (!k - i');
                 s = t.s;
                 e = t.e;
               }
                : Latex_parse_lib.Validators_context.post_command)
              :: acc
            else acc
        | _ -> acc)
      [] toks
    |> List.rev
  in
  Latex_parse_lib.Validators_context.set_post_commands cmd_spans

let cleanup () =
  Latex_parse_lib.Validators_context.clear ();
  Latex_parse_lib.File_context.clear_file_context ();
  Latex_parse_lib.Build_artifact_state.clear ();
  Latex_parse_lib.User_macro_context.clear ();
  Latex_parse_lib.Language_profile.Context.clear ()

(* ── Profile handling (PR #236, memo §4) ─────────────────────────── *)

let parse_profile_flag = function
  | "auto" -> `Auto
  | s -> (
      match Latex_parse_lib.Language_profile.tier_of_string s with
      | Some t -> `Forced t
      | None ->
          eprintf
            "Error: unknown profile %S (expected one of: auto, lp-core, \
             lp-extended, lp-foreign)\n"
            s;
          exit 2)

let resolve_profile ~requested ~src =
  let tier, features =
    match requested with
    | `Auto -> Latex_parse_lib.Language_profile.classify_source src
    | `Forced t -> (t, [])
  in
  Latex_parse_lib.Language_profile.Context.set tier;
  (tier, features)

let print_profile_banner tier features =
  eprintf "# profile=%s\n"
    (Latex_parse_lib.Language_profile.tier_to_string tier);
  List.iter
    (fun (f : Latex_parse_lib.Unsupported_feature.t) ->
      eprintf "# [%s] line %d offset %d: %s\n"
        (Latex_parse_lib.Unsupported_feature.severity_to_string f.severity)
        f.line f.offset f.message)
    features

let setup_all ~path ~src ~log_path =
  let base_dir = Filename.dirname path in
  setup_file_context ~base_dir ~tex_path:path ~src;
  setup_command_spans src;
  let bp = Latex_parse_lib.Build_profile.create ~tex_path:path ~base_dir in
  let bp =
    match log_path with
    | Some lp -> Latex_parse_lib.Build_profile.load_log_from ~log_path:lp bp
    | None -> Latex_parse_lib.Build_profile.load_log bp
  in
  (match Latex_parse_lib.Build_artifact_state.from_profile bp with
  | Some state -> Latex_parse_lib.Build_artifact_state.set state
  | None -> ());
  let reg = Latex_parse_lib.User_macro_registry.create src in
  Latex_parse_lib.User_macro_context.set reg;
  bp

(* ── Class C result detection ────────────────────────────────────── *)

let is_class_c id =
  Latex_parse_lib.Execution_class.classify id
  = Latex_parse_lib.Execution_class.C

let print_result (r : Latex_parse_lib.Validators.result) =
  let tag = if is_class_c r.id then "[build] " else "" in
  printf "%s\t%s\t%d\t%s%s\n" r.id
    (Latex_parse_lib.Validators.severity_to_string r.severity)
    r.count tag r.message

(* ── Apply-fixes flow (v26.2.1 PR #4) ─────────────────────────────── *)

(** Collect every fix edit from [results] into a single list. Rules that emit
    [fix = None] contribute nothing. If [filter_id] is [Some id], only results
    whose [r.id = id] contribute (v26.3 [--apply-fixes-for]). *)
let collect_fix_edits ?filter_id
    (results : Latex_parse_lib.Validators.result list) :
    Latex_parse_lib.Cst_edit.t list =
  List.concat_map
    (fun (r : Latex_parse_lib.Validators.result) ->
      let included =
        match filter_id with None -> true | Some id -> r.id = id
      in
      match r.fix with Some edits when included -> edits | _ -> [])
    results

let env_flag_on name =
  match Sys.getenv_opt name with
  | Some ("1" | "true" | "TRUE" | "on" | "ON") -> true
  | _ -> false

(** v26.2.1 PR #4 + v26.3 item B: run validators, collect fix edits (optionally
    filtered to a single rule via [filter_id]), apply them via
    [Rewrite_engine.apply], emit modified source.

    v26.4 §1.1 [best_effort]: when [true], conflicting fixes are NOT a hard
    error — the caller gets the maximal non-conflicting subset applied to
    stdout, with the skipped subset reported on stderr. Exit code 0 in that case
    (the partial-fix output is the contract). When [false] (default), behaviour
    is unchanged: any overlap returns exit 2 with no stdout. *)
let overlap_error a b =
  eprintf
    "E.apply-fixes.overlap: two rule fixes affect overlapping source ranges; \
     refusing to apply.\n\
     # first edit:  %s\n\
     # second edit: %s\n\
     # hint: re-run with --apply-fixes-best-effort to apply the maximal \
     non-conflicting subset.\n"
    (Latex_parse_lib.Cst_edit.to_string a)
    (Latex_parse_lib.Cst_edit.to_string b);
  2

(* P1a: maximum passes for the converging [--apply-fixes] loop. The corpus
   safety gate proves every file reaches a fixpoint in ≤8 passes; this cap is a
   generous backstop for arbitrary user documents and a hard stop should a
   future producer regress into a non-terminating cascade. *)
let apply_fixes_cap = 64

(* P1a: iterate [--apply-fixes] to a fixpoint. Each pass refreshes the
   src-dependent contexts (language profile, command spans, user macros, file
   context) for the evolving text, exactly as a fresh [--apply-fixes] subprocess
   would — so the in-process fixpoint is byte-identical to iterating the CLI
   externally, which is the behaviour [check_apply_fixes_safety.py] validates
   across the whole corpus. Benign cross-rule cascades (e.g. ENC-004 producing
   U+2026, then SPC-025 deleting the space before it) now resolve in a single
   invocation instead of needing repeated runs.

   Cycle-safe: a seen-set of per-pass digests detects oscillation and the cap
   bounds runaway cascades. Both known oscillating producer pairs were
   reconciled at source (no file oscillates today), but if a future pair
   regresses the loop emits the last stable state ([cur], the text whose
   application re-enters the cycle) and warns rather than hanging. Emitting
   [cur] — not the repeated state — keeps the safety gate able to flag the
   regression: [--apply-fixes] of the two cycle states still map to each other,
   so the gate's external loop sees the cycle. *)
let run_apply_fixes_converge ?filter_id ~path ~src () =
  let seen = Hashtbl.create 16 in
  Hashtbl.replace seen (Digest.string src) ();
  (* v27.1.2: each pass applies the maximal NON-CONFLICTING subset of edits
     (deterministic best-effort, [Cst_edit.apply_best_effort] — first-by-rule-
     order wins a conflict) instead of the former strict [Rewrite_engine.apply],
     which ABORTED the whole document if ANY two promoted rules emitted
     overlapping edits (e.g. TYPO-005 `...`→`\dots` vs TYPO-010 space-before-the
     ellipsis dot). Promoting many fix-producers into the default set made such
     overlaps common, so all-or-nothing left `--apply-fixes` unusable on real
     documents. Best-effort never corrupts (the applied subset is pairwise
     non-conflicting); an edit that loses a conflict on one pass is re-attempted
     on the next once the winning edit has changed the text, so the converge
     loop still drives every compatible fix to a fixpoint. Cycle-detection + the
     cap keep it terminating exactly as before. *)
  let rec loop cur passes =
    ignore (resolve_profile ~requested:`Auto ~src:cur);
    ignore (setup_all ~path ~src:cur ~log_path:None);
    (* Class-D-inclusive so L4 STYLE fix producers (STYLE-015/023) apply; batch
       path, not the keystroke hot path (v27.1.6). *)
    let results = Latex_parse_lib.Validators.run_all_with_class_d cur in
    let edits = collect_fix_edits ?filter_id results in
    if edits = [] then cur
    else
      let nxt, _applied, _skipped =
        Latex_parse_lib.Cst_edit.apply_best_effort cur edits
      in
      if String.equal nxt cur then cur
      else
        let dn = Digest.string nxt in
        if Hashtbl.mem seen dn then (
          eprintf
            "# apply-fixes: fix cycle detected after %d pass(es); emitting \
             last stable state (contradictory producers)\n"
            (passes + 1);
          cur)
        else if passes + 1 >= apply_fixes_cap then (
          eprintf
            "# apply-fixes: reached the %d-pass cap without a fixpoint; \
             emitting latest state\n"
            apply_fixes_cap;
          nxt)
        else (
          Hashtbl.replace seen dn ();
          loop nxt (passes + 1))
  in
  print_string (loop src 0);
  0

let run_apply_fixes ?filter_id ?(best_effort = false) ?(converge = false) ~path
    ~src () =
  let _tier, features = resolve_profile ~requested:`Auto ~src in
  print_profile_banner _tier features;
  Fun.protect ~finally:cleanup (fun () ->
      if converge && not best_effort then
        run_apply_fixes_converge ?filter_id ~path ~src ()
      else
        let _bp = setup_all ~path ~src ~log_path:None in
        (* Class-D-inclusive (see converge path) so STYLE-* fixes apply. *)
        let results = Latex_parse_lib.Validators.run_all_with_class_d src in
        let edits = collect_fix_edits ?filter_id results in
        if best_effort then (
          let out, applied, skipped =
            Latex_parse_lib.Cst_edit.apply_best_effort src edits
          in
          print_string out;
          if skipped <> [] then (
            eprintf
              "# apply-fixes-best-effort: %d edit(s) applied, %d skipped\n"
              (List.length applied) (List.length skipped);
            List.iter
              (fun e ->
                eprintf "# skipped: %s\n" (Latex_parse_lib.Cst_edit.to_string e))
              skipped);
          0)
        else
          match Latex_parse_lib.Rewrite_engine.apply ~source:src ~edits with
          | Ok out ->
              print_string out;
              0
          | Error (`Overlap (a, b)) -> overlap_error a b)

(* ── Entry point ─────────────────────────────────────────────────── *)

let () =
  let args = Array.to_list Sys.argv in
  (* v26.2.1 PR #4: `L0_APPLY_FIXES=1` env gate is equivalent to prefixing a
     single-path invocation with [--apply-fixes]. *)
  let apply_env_on = env_flag_on "L0_APPLY_FIXES" in
  match args with
  | [ _; "--apply-fixes"; path ] ->
      let src = read_all path in
      exit (run_apply_fixes ~converge:true ~path ~src ())
  | [ _; "--apply-fixes-for"; rule_id; path ] ->
      let src = read_all path in
      exit (run_apply_fixes ~filter_id:rule_id ~path ~src ())
  | [ _; "--apply-fixes-best-effort"; path ] ->
      let src = read_all path in
      exit (run_apply_fixes ~best_effort:true ~path ~src ())
  | [ _; "--apply-fixes-best-effort-for"; rule_id; path ] ->
      let src = read_all path in
      exit (run_apply_fixes ~best_effort:true ~filter_id:rule_id ~path ~src ())
  | [ _; path ] when apply_env_on ->
      let src = read_all path in
      exit (run_apply_fixes ~converge:true ~path ~src ())
  | [ _; path ] ->
      let src = read_all path in
      let tier, features = resolve_profile ~requested:`Auto ~src in
      print_profile_banner tier features;
      let bp = setup_all ~path ~src ~log_path:None in
      Fun.protect ~finally:cleanup (fun () ->
          if Latex_parse_lib.Build_profile.has_log bp then
            let policy = Latex_parse_lib.Execution_policy.with_build in
            let results =
              Latex_parse_lib.Validators.run_with_policy policy src
            in
            List.iter print_result results
          else
            let scored = Latex_parse_lib.Validators.run_all_scored src in
            List.iter
              (fun (r : Latex_parse_lib.Evidence_scoring.scored_result) ->
                printf "%s\t%s\t%d\t%s\n" r.id
                  (Latex_parse_lib.Validators_common.severity_to_string
                     r.severity)
                  r.count r.message)
              scored)
  | [ _; "--profile"; profile_arg; path ] ->
      let src = read_all path in
      let requested = parse_profile_flag profile_arg in
      let tier, features = resolve_profile ~requested ~src in
      print_profile_banner tier features;
      let bp = setup_all ~path ~src ~log_path:None in
      Fun.protect ~finally:cleanup (fun () ->
          if Latex_parse_lib.Build_profile.has_log bp then
            let policy = Latex_parse_lib.Execution_policy.with_build in
            let results =
              Latex_parse_lib.Validators.run_with_policy policy src
            in
            List.iter print_result results
          else
            let scored = Latex_parse_lib.Validators.run_all_scored src in
            List.iter
              (fun (r : Latex_parse_lib.Evidence_scoring.scored_result) ->
                printf "%s\t%s\t%d\t%s\n" r.id
                  (Latex_parse_lib.Validators_common.severity_to_string
                     r.severity)
                  r.count r.message)
              scored)
  | [ _; "--advisory"; path ] ->
      (* PR #241 (memo §11): hot-path + Class D advisory rules. *)
      let src = read_all path in
      let tier, features = resolve_profile ~requested:`Auto ~src in
      print_profile_banner tier features;
      ignore (setup_all ~path ~src ~log_path:None);
      let policy = Latex_parse_lib.Execution_policy.with_advisory in
      Fun.protect ~finally:cleanup (fun () ->
          let results = Latex_parse_lib.Validators.run_with_policy policy src in
          List.iter print_result results)
  | [ _; "--log"; log_path; path ] ->
      let src = read_all path in
      let tier, features = resolve_profile ~requested:`Auto ~src in
      print_profile_banner tier features;
      ignore (setup_all ~path ~src ~log_path:(Some log_path));
      let policy = Latex_parse_lib.Execution_policy.with_build in
      Fun.protect ~finally:cleanup (fun () ->
          let results = Latex_parse_lib.Validators.run_with_policy policy src in
          List.iter print_result results)
  | [ _; "--layer"; layer; path ] ->
      let src = read_all path in
      ignore (setup_all ~path ~src ~log_path:None);
      let ly = parse_layer layer in
      Fun.protect ~finally:cleanup (fun () ->
          let results, total_ms, timings =
            Latex_parse_lib.Validators.run_all_with_timings_for_layer src ly
          in
          printf "# layer=%s\ttotal_ms=%.3f\n" layer total_ms;
          List.iter (fun (id, ms) -> printf "# %s\t%.3f\n" id ms) timings;
          List.iter print_result results)
  | [ _; "--project"; path ] ->
      let graph = Latex_parse_lib.Project_graph.build ~root:path in
      let ps = Latex_parse_lib.Project_state.build graph in
      Latex_parse_lib.Project_context.set ps;
      Fun.protect
        ~finally:(fun () ->
          Latex_parse_lib.Project_context.clear ();
          cleanup ())
        (fun () ->
          (* Run single-file validators on each file *)
          List.iter
            (fun (fs : Latex_parse_lib.Project_state.file_state) ->
              let src = read_all fs.path in
              ignore (setup_all ~path:fs.path ~src ~log_path:None);
              let results = Latex_parse_lib.Validators.run_all src in
              List.iter
                (fun (r : Latex_parse_lib.Validators.result) ->
                  printf "[%s] %s\t%s\t%d\t%s\n"
                    (Filename.basename fs.path)
                    r.id
                    (Latex_parse_lib.Validators.severity_to_string r.severity)
                    r.count r.message)
                results)
            ps.file_states)
  | _ ->
      eprintf
        "Usage: %s [--apply-fixes | --apply-fixes-for RULE-ID | \
         --apply-fixes-best-effort | --apply-fixes-best-effort-for RULE-ID] \
         [--profile auto|lp-core|lp-extended|lp-foreign] [--advisory] \
         [--project <root.tex>] [--layer l0|l1|l2|l3|l4] [--log <file.log>] \
         <file.tex>\n\n\
         --apply-fixes  run validators, apply every rule's fix edits and emit \
         the\n\
        \               modified source to stdout. Iterates to a fixpoint \
         (P1a) so\n\
        \               cross-rule cascades resolve in one run; cycle-safe. \
         Each pass\n\
        \               applies the maximal NON-CONFLICTING subset \
         (deterministic\n\
        \               best-effort, rule-order priority), so overlapping \
         fixes from\n\
        \               different rules never abort the document (v27.1.2). \
         L0_APPLY_FIXES=1\n\
        \               is equivalent when no other flag is given.\n\
         --apply-fixes-for RULE-ID  same as --apply-fixes but only applies \
         fixes from results\n\
        \               whose [r.id = RULE-ID] (strict; a single rule's edits \
         must not self-overlap). Useful for incremental adoption (v26.3).\n\
         --apply-fixes-best-effort  v26.4: applies the maximal non-conflicting \
         subset of fixes\n\
        \               via Cst_edit.apply_best_effort. Reports the skipped \
         subset to stderr.\n\
        \               Exit 0 even when some edits were skipped (the \
         partial-fix output is the contract).\n\
         --apply-fixes-best-effort-for RULE-ID  same as \
         --apply-fixes-best-effort, filtered by rule id (v26.4).\n"
        Sys.argv.(0);
      exit 2
