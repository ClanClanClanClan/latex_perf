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
    [fix = None] contribute nothing. *)
let collect_fix_edits (results : Latex_parse_lib.Validators.result list) :
    Latex_parse_lib.Cst_edit.t list =
  List.concat_map
    (fun (r : Latex_parse_lib.Validators.result) ->
      match r.fix with Some edits -> edits | None -> [])
    results

let env_flag_on name =
  match Sys.getenv_opt name with
  | Some ("1" | "true" | "TRUE" | "on" | "ON") -> true
  | _ -> false

(** v26.2.1 PR #4: run validators, collect fix edits, apply them via
    [Rewrite_engine.apply] (which wraps [Cst_edit.apply_all]), and emit the
    modified source to stdout. On overlap, emit [E.apply-fixes.overlap] to
    stderr and exit 2 without touching stdout. If no rule emits fixes, the
    original source is echoed unchanged and the return code is 0. *)
let run_apply_fixes ~path ~src =
  let _tier, features = resolve_profile ~requested:`Auto ~src in
  print_profile_banner _tier features;
  let _bp = setup_all ~path ~src ~log_path:None in
  Fun.protect ~finally:cleanup (fun () ->
      let results = Latex_parse_lib.Validators.run_all src in
      let edits = collect_fix_edits results in
      match Latex_parse_lib.Rewrite_engine.apply ~source:src ~edits with
      | Ok out ->
          print_string out;
          0
      | Error (`Overlap (a, b)) ->
          eprintf
            "E.apply-fixes.overlap: two rule fixes affect overlapping source \
             ranges; refusing to apply.\n\
             # first edit:  %s\n\
             # second edit: %s\n"
            (Latex_parse_lib.Cst_edit.to_string a)
            (Latex_parse_lib.Cst_edit.to_string b);
          2)

(* ── Entry point ─────────────────────────────────────────────────── *)

let () =
  let args = Array.to_list Sys.argv in
  (* v26.2.1 PR #4: `L0_APPLY_FIXES=1` env gate is equivalent to prefixing a
     single-path invocation with [--apply-fixes]. *)
  let apply_env_on = env_flag_on "L0_APPLY_FIXES" in
  match args with
  | [ _; "--apply-fixes"; path ] ->
      let src = read_all path in
      exit (run_apply_fixes ~path ~src)
  | [ _; path ] when apply_env_on ->
      let src = read_all path in
      exit (run_apply_fixes ~path ~src)
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
        "Usage: %s [--apply-fixes] [--profile \
         auto|lp-core|lp-extended|lp-foreign] [--advisory] [--project \
         <root.tex>] [--layer l0|l1|l2|l3|l4] [--log <file.log>] <file.tex>\n\n\
         --apply-fixes  run validators, apply every rule's fix edits via \
         Cst_edit.apply_all,\n\
        \               and emit the modified source to stdout. \
         L0_APPLY_FIXES=1 is equivalent\n\
        \               when no other flag is given. Overlapping fixes → \
         stderr + exit 2.\n"
        Sys.argv.(0);
      exit 2
