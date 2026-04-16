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
  Latex_parse_lib.Build_profile.deactivate ()

let setup_all ~path ~src ~log_path =
  let base_dir = Filename.dirname path in
  setup_file_context ~base_dir ~tex_path:path ~src;
  setup_command_spans src;
  let bp =
    match log_path with
    | Some lp ->
        Latex_parse_lib.Build_profile.create_with_log ~tex_path:path
          ~log_path:lp
    | None -> Latex_parse_lib.Build_profile.create path
  in
  Latex_parse_lib.Build_profile.activate bp;
  bp

(* ── Class C result detection ────────────────────────────────────── *)

let _class_c_ids =
  List.map
    (fun (r : Latex_parse_lib.Validators.rule) -> r.id)
    Latex_parse_lib.Validators.rules_class_c

let is_class_c id = List.mem id _class_c_ids

let print_result (r : Latex_parse_lib.Validators.result) =
  let tag = if is_class_c r.id then "[build] " else "" in
  printf "%s\t%s\t%d\t%s%s\n" r.id
    (Latex_parse_lib.Validators.severity_to_string r.severity)
    r.count tag r.message

(* ── Entry point ─────────────────────────────────────────────────── *)

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | [ _; path ] ->
      let src = read_all path in
      let bp = setup_all ~path ~src ~log_path:None in
      Fun.protect ~finally:cleanup (fun () ->
          if Latex_parse_lib.Build_profile.has_log bp then
            let results = Latex_parse_lib.Validators.run_with_build src in
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
  | [ _; "--log"; log_path; path ] ->
      let src = read_all path in
      ignore (setup_all ~path ~src ~log_path:(Some log_path));
      Fun.protect ~finally:cleanup (fun () ->
          let results = Latex_parse_lib.Validators.run_with_build src in
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
  | _ ->
      eprintf
        "Usage: %s [--layer l0|l1|l2|l3|l4] [--log <file.log>] <file.tex>\n"
        Sys.argv.(0);
      exit 2
