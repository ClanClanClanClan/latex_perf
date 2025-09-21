open Printf

let read_all path =
  let ic = open_in_bin path in
  let buf = really_input_string ic (in_channel_length ic) in
  close_in ic; buf

let parse_layer = function
  | "l0" -> Latex_parse_lib.Validators.L0
  | "l1" -> Latex_parse_lib.Validators.L1
  | "l2" -> Latex_parse_lib.Validators.L2
  | "l3" -> Latex_parse_lib.Validators.L3
  | "l4" -> Latex_parse_lib.Validators.L4
  | _ -> Latex_parse_lib.Validators.L0

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | [_; path] ->
      let src = read_all path in
      (* Build post-command spans for context, mirroring REST summary *)
      let module T = Latex_parse_lib.Tokenizer_lite in
      let toks = T.tokenize src in
      let n = String.length src in
      let cmd_spans = List.fold_left (fun acc (t:T.tok) -> match t.kind with
        | T.Command ->
            let i' = t.s + 1 in
            let k = ref i' in
            while !k < n && ((let ch = String.unsafe_get src !k in
                              (ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z'))) do incr k done;
            if !k > i' then ({ Latex_parse_lib.Validators_context.name = String.sub src i' (!k - i'); s = t.s; e = t.e } : Latex_parse_lib.Validators_context.post_command) :: acc else acc
        | _ -> acc
      ) [] toks |> List.rev in
      Latex_parse_lib.Validators_context.set_post_commands cmd_spans;
      let results = Latex_parse_lib.Validators.run_all src in
      Latex_parse_lib.Validators_context.clear ();
      List.iter (fun (r:Latex_parse_lib.Validators.result) ->
        printf "%s\t%s\t%d\t%s\n"
          r.id (Latex_parse_lib.Validators.severity_to_string r.severity) r.count r.message
      ) results
  | [_; "--layer"; layer; path] ->
      let ly = parse_layer layer in
      let src = read_all path in
      let module T = Latex_parse_lib.Tokenizer_lite in
      let toks = T.tokenize src in
      let n = String.length src in
      let cmd_spans = List.fold_left (fun acc (t:T.tok) -> match t.kind with
        | T.Command ->
            let i' = t.s + 1 in
            let k = ref i' in
            while !k < n && ((let ch = String.unsafe_get src !k in
                              (ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z'))) do incr k done;
            if !k > i' then ({ Latex_parse_lib.Validators_context.name = String.sub src i' (!k - i'); s = t.s; e = t.e } : Latex_parse_lib.Validators_context.post_command) :: acc else acc
        | _ -> acc
      ) [] toks |> List.rev in
      Latex_parse_lib.Validators_context.set_post_commands cmd_spans;
      let (results, total_ms, timings) = Latex_parse_lib.Validators.run_all_with_timings_for_layer src ly in
      Latex_parse_lib.Validators_context.clear ();
      printf "# layer=%s\ttotal_ms=%.3f\n" layer total_ms;
      List.iter (fun (id, ms) -> printf "# %s\t%.3f\n" id ms) timings;
      List.iter (fun (r:Latex_parse_lib.Validators.result) ->
        printf "%s\t%s\t%d\t%s\n"
          r.id (Latex_parse_lib.Validators.severity_to_string r.severity) r.count r.message
      ) results
  | _ ->
      eprintf "Usage: %s [--layer l0|l1|l2|l3|l4] <file.tex>\n" Sys.argv.(0);
      exit 2
