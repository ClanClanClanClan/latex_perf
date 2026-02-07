(* VPD Compile — Main driver for the Validator-Producing DSL compiler.

   Usage: vpd_compile <manifest.json> [-o <output.ml>] [--internal]

   Reads a VPD manifest in JSON format and emits an OCaml module containing
   validator definitions ready for inclusion in the build.

   --internal Generated file lives inside the latex_parse_lib library. Uses
   sibling module references (Validators, Unicode) instead of fully-qualified
   Latex_parse_lib.Validators paths. *)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let internal = List.mem "--internal" args in
  let args = List.filter (( <> ) "--internal") args in
  match args with
  | [ input ] ->
      let manifest = Vpd_parse.parse_file input in
      let code = Vpd_emit.emit_module ~internal manifest in
      print_string code
  | [ input; "-o"; output ] ->
      let manifest = Vpd_parse.parse_file input in
      let code = Vpd_emit.emit_module ~internal manifest in
      let oc = open_out output in
      output_string oc code;
      close_out oc;
      Printf.eprintf "[vpd] Generated %d rules -> %s%s\n"
        (List.length manifest.rules)
        output
        (if internal then " (internal)" else "")
  | _ ->
      Printf.eprintf "Usage: %s <manifest.json> [-o <output.ml>] [--internal]\n"
        Sys.argv.(0);
      exit 2
