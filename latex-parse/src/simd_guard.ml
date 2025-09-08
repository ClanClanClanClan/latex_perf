external cpu_supported : unit -> bool = "ocaml_simd_cpu_supported"
external symbol_linked : unit -> bool = "ocaml_simd_symbol_linked"

let env_allow_scalar () =
  match Sys.getenv_opt "L0_ALLOW_SCALAR" with
  | Some "1" | Some "true" | Some "TRUE" -> true
  | _ -> false

let require ?(allow_scalar_env=true) () =
  let allow_scalar = allow_scalar_env && env_allow_scalar () in
  let cpu_ok   = cpu_supported () in
  let sym_ok   = symbol_linked () in
  if Config.require_simd && not allow_scalar then begin
    if not cpu_ok then failwith "SIMD_v2: CPU SIMD not supported (refusing to start)";
    if not sym_ok then failwith "SIMD_v2: SIMD library not linked/force-loaded (refusing to start)";
  end;
  (cpu_ok, sym_ok, allow_scalar)