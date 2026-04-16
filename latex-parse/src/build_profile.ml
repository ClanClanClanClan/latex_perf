(* ══════════════════════════════════════════════════════════════════════
   Build_profile — compile-log discovery and activation for Class C rules

   Encapsulates finding a .log file, parsing it via Log_parser, and installing
   the log context so that log-dependent validators fire.
   ══════════════════════════════════════════════════════════════════════ *)

type t = {
  tex_path : string;
  log_path : string option;
  log_context : Log_parser.log_context option;
}

let read_file path =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      let n = in_channel_length ic in
      really_input_string ic n)

let log_path_for_tex tex_path =
  try
    let base = Filename.chop_extension tex_path in
    let candidate = base ^ ".log" in
    if Sys.file_exists candidate then Some candidate else None
  with Invalid_argument _ -> None

let load_log_from_path path =
  try
    let content = read_file path in
    Some (Log_parser.parse_log content)
  with Sys_error _ -> None

let create (tex_path : string) : t =
  let log_path = log_path_for_tex tex_path in
  let log_context =
    match log_path with Some p -> load_log_from_path p | None -> None
  in
  { tex_path; log_path; log_context }

let create_with_log ~(tex_path : string) ~(log_path : string) : t =
  let log_context = load_log_from_path log_path in
  { tex_path; log_path = Some log_path; log_context }

let activate (bp : t) : unit =
  match bp.log_context with
  | Some ctx -> Log_parser.set_log_context ctx
  | None -> ()

let deactivate () : unit = Log_parser.clear_log_context ()
let has_log (bp : t) : bool = bp.log_context <> None
