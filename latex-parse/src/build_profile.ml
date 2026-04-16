(* ══════════════════════════════════════════════════════════════════════
   Build_profile — compile-log discovery and activation for Class C rules

   Encapsulates finding a .log file, parsing it via Log_parser, and installing
   the log context so that log-dependent validators fire.
   ══════════════════════════════════════════════════════════════════════ *)

type engine = PDFLaTeX | XeLaTeX | LuaLaTeX | LaTeX | Unknown

type t = {
  engine : engine;
  log_path : string option;
  tex_path : string;
  base_dir : string;
  log_context : Log_parser.log_context option;
  log_mtime : float option;
  source_mtime : float option;
}

let read_file path =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      let n = in_channel_length ic in
      really_input_string ic n)

let mtime_of path =
  try Some (Unix.stat path).st_mtime with Unix.Unix_error _ -> None

let log_path_for_tex tex_path =
  try
    let base = Filename.chop_extension tex_path in
    let candidate = base ^ ".log" in
    if Sys.file_exists candidate then Some candidate else None
  with Invalid_argument _ -> None

let detect_engine (content : string) : engine =
  if
    String.length content > 200
    &&
    let prefix = String.sub content 0 (min 200 (String.length content)) in
    try
      ignore
        (Re_compat.search_forward (Re_compat.regexp_string "XeTeX") prefix 0);
      true
    with Not_found -> false
  then XeLaTeX
  else if
    String.length content > 200
    &&
    let prefix = String.sub content 0 (min 200 (String.length content)) in
    try
      ignore
        (Re_compat.search_forward (Re_compat.regexp_string "LuaTeX") prefix 0);
      true
    with Not_found -> false
  then LuaLaTeX
  else if
    String.length content > 200
    &&
    let prefix = String.sub content 0 (min 200 (String.length content)) in
    try
      ignore
        (Re_compat.search_forward (Re_compat.regexp_string "pdfTeX") prefix 0);
      true
    with Not_found -> false
  then PDFLaTeX
  else Unknown

let engine_to_string = function
  | PDFLaTeX -> "pdflatex"
  | XeLaTeX -> "xelatex"
  | LuaLaTeX -> "lualatex"
  | LaTeX -> "latex"
  | Unknown -> "unknown"

let create ~(tex_path : string) ~(base_dir : string) : t =
  {
    engine = Unknown;
    log_path = None;
    tex_path;
    base_dir;
    log_context = None;
    log_mtime = None;
    source_mtime = mtime_of tex_path;
  }

let load_log_from ~(log_path : string) (bp : t) : t =
  try
    let content = read_file log_path in
    let ctx = Log_parser.parse_log content in
    let engine = detect_engine content in
    {
      bp with
      log_path = Some log_path;
      log_context = Some ctx;
      log_mtime = mtime_of log_path;
      engine;
    }
  with Sys_error _ -> bp

let load_log (bp : t) : t =
  match log_path_for_tex bp.tex_path with
  | Some lp -> load_log_from ~log_path:lp bp
  | None -> bp

let is_stale (bp : t) : bool =
  match (bp.log_mtime, bp.source_mtime) with
  | Some lm, Some sm -> lm < sm
  | _ -> false

let activate (bp : t) : unit =
  match bp.log_context with
  | Some ctx -> Log_parser.set_log_context ctx
  | None -> ()

let deactivate () : unit = Log_parser.clear_log_context ()
let has_log (bp : t) : bool = bp.log_context <> None
