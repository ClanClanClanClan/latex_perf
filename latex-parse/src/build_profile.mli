(** Build profile: encapsulates finding, loading, and activating a LaTeX compile
    log for Class C rule execution.

    Usage:
    {[
      let bp = Build_profile.create ~tex_path:"paper.tex" ~base_dir:"." in
      let bp = Build_profile.load_log bp in
      Build_profile.activate bp;
      Fun.protect ~finally:Build_profile.deactivate (fun () ->
          Validators.run_with_policy Execution_policy.with_build src)
    ]} *)

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

val create : tex_path:string -> base_dir:string -> t
(** [create ~tex_path ~base_dir] builds a profile. Does not read the log yet. *)

val load_log : t -> t
(** Auto-detect sibling [.log] file, read and parse it. Populates [log_context],
    [log_path], [log_mtime]. Also detects engine from log. *)

val load_log_from : log_path:string -> t -> t
(** Load a specific [.log] file. *)

val detect_engine : string -> engine
(** Detect engine from log file content. *)

val engine_to_string : engine -> string

val is_stale : t -> bool
(** [true] if the log file is older than the source file. *)

val activate : t -> unit
(** Installs log context via {!Log_parser.set_log_context}. *)

val deactivate : unit -> unit
(** Clears log context via {!Log_parser.clear_log_context}. *)

val has_log : t -> bool
(** [true] if a log file was found and parsed. *)
