(** Build profile: encapsulates finding, loading, and activating a LaTeX compile
    log for Class C rule execution.

    Usage:
    {[
      let bp = Build_profile.create "paper.tex" in
      Build_profile.activate bp;
      Fun.protect ~finally:Build_profile.deactivate (fun () ->
          Validators.run_with_build src)
    ]} *)

type t = {
  tex_path : string;
  log_path : string option;
  log_context : Log_parser.log_context option;
}

val create : string -> t
(** [create tex_path] auto-detects a sibling [.log] file (same basename, same
    directory). Reads and parses it if found. *)

val create_with_log : tex_path:string -> log_path:string -> t
(** [create_with_log ~tex_path ~log_path] loads the specified log file. *)

val activate : t -> unit
(** Installs the log context (if any) via {!Log_parser.set_log_context} so that
    Class C rules can read it. *)

val deactivate : unit -> unit
(** Clears the log context via {!Log_parser.clear_log_context}. *)

val has_log : t -> bool
(** [true] if a log file was found and parsed. *)
