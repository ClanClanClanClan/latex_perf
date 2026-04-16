(* ══════════════════════════════════════════════════════════════════════
   Build_artifact_state — thread-local build profile + log context

   Follows the same Hashtbl + Thread.id pattern as Validators_context and
   File_context. When set is called, also installs Log_parser context for
   backward compatibility with existing Class C rule implementations.
   ══════════════════════════════════════════════════════════════════════ *)

type t = { profile : Build_profile.t; log_context : Log_parser.log_context }

let _tbl : (int, t) Hashtbl.t = Hashtbl.create 4

let set (state : t) : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.replace _tbl tid state;
  Log_parser.set_log_context state.log_context

let get () : t option =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.find_opt _tbl tid

let clear () : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.remove _tbl tid;
  Log_parser.clear_log_context ()

let from_profile (bp : Build_profile.t) : t option =
  match bp.log_context with
  | Some ctx -> Some { profile = bp; log_context = ctx }
  | None -> None
