(* ══════════════════════════════════════════════════════════════════════
   User_macro_context — thread-local user macro registry

   Follows the same Hashtbl + Thread.id pattern as File_context, Log_parser,
   Build_artifact_state, and Validators_context.
   ══════════════════════════════════════════════════════════════════════ *)

let _tbl : (int, User_macro_registry.registry) Hashtbl.t = Hashtbl.create 4

let set (reg : User_macro_registry.registry) : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.replace _tbl tid reg

let get () : User_macro_registry.registry option =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.find_opt _tbl tid

let clear () : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.remove _tbl tid
