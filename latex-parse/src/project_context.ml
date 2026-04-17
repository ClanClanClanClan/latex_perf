let _tbl : (int, Project_state.project_state) Hashtbl.t = Hashtbl.create 4

let set (st : Project_state.project_state) : unit =
  Hashtbl.replace _tbl (Thread.id (Thread.self ())) st

let get () : Project_state.project_state option =
  Hashtbl.find_opt _tbl (Thread.id (Thread.self ()))

let clear () : unit = Hashtbl.remove _tbl (Thread.id (Thread.self ()))
