let _tbl : (int, Partial_cst.partial_document) Hashtbl.t = Hashtbl.create 4

let set (pd : Partial_cst.partial_document) : unit =
  Hashtbl.replace _tbl (Thread.id (Thread.self ())) pd

let get () : Partial_cst.partial_document option =
  Hashtbl.find_opt _tbl (Thread.id (Thread.self ()))

let clear () : unit = Hashtbl.remove _tbl (Thread.id (Thread.self ()))
