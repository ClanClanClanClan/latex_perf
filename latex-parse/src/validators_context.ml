(* Per-thread expander summary context for validators *)

type post_command = { name: string; s: int; e: int }

let tbl : (int, post_command list) Hashtbl.t = Hashtbl.create 16

let set_post_commands (xs:post_command list) : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.replace tbl tid xs

let get_post_commands () : post_command list =
  let tid = Thread.id (Thread.self ()) in
  match Hashtbl.find_opt tbl tid with
  | Some xs -> xs
  | None -> []

let clear () : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.remove tbl tid

