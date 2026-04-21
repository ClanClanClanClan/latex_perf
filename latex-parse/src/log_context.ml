(** Compile-log context facade. See [log_context.mli]. *)

type t = Log_parser.log_context

let empty : t = Log_parser.empty_context
let parse : string -> t = Log_parser.parse_log
let set : t -> unit = Log_parser.set_log_context
let get : unit -> t option = Log_parser.get_log_context
let clear : unit -> unit = Log_parser.clear_log_context
let is_active () : bool = Option.is_some (Log_parser.get_log_context ())
