(** Live event bus for semantic deltas (spec W62). *)

type event =
  | LabelDefined of { key : string; position : int }
  | RefUsed of { key : string; position : int; command : string }
  | SectionStarted of { level : int; title : string; position : int }
  | EnvironmentOpened of { name : string; position : int }
  | EnvironmentClosed of { name : string; position : int }
  | DocumentBegin of int
  | DocumentEnd of int
  | TaskScheduled of { task_id : string; priority : float }
  | TaskCompleted of { task_id : string; elapsed_ms : float }

type handler = event -> unit
type bus

val create : unit -> bus
val subscribe : bus -> string -> handler -> unit
val unsubscribe : bus -> string -> unit
val publish : bus -> event -> unit
val event_count : bus -> int
val global : unit -> bus
val publish_global : event -> unit
val subscribe_global : string -> handler -> unit
val scan_and_publish : bus -> string -> unit
