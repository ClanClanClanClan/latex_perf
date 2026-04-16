(** Build artifact state: thread-local build profile and log context.

    Wraps {!Build_profile} and {!Log_parser} into a single state object. When
    {!set} is called, it also installs the log context via
    {!Log_parser.set_log_context} so existing Class C rules work unchanged. *)

type t = { profile : Build_profile.t; log_context : Log_parser.log_context }

val set : t -> unit
(** Store state for the current thread. Also sets {!Log_parser.set_log_context}. *)

val get : unit -> t option
(** Retrieve state for the current thread. *)

val clear : unit -> unit
(** Clear state and log context for the current thread. *)

val from_profile : Build_profile.t -> t option
(** Create state from a loaded build profile. Returns [None] if no log context. *)
