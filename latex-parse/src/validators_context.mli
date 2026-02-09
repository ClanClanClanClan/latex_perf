(** Per-thread context storage for LaTeX command spans used by validators. *)

type post_command = { name : string; s : int; e : int }

val set_post_commands : post_command list -> unit
(** Store the command list for the current thread. *)

val get_post_commands : unit -> post_command list
(** Retrieve the command list for the current thread (empty if unset). *)

val clear : unit -> unit
(** Remove the stored commands for the current thread. *)
