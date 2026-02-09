(** Unix-domain socket service loop with hedged-request broker integration. *)

val run : unit -> unit
(** Start the service: bind the socket, spawn the broker pool, and accept
    connections in a loop. Does not return under normal operation. *)
