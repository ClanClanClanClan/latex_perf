(** SIMD tokeniser worker process.

    Each worker runs in a forked child process, listening for IPC requests on
    the given file descriptor, performing SIMD tokenisation, and replying with
    results. Workers self-retire after exceeding allocation or major-cycle
    budgets. *)

val start_loop : Unix.file_descr -> core:int -> unit
(** [start_loop fd ~core] enters the request loop. Does not return under normal
    operation (exits the process on HUP or retirement). *)
