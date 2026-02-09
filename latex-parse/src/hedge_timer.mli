(** Hedge timer for speculative RPC retries.

    Wraps a timerfd (Linux) or kqueue timer (macOS) via C FFI. *)

type t
(** Opaque timer handle. *)

val create : unit -> t
(** Create a new hedge timer. *)

val arm : t -> ns:int64 -> unit
(** Arm the timer to fire after [ns] nanoseconds. *)

val wait_two : t -> fd1:int -> fd2:int -> int * int
(** [wait_two t ~fd1 ~fd2] waits for either [fd1], [fd2], or the timer to become
    ready. Returns [(timer_fired, ready_fd)] where [timer_fired] is [1] if the
    timer expired and [ready_fd] is the file descriptor that became readable (or
    [-1] if none). *)
