(** Minimal Prometheus metrics exporter.

    Enable with [L0_PROM=1]. Configuration:
    - [L0_PROM_ADDR="HOST:PORT"] (default 127.0.0.1:9109)
    - [L0_PROM_UDS="/path/to/socket"] (Unix domain socket, takes precedence) *)

val on_request : unit -> unit
val on_error : unit -> unit
val on_hedge_fired : unit -> unit
val on_hedge_win : unit -> unit
val on_rotation : unit -> unit
val observe_latency : float -> unit

val dump_metrics : out_channel -> unit
(** Write all metrics in Prometheus exposition format to the given channel. *)

val serve : unit -> unit
(** Start the HTTP metrics server in the current thread. Does not return under
    normal operation. *)
