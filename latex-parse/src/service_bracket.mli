(** Request-response timing instrumentation for service latency measurement. *)

type stamps = {
  mutable t_in_start : int64;
  mutable t_in_done : int64;
  mutable t_proc_start : int64;
  mutable t_hedge_fire : int64;
  mutable t_first_reply : int64;
  mutable t_reply_ready : int64;
}

val make : unit -> stamps
(** Create a zeroed timestamp record. *)

val measure_bytes_in_to_reply_ready :
  recv:(unit -> bytes) ->
  process:(bytes -> 'r) ->
  format:('r -> bytes) ->
  send:(bytes -> unit) ->
  float * stamps
(** Run the recv/process/format/send pipeline, returning (elapsed_ms, stamps). *)
