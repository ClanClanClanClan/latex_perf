(** Fault-injection testing framework for distributed system resilience. *)

type fault_type =
  | WorkerCrash of int
  | NetworkDelay of float
  | MemoryPressure of int
  | CPUSpike of float
  | IOBlock of float
  | RandomWorkerKill
  | BrokerOverload

type fault_config = {
  enabled : bool;
  probability : float;
  faults : fault_type list;
  seed : int option;
}

val configure :
  enabled:bool ->
  probability:float ->
  faults:fault_type list ->
  seed:int option ->
  unit
(** Set the global fault-injection configuration. *)

val inject_fault : fault_type -> unit
(** Inject a specific fault if the probability check passes. *)

val run_scenario : string -> int list -> string -> unit
(** [run_scenario name worker_pids socket_path] executes a named fault scenario. *)

val check_recovery : string -> bool
(** [check_recovery socket_path] attempts a health-check connection and returns
    [true] if the service responds. *)

val is_enabled : unit -> bool
val get_probability : unit -> float

val trigger_random_fault : unit -> unit
(** Pick a random fault from the configured list and inject it. *)

val inject_broker_overload : string -> int -> unit
(** [inject_broker_overload socket_path request_count] floods the broker with
    rapid connections for stress testing. *)
