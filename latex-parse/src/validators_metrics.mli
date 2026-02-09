(** Prometheus metrics aggregation for validator rule execution. *)

val record : id:string -> count:int -> dur_ms:float -> unit
(** Record a rule evaluation with its hit count and duration. *)

val dump_prometheus : out_channel -> unit
(** Write all accumulated rule metrics in Prometheus text format. *)
