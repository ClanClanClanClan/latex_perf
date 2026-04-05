(** Result cache for validator engine (spec W19). *)

type cache_key = {
  source_hash : string;
  validator_count : int;
  language : string;
}

type 'a cache

val compute_key :
  source:string -> validator_count:int -> language:string -> cache_key

val key_to_string : cache_key -> string
val create : ?default_ttl:float -> unit -> 'a cache
val lookup : 'a cache -> cache_key -> 'a option
val store : 'a cache -> cache_key -> 'a -> unit
val invalidate : 'a cache -> cache_key -> unit
val clear : 'a cache -> unit
val hit_rate : 'a cache -> float
val stats : 'a cache -> string
val global : unit -> Validators_common.result list cache
