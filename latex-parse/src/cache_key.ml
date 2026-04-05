(* ══════════════════════════════════════════════════════════════════════
   Cache_key — result cache for validator engine (spec W19)

   Computes a cache key from (source_hash, validator_set_hash, language). Caches
   validator results to skip recomputation on unchanged input.
   ══════════════════════════════════════════════════════════════════════ *)

type cache_key = {
  source_hash : string;
  validator_count : int;
  language : string;
}

type 'a cache_entry = {
  _key : cache_key;
  results : 'a;
  created_at : float;
  ttl_seconds : float;
}

type 'a cache = {
  tbl : (string, 'a cache_entry) Hashtbl.t;
  mutable hits : int;
  mutable misses : int;
  default_ttl : float;
}

(* ── Hash computation ───────────────────────────────────────── *)

let hash_string (s : string) : string =
  (* Simple DJB2 hash — fast, sufficient for cache keys *)
  let h = ref 5381 in
  String.iter (fun c -> h := (!h * 33) + Char.code c) s;
  Printf.sprintf "%016x" !h

let compute_key ~(source : string) ~(validator_count : int) ~(language : string)
    : cache_key =
  { source_hash = hash_string source; validator_count; language }

let key_to_string (k : cache_key) : string =
  Printf.sprintf "%s:%d:%s" k.source_hash k.validator_count k.language

(* ── Cache operations ───────────────────────────────────────── *)

let create ?(default_ttl = 3600.0) () : 'a cache =
  { tbl = Hashtbl.create 64; hits = 0; misses = 0; default_ttl }

let lookup (c : 'a cache) (key : cache_key) : 'a option =
  let ks = key_to_string key in
  match Hashtbl.find_opt c.tbl ks with
  | Some entry ->
      let now = Unix.gettimeofday () in
      if now -. entry.created_at < entry.ttl_seconds then (
        c.hits <- c.hits + 1;
        Some entry.results)
      else (
        (* TTL expired *)
        Hashtbl.remove c.tbl ks;
        c.misses <- c.misses + 1;
        None)
  | None ->
      c.misses <- c.misses + 1;
      None

let store (c : 'a cache) (key : cache_key) (results : 'a) : unit =
  let ks = key_to_string key in
  Hashtbl.replace c.tbl ks
    {
      _key = key;
      results;
      created_at = Unix.gettimeofday ();
      ttl_seconds = c.default_ttl;
    }

let invalidate (c : 'a cache) (key : cache_key) : unit =
  Hashtbl.remove c.tbl (key_to_string key)

let clear (c : 'a cache) : unit = Hashtbl.clear c.tbl

let hit_rate (c : 'a cache) : float =
  let total = c.hits + c.misses in
  if total = 0 then 0.0 else float_of_int c.hits /. float_of_int total

let stats (c : 'a cache) : string =
  Printf.sprintf "hits=%d misses=%d rate=%.1f%% entries=%d" c.hits c.misses
    (hit_rate c *. 100.0)
    (Hashtbl.length c.tbl)

(* ── Global validator result cache ──────────────────────────── *)

let _global_cache : Validators_common.result list cache = create ()
let global () = _global_cache
