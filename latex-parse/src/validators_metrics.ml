open Printf

module T = struct
  type agg = {
    mutable hits : int;
    mutable dur_ms : float;
    mutable last_count : int;
  }
end

let mu = Mutex.create ()
let tbl : (string, T.agg) Hashtbl.t = Hashtbl.create 97

let record ~(id : string) ~(count : int) ~(dur_ms : float) =
  Mutex.lock mu;
  let a =
    match Hashtbl.find_opt tbl id with
    | Some x -> x
    | None ->
        let x = { T.hits = 0; dur_ms = 0.; last_count = 0 } in
        Hashtbl.add tbl id x;
        x
  in
  a.T.hits <- a.T.hits + 1;
  a.T.dur_ms <- a.T.dur_ms +. dur_ms;
  a.T.last_count <- count;
  Mutex.unlock mu

let dump_prometheus oc =
  Mutex.lock mu;
  Hashtbl.iter
    (fun id a ->
      fprintf oc "validators_rule_hits_total{id=\"%s\"} %d\n" id a.T.hits;
      fprintf oc "validators_rule_duration_ms_sum{id=\"%s\"} %.6f\n" id
        a.T.dur_ms;
      fprintf oc "validators_rule_last_count{id=\"%s\"} %d\n" id a.T.last_count)
    tbl;
  Mutex.unlock mu
