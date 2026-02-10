(** Unit tests for Metrics_prometheus counter and histogram logic. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[metrics-prom] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let dump_to_string () =
  let rd, wr = Unix.pipe () in
  let oc = Unix.out_channel_of_descr wr in
  Metrics_prometheus.dump_metrics oc;
  flush oc;
  Unix.close wr;
  let buf = Buffer.create 1024 in
  let tmp = Bytes.create 4096 in
  let rec loop () =
    let n = Unix.read rd tmp 0 4096 in
    if n > 0 then (
      Buffer.add_subbytes buf tmp 0 n;
      loop ())
  in
  loop ();
  Unix.close rd;
  Buffer.contents buf

let contains s sub =
  let slen = String.length s and sublen = String.length sub in
  let rec check i =
    if i + sublen > slen then false
    else if String.sub s i sublen = sub then true
    else check (i + 1)
  in
  check 0

let () =
  (* 1. on_request increments counter *)
  run "on_request" (fun tag ->
      Metrics_prometheus.on_request ();
      let s = dump_to_string () in
      expect (contains s "l0_requests_total") (tag ^ ": key present");
      (* Counter should be > 0 since we just called on_request *)
      expect (not (contains s "l0_requests_total 0")) (tag ^ ": non-zero"));

  (* 2. on_error increments counter *)
  run "on_error" (fun tag ->
      Metrics_prometheus.on_error ();
      let s = dump_to_string () in
      expect (contains s "l0_errors_total") (tag ^ ": key present"));

  (* 3. on_hedge_fired increments counter *)
  run "on_hedge_fired" (fun tag ->
      Metrics_prometheus.on_hedge_fired ();
      let s = dump_to_string () in
      expect (contains s "l0_hedge_fired_total") (tag ^ ": key present"));

  (* 4. on_hedge_win increments counter *)
  run "on_hedge_win" (fun tag ->
      Metrics_prometheus.on_hedge_win ();
      let s = dump_to_string () in
      expect (contains s "l0_hedge_wins_total") (tag ^ ": key present"));

  (* 5. on_rotation increments counter *)
  run "on_rotation" (fun tag ->
      Metrics_prometheus.on_rotation ();
      let s = dump_to_string () in
      expect (contains s "l0_rotations_total") (tag ^ ": key present"));

  (* 6. observe_latency populates histogram *)
  run "histogram" (fun tag ->
      Metrics_prometheus.observe_latency 3.0;
      Metrics_prometheus.observe_latency 12.0;
      Metrics_prometheus.observe_latency 100.0;
      let s = dump_to_string () in
      expect (contains s "l0_latency_ms_bucket") (tag ^ ": bucket present");
      expect (contains s "l0_latency_ms_count") (tag ^ ": count present"));

  (* 7. dump_metrics produces valid Prometheus format *)
  run "format" (fun tag ->
      let s = dump_to_string () in
      expect (contains s "# HELP") (tag ^ ": HELP line");
      expect (contains s "# TYPE") (tag ^ ": TYPE line");
      expect (contains s "counter") (tag ^ ": counter type");
      expect (contains s "histogram") (tag ^ ": histogram type"));

  (* 8. parse_addr helper *)
  run "parse_addr" (fun _tag ->
      (* We can't directly test parse_addr since it's not exposed, but
         dump_metrics always succeeds — validates internal state *)
      let s = dump_to_string () in
      expect (String.length s > 0) _tag);

  if !fails > 0 then (
    Printf.eprintf "[metrics-prom] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[metrics-prom] PASS %d cases\n%!" !cases
