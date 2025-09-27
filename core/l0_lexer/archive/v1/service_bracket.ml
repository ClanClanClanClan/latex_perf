(* Service measurement timing bracket (§3.6) - Enhanced with SIMD.md 5-stamp
   timing *)

(* Advanced service timing with 5 stamps for tail diagnosis *)
type service_timing = {
  mutable t_in_start : int64; (* When request bytes start arriving *)
  mutable t_in_done : int64; (* When request bytes fully received *)
  mutable t_proc_start : int64; (* When processing starts *)
  mutable t_hedge_fire : int64; (* When hedge timer fires (0L if no hedge) *)
  mutable t_first_reply : int64; (* When first reply arrives *)
  mutable t_reply_ready : int64; (* When reply is ready to send *)
}

(* Backward compatibility: simple timing *)
type simple_timing = {
  bytes_in_ns : int64; (* t_in_start for compatibility *)
  reply_ready_ns : int64; (* t_reply_ready for compatibility *)
}

type measurement = {
  service_ns : int64; (* t_reply_ready - t_in_start *)
  token_count : int;
  digest : int64;
  path : string; (* "primary", "secondary", "in-process", "hedge" *)
}

(* Enhanced timing functions with SIMD.md § 3.6 support *)

let make () =
  let t = Clock.now_ns () in
  {
    t_in_start = t;
    t_in_done = 0L;
    t_proc_start = 0L;
    t_hedge_fire = 0L;
    t_first_reply = 0L;
    t_reply_ready = 0L;
  }

let stamp_in_done st = { st with t_in_done = Clock.now_ns () }
let stamp_proc_start st = { st with t_proc_start = Clock.now_ns () }
let stamp_hedge_fire st = { st with t_hedge_fire = Clock.now_ns () }
let stamp_first_reply st = { st with t_first_reply = Clock.now_ns () }
let stamp_reply_ready st = { st with t_reply_ready = Clock.now_ns () }

let measure_bytes_in_to_reply_ready ~recv ~process ~format ~send =
  let st = make () in
  let req = recv () in
  let st = stamp_in_done st in
  let st = stamp_proc_start st in
  let result = process req in
  let st = stamp_first_reply st in
  let reply = format result in
  let st = stamp_reply_ready st in
  send reply;
  let ms_total =
    Int64.to_float (Int64.sub st.t_reply_ready st.t_in_start) /. 1_000_000.0
  in
  (ms_total, st)

(* Backward compatibility functions *)
let create_timing () =
  let now = Clock.now_ns () in
  { bytes_in_ns = now; reply_ready_ns = 0L }

let complete_timing timing = { timing with reply_ready_ns = Clock.now_ns () }

let calculate_service_time timing =
  Int64.sub timing.reply_ready_ns timing.bytes_in_ns

let create_measurement timing token_count digest path =
  { service_ns = calculate_service_time timing; token_count; digest; path }

(* Convert nanoseconds to milliseconds for reporting *)
let ns_to_ms ns = Int64.to_float ns /. 1_000_000.0

let measurement_to_string m =
  Printf.sprintf "%.3fms (%d tokens, path=%s)" (ns_to_ms m.service_ns)
    m.token_count m.path
