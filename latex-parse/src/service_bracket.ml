type stamps = {
  mutable t_in_start : int64;
  mutable t_in_done : int64;
  mutable t_proc_start : int64;
  mutable t_hedge_fire : int64;
  mutable t_first_reply : int64;
  mutable t_reply_ready : int64;
}

let make () =
  {
    t_in_start = 0L;
    t_in_done = 0L;
    t_proc_start = 0L;
    t_hedge_fire = 0L;
    t_first_reply = 0L;
    t_reply_ready = 0L;
  }

let measure_bytes_in_to_reply_ready ~(recv : unit -> bytes)
    ~(process : bytes -> 'r) ~(format : 'r -> bytes) ~(send : bytes -> unit) =
  let st = make () in
  st.t_in_start <- Clock.now ();
  let req = recv () in
  st.t_in_done <- Clock.now ();
  st.t_proc_start <- st.t_in_done;
  let res = process req in
  let reply = format res in
  st.t_reply_ready <- Clock.now ();
  send reply;
  (Clock.ms_of_ns Int64.(sub st.t_reply_ready st.t_in_start), st)
