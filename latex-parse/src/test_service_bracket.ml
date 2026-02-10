(** Unit tests for Service_bracket pipeline timing. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[svc-bracket] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. make() returns all-zero stamps *)
  run "make zeros" (fun tag ->
      let st = Service_bracket.make () in
      expect (st.t_in_start = 0L) (tag ^ ": t_in_start");
      expect (st.t_in_done = 0L) (tag ^ ": t_in_done");
      expect (st.t_proc_start = 0L) (tag ^ ": t_proc_start");
      expect (st.t_hedge_fire = 0L) (tag ^ ": t_hedge_fire");
      expect (st.t_first_reply = 0L) (tag ^ ": t_first_reply");
      expect (st.t_reply_ready = 0L) (tag ^ ": t_reply_ready"));

  (* 2. measure returns non-negative elapsed_ms *)
  run "non-negative elapsed" (fun tag ->
      let ms, _st =
        Service_bracket.measure_bytes_in_to_reply_ready
          ~recv:(fun () -> Bytes.of_string "test")
          ~process:(fun b -> b)
          ~format:(fun b -> b)
          ~send:(fun _ -> ())
      in
      expect (ms >= 0.0) (tag ^ Printf.sprintf ": got %.3f" ms));

  (* 3. Stamps are populated after measurement *)
  run "stamps populated" (fun tag ->
      let _ms, st =
        Service_bracket.measure_bytes_in_to_reply_ready
          ~recv:(fun () -> Bytes.of_string "x")
          ~process:(fun b -> b)
          ~format:(fun b -> b)
          ~send:(fun _ -> ())
      in
      expect (st.t_in_start > 0L) (tag ^ ": t_in_start > 0");
      expect (st.t_in_done >= st.t_in_start) (tag ^ ": t_in_done >= start");
      expect
        (st.t_reply_ready >= st.t_in_done)
        (tag ^ ": t_reply_ready >= in_done"));

  (* 4. Elapsed reflects work *)
  run "timing accuracy" (fun tag ->
      let ms, _st =
        Service_bracket.measure_bytes_in_to_reply_ready
          ~recv:(fun () -> Bytes.of_string "x")
          ~process:(fun b ->
            Unix.sleepf 0.010;
            b)
          ~format:(fun b -> b)
          ~send:(fun _ -> ())
      in
      expect (ms >= 7.0) (tag ^ Printf.sprintf ": expected >= 7ms, got %.3f" ms));

  (* 5. Stamp ordering invariant *)
  run "stamp ordering" (fun tag ->
      let _ms, st =
        Service_bracket.measure_bytes_in_to_reply_ready
          ~recv:(fun () -> Bytes.of_string "x")
          ~process:(fun b -> b)
          ~format:(fun b -> b)
          ~send:(fun _ -> ())
      in
      expect
        (st.t_in_start <= st.t_in_done && st.t_in_done <= st.t_reply_ready)
        tag);

  (* 6. Each callback called exactly once *)
  run "callback counts" (fun tag ->
      let recv_n = ref 0 in
      let proc_n = ref 0 in
      let fmt_n = ref 0 in
      let send_n = ref 0 in
      let _ms, _st =
        Service_bracket.measure_bytes_in_to_reply_ready
          ~recv:(fun () ->
            incr recv_n;
            Bytes.of_string "x")
          ~process:(fun b ->
            incr proc_n;
            b)
          ~format:(fun b ->
            incr fmt_n;
            b)
          ~send:(fun _ -> incr send_n)
      in
      expect (!recv_n = 1) (tag ^ ": recv");
      expect (!proc_n = 1) (tag ^ ": process");
      expect (!fmt_n = 1) (tag ^ ": format");
      expect (!send_n = 1) (tag ^ ": send"));

  if !fails > 0 then (
    Printf.eprintf "[svc-bracket] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[svc-bracket] PASS %d cases\n%!" !cases
