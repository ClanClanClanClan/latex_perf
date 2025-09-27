(* Event-driven hedge timer - kqueue (macOS) / timerfd (Linux) *)

type t = { mutable timer_fd : Unix.file_descr option; mutable armed : bool }

external setup_hedge_timer_macos : unit -> int = "hedge_timer_setup_macos_stub"
external arm_hedge_timer : int -> int64 -> unit = "hedge_timer_arm_stub"
external disarm_hedge_timer : int -> unit = "hedge_timer_disarm_stub"

let create () =
  let fd_int = setup_hedge_timer_macos () in
  let fd = Obj.magic fd_int in
  (* Convert int to file_descr for kqueue *)
  { timer_fd = Some fd; armed = false }

let arm t ~ns =
  match t.timer_fd with
  | None -> failwith "hedge timer not initialized"
  | Some fd ->
      let fd_int = Obj.magic fd in
      arm_hedge_timer fd_int ns;
      t.armed <- true

let disarm t =
  if t.armed then
    match t.timer_fd with
    | None -> ()
    | Some fd ->
        let fd_int = Obj.magic fd in
        disarm_hedge_timer fd_int;
        t.armed <- false

let is_armed t = t.armed

(* Convenience function for millisecond timing *)
let arm_ms t ms =
  let ns = Int64.mul (Int64.of_int ms) 1_000_000L in
  arm t ~ns
