open Ipc

type wstate = Hot | Cooling
type worker = {
  mutable fd       : Unix.file_descr;
  mutable pid      : int;
  core             : int;
  mutable state    : wstate;
  mutable inflight : bool;
  mutable alloc_mb : float;
  mutable major    : int;
}

let spawn_worker ~core =
  let sv, sc = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.set_close_on_exec sv; Unix.set_close_on_exec sc;
  match Unix.fork () with
  | 0 -> Unix.close sv; (Worker.start_loop sc ~core : unit); exit 0
  | pid ->
      Unix.close sc; Unix.clear_nonblock sv;
      { fd=sv; pid; core; state=Hot; inflight=false; alloc_mb=0.0; major=0 }

type pool = {
  workers: worker array;
  mutable rr: int;
  timer: Hedge_timer.t;
  mutable requests: int;
  mutable hedge_fired: int;
  mutable hedge_wins: int;
  mutable rotations: int;
}

let init_pool cores =
  { workers = Array.mapi (fun _ c -> spawn_worker ~core:c) cores;
    rr=0; timer=Hedge_timer.create ();
    requests=0; hedge_fired=0; hedge_wins=0; rotations=0; }

let pick_hot p =
  let n = Array.length p.workers in
  let rec go i k =
    if k>=n then p.workers.(i mod n) else
    let w = p.workers.(i mod n) in
    if w.state=Hot && not w.inflight then (p.rr <- i+1; w)
    else go (i+1) (k+1)
  in go p.rr 0

let pick_secondary p primary =
  let n = Array.length p.workers in
  let rec go i k =
    if k>=n then primary else
    let w = p.workers.(i mod n) in
    if w != primary && w.state=Hot && not w.inflight then w else go (i+1) (k+1)
  in go p.rr 1

(* CRITICAL FIX: Ultra-aggressive rotation for P99.9 tail latency *)
let update_on_resp _p w ~alloc_mb10 ~major =
  w.inflight <- false;
  w.alloc_mb <- float alloc_mb10 /. 10.0;
  w.major    <- major;
  (* CRITICAL FIX: Even more aggressive thresholds for P99.9 *)
  let ultra_aggressive_threshold = float Config.worker_alloc_budget_mb *. 0.6 in
  if (w.alloc_mb >= ultra_aggressive_threshold ||
      w.major    >= (Config.worker_major_cycles_budget - 1) ||  (* Rotate 1 cycle earlier *)
      (w.alloc_mb >= 150.0 && w.major >= 1)) && w.state=Hot  (* Very early rotation *)
  then w.state <- Cooling

let maybe_rotate p w =
  if w.state=Cooling && not w.inflight then (
    (try Unix.close w.fd with _->());
    (try ignore (Unix.waitpid [] w.pid) with _->());
    let nw = spawn_worker ~core:w.core in
    w.fd <- nw.fd; w.pid <- nw.pid; w.state <- Hot; w.inflight <- false;
    w.alloc_mb <- 0.0; w.major <- 0; p.rotations <- p.rotations + 1;
    Metrics_prometheus.on_rotation ()
  )

let inflight_total p =
  Array.fold_left (fun acc w -> acc + (if w.inflight then 1 else 0)) 0 p.workers

let int_of_fd (fd:Unix.file_descr) : int = (Obj.magic fd : int)

let find_by_fd p fd =
  let rec loop i =
    if i = Array.length p.workers then None
    else
      let w = p.workers.(i) in
      if int_of_fd w.fd = fd then Some w else loop (i+1)
  in loop 0

let req_ctr = ref 0L
let next_req_id () = let id = !req_ctr in req_ctr := Int64.succ id; id

let drain_one_ready ~deadline_ns p =
  let fd1 =
    if p.workers.(0).inflight then int_of_fd p.workers.(0).fd else -1 in
  let fd2 =
    if p.workers.(1).inflight then int_of_fd p.workers.(1).fd else -1 in
  if fd1 < 0 && fd2 < 0 then () else begin
    let tf, ready = Hedge_timer.wait_two p.timer ~fd1 ~fd2 in
    ignore tf;
    if ready >= 0 then
      match find_by_fd p (Obj.magic ready) with
      | None -> ()
      | Some w ->
          begin match Ipc.read_any w.fd with
          | Any_resp (_rid, _st, _nt, _iss, mb10, maj) ->
              update_on_resp p w ~alloc_mb10:mb10 ~major:maj; maybe_rotate p w
          | Any_hup ->
              w.inflight <- false; maybe_rotate p w
          | _ -> ()
          end
    else ()
  end;
  (* CRITICAL FIX: More graceful timeout handling for P99.9 *)
  if Int64.sub (Clock.now ()) deadline_ns > 0L then (
    (* Try to recover by marking stuck workers as not inflight *)
    Array.iter (fun w -> if w.inflight then w.inflight <- false) p.workers;
    Printf.eprintf "[broker] WARNING: Timeout recovery - cleared inflight flags\n%!"
  )

type svc_result = { status:int; n_tokens:int; issues_len:int; origin:[`P|`H]; hedge_fired: bool }

let rescue_once p ~req_id ~(input:bytes) : svc_result =
  Array.iter (maybe_rotate p) p.workers;
  let w = pick_hot p in
  w.inflight <- true;
  Ipc.write_req w.fd ~req_id ~bytes:input;
  match Ipc.read_any w.fd with
  | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
      update_on_resp p w ~alloc_mb10:mb10 ~major:maj; maybe_rotate p w;
      { status=st; n_tokens=nt; issues_len=iss; origin=`P; hedge_fired=false }
  | Any_hup ->
      w.inflight <- false; maybe_rotate p w;
      failwith "broker: rescue failed (HUP)"
  | _ -> failwith "broker: rescue unexpected"

let hedged_call p ~(input:bytes) ~(hedge_ms:int) : svc_result =
  (* CRITICAL FIX: Further reduced timeout to 200ms for aggressive P99.9 *)
  let deadline = Int64.add (Clock.now ()) (Clock.ns_of_ms 200) in
  while inflight_total p >= Array.length p.workers do
    drain_one_ready ~deadline_ns:deadline p
  done;

  let req_id  = next_req_id () in
  let primary = pick_hot p in
  primary.inflight <- true;
  Ipc.write_req primary.fd ~req_id ~bytes:input;

  Hedge_timer.arm p.timer ~ns:(Clock.ns_of_ms hedge_ms);
  p.requests <- p.requests + 1;

  let rec wait_primary_or_timer () =
    let tf, ready = Hedge_timer.wait_two p.timer
        ~fd1:(int_of_fd primary.fd) ~fd2:(-1)
    in
    if ready = int_of_fd primary.fd then `Primary_ready
    else if tf = 1 then `Hedge_fire else wait_primary_or_timer ()
  in

  match wait_primary_or_timer () with
  | `Primary_ready ->
      begin match Ipc.read_any primary.fd with
      | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
          update_on_resp p primary ~alloc_mb10:mb10 ~major:maj; maybe_rotate p primary;
          { status=st; n_tokens=nt; issues_len=iss; origin=`P; hedge_fired=false }
      | Any_hup ->
          primary.inflight <- false; maybe_rotate p primary;
          let sec = pick_secondary p primary in
          sec.inflight <- true; Ipc.write_req sec.fd ~req_id ~bytes:input;
          begin match Ipc.read_any sec.fd with
          | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
              update_on_resp p sec ~alloc_mb10:mb10 ~major:maj; maybe_rotate p sec;
              { status=st; n_tokens=nt; issues_len=iss; origin=`H; hedge_fired=true }
          | Any_hup ->
              sec.inflight <- false; maybe_rotate p sec;
              rescue_once p ~req_id ~input
          | _ -> rescue_once p ~req_id ~input
          end
      | _ -> rescue_once p ~req_id ~input
      end

  | `Hedge_fire ->
      p.hedge_fired <- p.hedge_fired + 1;
      Metrics_prometheus.on_hedge_fired ();
      let sec = pick_secondary p primary in
      sec.inflight <- true; Ipc.write_req sec.fd ~req_id ~bytes:input;
      let rec race () =
        let _tf, ready = Hedge_timer.wait_two p.timer
            ~fd1:(int_of_fd primary.fd) ~fd2:(int_of_fd sec.fd) in
        if ready = int_of_fd primary.fd then
          begin match Ipc.read_any primary.fd with
          | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
              update_on_resp p primary ~alloc_mb10:mb10 ~major:maj; maybe_rotate p primary;
              Ipc.write_cancel sec.fd ~req_id; sec.inflight <- false;
              { status=st; n_tokens=nt; issues_len=iss; origin=`P; hedge_fired=true }
          | Any_hup ->
              primary.inflight <- false; maybe_rotate p primary; race ()
          | _ -> race ()
          end
        else if ready = int_of_fd sec.fd then
          begin match Ipc.read_any sec.fd with
          | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
              update_on_resp p sec ~alloc_mb10:mb10 ~major:maj; maybe_rotate p sec;
              Ipc.write_cancel primary.fd ~req_id; primary.inflight <- false;
              p.hedge_wins <- p.hedge_wins + 1;
              Metrics_prometheus.on_hedge_win ();
              { status=st; n_tokens=nt; issues_len=iss; origin=`H; hedge_fired=true }
          | Any_hup ->
              sec.inflight <- false; maybe_rotate p sec; race ()
          | _ -> race ()
          end
        else race ()
      in race ()
