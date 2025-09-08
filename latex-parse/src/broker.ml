(* latex-parse/src/broker.ml - Fixed version matching spec *)
open Ipc

(* ---------- Worker model ---------- *)

type wstate = Hot | Cooling
type worker = {
  mutable fd       : Unix.file_descr;
  mutable pid      : int;
  core             : int;
  mutable state    : wstate;
  mutable inflight : bool;   (* at most one inflight per worker *)
  mutable alloc_mb : float;  (* per‑spawn delta, updated from replies *)
  mutable major    : int;    (* per‑spawn delta, updated from replies *)
}

let spawn_worker ~core =
  let sv, sc = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.set_close_on_exec sv; Unix.set_close_on_exec sc;
  match Unix.fork () with
  | 0 ->
      Unix.close sv;
      (Worker.start_loop sc ~core : unit); exit 0
  | pid ->
      Unix.close sc;
      (* Keep the socket blocking; the broker reads synchronously *)
      Unix.clear_nonblock sv;
      { fd=sv; pid; core; state=Hot; inflight=false; alloc_mb=0.0; major=0 }

type pool = {
  workers        : worker array;
  mutable rr     : int;
  timer          : Hedge_timer.t;
  mutable requests     : int;
  mutable hedge_fired  : int;
  mutable hedge_wins   : int;
  mutable rotations    : int;
}

let init_pool cores = {
  workers = Array.mapi (fun _ c -> spawn_worker ~core:c) cores;
  rr=0; timer=Hedge_timer.create ();
  requests=0; hedge_fired=0; hedge_wins=0; rotations=0;
}

let pick_hot p =
  let n = Array.length p.workers in
  let rec find i tries =
    if tries >= n then p.workers.(i mod n) else
    let w = p.workers.(i mod n) in
    if w.state=Hot && not w.inflight then (p.rr <- i+1; w)
    else find (i+1) (tries+1)
  in find p.rr 0

let pick_secondary p primary =
  let n = Array.length p.workers in
  let rec find i tries =
    if tries >= n then primary else
    let w = p.workers.(i mod n) in
    if (w != primary) && w.state=Hot && not w.inflight then w
    else find (i+1) (tries+1)
  in find p.rr 1

let update_on_resp _p w ~alloc_mb10 ~major =
  w.inflight <- false;
  w.alloc_mb <- float alloc_mb10 /. 10.0; 
  w.major <- major;
  if (w.alloc_mb >= float Config.worker_alloc_budget_mb ||
      w.major    >= Config.worker_major_cycles_budget) && w.state=Hot
  then w.state <- Cooling

let maybe_rotate p w =
  if w.state=Cooling && not w.inflight then (
    (try Unix.close w.fd with _->());
    (try ignore (Unix.waitpid [] w.pid) with _->());
    let nw = spawn_worker ~core:w.core in
    w.fd <- nw.fd; w.pid <- nw.pid; w.state <- Hot; w.inflight <- false;
    w.alloc_mb <- 0.0; w.major <- 0; p.rotations <- p.rotations + 1
  )
  
let force_rotate p w =
  (try Unix.close w.fd with _->());
  (try ignore (Unix.waitpid [] w.pid) with _->());
  let nw = spawn_worker ~core:w.core in
  w.fd <- nw.fd; w.pid <- nw.pid; w.state <- Hot; w.inflight <- false;
  w.alloc_mb <- 0.0; w.major <- 0; p.rotations <- p.rotations + 1

(* ---------- Unique request IDs (no RNG collisions) ---------- *)

let req_ctr = ref 0L
let next_req_id () =
  let id = !req_ctr in
  req_ctr := Int64.succ id; id

(* ---------- Drain a single completed worker when pool is full ---------- *)

let int_of_fd (fd:Unix.file_descr) : int = (Obj.magic fd : int)

let drain_one_ready ~deadline_ns p : unit =
  (* Only two workers are supported; watch just the inflight ones. *)
  let w0 =
    if p.workers.(0).inflight then Some p.workers.(0) else None
  and w1 =
    if p.workers.(1).inflight then Some p.workers.(1) else None
  in
  let fd1 = match w0 with Some w -> int_of_fd w.fd | None -> -1
  and fd2 = match w1 with Some w -> int_of_fd w.fd | None -> -1 in

  if fd1 < 0 && fd2 < 0 then
    (* Nothing inflight: nothing to drain. *)
    ()
  else begin
    let tf, ready = Hedge_timer.wait_two p.timer 
        ~fd1:(Obj.magic fd1 : Unix.file_descr) 
        ~fd2:(Obj.magic fd2 : Unix.file_descr) in
    ignore tf;
    let use_fd =
      if ready = fd1 then fd1 else if ready = fd2 then fd2 else -1 in
    if use_fd >= 0 then
      let w = if use_fd = fd1 then w0 else w1 in
      match w with
      | None -> ()
      | Some w ->
          begin match Ipc.read_any w.fd with
          | Any_resp (_rid, st, nt, iss, mb10, maj) ->
              update_on_resp p w ~alloc_mb10:mb10 ~major:maj; 
              maybe_rotate p w;
              ignore st; ignore nt; ignore iss
          | Any_hup ->
              w.inflight <- false; force_rotate p w
          | _ -> ()
          end
    else
      (* Timer fired while draining; ignore here. *)
      ()
  end;
  if Int64.sub (Clock.now ()) deadline_ns > 0L then
    failwith "Backpressure timeout: workers stuck inflight"
  else
    ()

let inflight_total p =
  Array.fold_left (fun acc w -> acc + (if w.inflight then 1 else 0)) 0 p.workers

(* ---------- Hedged request ---------- *)

type svc_result = { status:int; n_tokens:int; issues_len:int; origin:[`P|`H] }

let rec hedged_call p ~(input:bytes) ~(hedge_ms:int) : svc_result =
  (* Ensure there is at least one free slot; if not, **drain** one completion. *)
  let deadline = Int64.add (Clock.now ()) (Clock.ns_of_ms 30_000) in
  while inflight_total p >= Array.length p.workers do
    drain_one_ready ~deadline_ns:deadline p
  done;

  let req_id = next_req_id () in
  let prim = pick_hot p in
  prim.inflight <- true;
  Ipc.write_req prim.fd ~req_id ~bytes:input;

  (* Arm timer **before** waiting. *)
  Hedge_timer.arm p.timer ~ns:(Clock.ns_of_ms hedge_ms);
  p.requests <- p.requests + 1;

  (* Wait for primary or timer *)
  let rec wait_primary_or_timer () =
    let timer_fired, ready_fd =
      Hedge_timer.wait_two p.timer
        ~fd1:prim.fd ~fd2:(Obj.magic (-1) : Unix.file_descr)
    in
    if ready_fd = int_of_fd prim.fd then `Primary_ready
    else if timer_fired = 1 then `Hedge_fire
    else wait_primary_or_timer ()
  in

  match wait_primary_or_timer () with
  | `Primary_ready ->
      begin match Ipc.read_any prim.fd with
      | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
          update_on_resp p prim ~alloc_mb10:mb10 ~major:maj; 
          maybe_rotate p prim;
          { status=st; n_tokens=nt; issues_len=iss; origin=`P }
      | Any_hup ->
          prim.inflight <- false; 
          force_rotate p prim;
          let sec = pick_secondary p prim in
          sec.inflight <- true; 
          Ipc.write_req sec.fd ~req_id ~bytes:input;
          (match Ipc.read_any sec.fd with
           | Any_resp (_rid, st, nt, iss, mb10, maj) ->
               update_on_resp p sec ~alloc_mb10:mb10 ~major:maj; 
               maybe_rotate p sec;
               { status=st; n_tokens=nt; issues_len=iss; origin=`H }
           | _ -> failwith "broker: primary died; secondary failed")
      | _ -> hedged_call p ~input ~hedge_ms
      end

  | `Hedge_fire ->
      p.hedge_fired <- p.hedge_fired + 1;
      let sec = pick_secondary p prim in
      sec.inflight <- true;
      Ipc.write_req sec.fd ~req_id ~bytes:input;

      (* Race both workers to first completion. *)
      let rec race () =
        let _tf, ready = Hedge_timer.wait_two p.timer ~fd1:prim.fd ~fd2:sec.fd in
        if ready = (Obj.magic prim.fd : int) then
          match Ipc.read_any prim.fd with
          | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
              update_on_resp p prim ~alloc_mb10:mb10 ~major:maj; 
              maybe_rotate p prim;
              Ipc.write_cancel sec.fd ~req_id; 
              sec.inflight <- false;
              { status=st; n_tokens=nt; issues_len=iss; origin=`P }
          | Any_hup -> 
              prim.inflight <- false; 
              force_rotate p prim; 
              race ()
          | _ -> race ()
        else if ready = (Obj.magic sec.fd : int) then
          match Ipc.read_any sec.fd with
          | Any_resp (rid, st, nt, iss, mb10, maj) when rid=req_id ->
              update_on_resp p sec ~alloc_mb10:mb10 ~major:maj; 
              maybe_rotate p sec;
              Ipc.write_cancel prim.fd ~req_id; 
              prim.inflight <- false;
              p.hedge_wins <- p.hedge_wins + 1;
              { status=st; n_tokens=nt; issues_len=iss; origin=`H }
          | Any_hup -> 
              sec.inflight <- false; 
              force_rotate p sec; 
              race ()
          | _ -> race ()
        else race ()
      in
      race ()