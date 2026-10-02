(* Hedged-RPC broker over a pool of forked worker processes.

   INVARIANTS (each was violated before OPEN-127; see PROJECT_STATE
   C-122..C-124):

   (I1) A worker process owns exactly stdin, stdout, stderr and its own end of
   its socketpair. Workers are forked and never exec, so close-on-exec closes
   nothing: before the fix every worker inherited the parent's end of every
   EARLIER worker's socketpair (plus the listening socket and any accepted
   client connection). Retiring a worker closes the parent's end and waits for
   the worker to read EOF and exit; a sibling holding a copy of that end meant
   the EOF never came, and the request that triggered the retirement hung in
   waitpid until the sibling itself was retired by a later request.
   [close_inherited_fds] runs first thing in every child.

   (I2) Every request written to a worker produces exactly one response or the
   worker's death (EOF), because a worker is single-threaded and reads a Cancel
   only between requests, so it can never cancel a request in flight.
   [w.outstanding] counts requests written and not yet answered; a worker is
   reused only when [outstanding = 0], after the responses it still owes (the
   loser of a hedge race) have been read and discarded. Before the fix an
   [inflight] flag was cleared on a Cancel or on a 200 ms "timeout recovery"
   without reading the response, so a later request read an earlier request's
   reply, failed the req_id match and fell into an error or a wait on a socket
   with nothing to read.

   (I3) One call at a time: main_service runs one thread per connection, and
   every thread drives the same pool, timer and sockets, so two concurrent calls
   interleaved their reads of one socket and decoded each other's frames
   (status=20 tokens=0 was observed). [hedged_call] holds [p.mu] for its whole
   duration. (The mutex was removed in Feb 2026 as "incompatible with blocking C
   sections"; that diagnosis was wrong: the hang it saw was (I1), which a mutex
   turns from intermittent into permanent because the request that would retire
   the fd-holding sibling can no longer run.)

   (I4) A worker that died (EOF, a write that fails, or a frame that is not a
   response) is reaped and replaced at once, so a dead worker is never chosen
   again. Before the fix a dead Hot worker was never respawned. *)

open Ipc

type wstate = Hot | Cooling

type worker = {
  mutable fd : Unix.file_descr;
  mutable pid : int;
  core : int;
  mutable state : wstate;
  mutable outstanding : int;
  mutable alloc_mb : float;
  mutable major : int;
}

(* ---- (I1) fd hygiene in the child ---- *)

let fd_dirs = [ "/proc/self/fd"; "/dev/fd" ]

let list_open_fds () =
  let rec go = function
    | [] -> None
    | d :: ds -> (
        match Sys.readdir d with
        | names ->
            Some (List.filter_map int_of_string_opt (Array.to_list names))
        | exception Sys_error _ -> go ds)
  in
  go fd_dirs

let close_inherited_fds ~keep =
  match list_open_fds () with
  | None ->
      prerr_endline "[worker] cannot list open fds; refusing to run";
      exit 2
  | Some fds ->
      (* The listing includes the directory fd Sys.readdir used, which is
         already closed: EBADF is expected for it. *)
      List.iter
        (fun n ->
          if n > 2 && n <> keep then
            try Unix.close (Fd_util.int_to_fd n) with Unix.Unix_error _ -> ())
        fds

let spawn_worker ~core =
  let sv, sc = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.set_close_on_exec sv;
  Unix.set_close_on_exec sc;
  match Unix.fork () with
  | 0 ->
      Unix.close sv;
      close_inherited_fds ~keep:(Fd_util.fd_to_int sc);
      (Worker.start_loop sc ~core : unit);
      exit 0
  | pid ->
      Unix.close sc;
      Unix.clear_nonblock sv;
      {
        fd = sv;
        pid;
        core;
        state = Hot;
        outstanding = 0;
        alloc_mb = 0.0;
        major = 0;
      }

type pool = {
  workers : worker array;
  mutable rr : int;
  timer : Hedge_timer.t;
  mu : Mutex.t;
  mutable requests : int;
  mutable hedge_fired : int;
  mutable hedge_wins : int;
  mutable rotations : int;
}

let init_pool cores =
  if Array.length cores = 0 then invalid_arg "Broker.init_pool: no cores";
  (* The child refuses to run without an fd listing; fail here, loudly, rather
     than spawn workers that exit at once. *)
  if list_open_fds () = None then
    failwith "Broker.init_pool: neither /proc/self/fd nor /dev/fd is listable";
  {
    workers = Array.map (fun c -> spawn_worker ~core:c) cores;
    rr = 0;
    timer = Hedge_timer.create ();
    mu = Mutex.create ();
    requests = 0;
    hedge_fired = 0;
    hedge_wins = 0;
    rotations = 0;
  }

(* ---- (I4) replacing a worker ---- *)

(* Close the parent's end and reap the child. By (I1) the parent held the only
   copy of that end, so a live worker reads EOF in its request loop and exits;
   callers only replace a worker that is idle (outstanding = 0) or already dead,
   so the wait is bounded by the worker finishing nothing. *)
let replace p w =
  (try Unix.close w.fd with Unix.Unix_error _ -> ());
  let rec reap () =
    try ignore (Unix.waitpid [] w.pid) with
    | Unix.Unix_error (Unix.EINTR, _, _) -> reap ()
    | Unix.Unix_error _ -> ()
  in
  reap ();
  let nw = spawn_worker ~core:w.core in
  w.fd <- nw.fd;
  w.pid <- nw.pid;
  w.state <- Hot;
  w.outstanding <- 0;
  w.alloc_mb <- 0.0;
  w.major <- 0;
  p.rotations <- p.rotations + 1;
  Metrics_prometheus.on_rotation ()

let update_on_resp w ~alloc_mb10 ~major =
  w.alloc_mb <- float alloc_mb10 /. 10.0;
  w.major <- major;
  let threshold = float Config.worker_alloc_budget_mb *. 0.6 in
  if
    w.state = Hot
    && (w.alloc_mb >= threshold
       || w.major >= Config.worker_major_cycles_budget - 1
       || (w.alloc_mb >= 150.0 && w.major >= 1))
  then w.state <- Cooling

(* ---- (I2) every request answered exactly once ---- *)

(* Write a request; [false] if the worker is gone (it is then replaced). *)
let send p w ~req_id ~input =
  match Ipc.write_req w.fd ~req_id ~bytes:input with
  | () ->
      w.outstanding <- w.outstanding + 1;
      true
  | exception (Failure _ | Unix.Unix_error _) ->
      replace p w;
      false

type got = Reply of int64 * int * int * int | Died

(* Read the next frame from a worker that owes a response (blocking). *)
let recv p w =
  match Ipc.read_any w.fd with
  | Any_resp (rid, st, nt, iss, mb10, maj) ->
      w.outstanding <- w.outstanding - 1;
      update_on_resp w ~alloc_mb10:mb10 ~major:maj;
      Reply (rid, st, nt, iss)
  | Any_hup | Any_req _ | Any_cancel _ ->
      replace p w;
      Died
  | exception (Failure _ | Unix.Unix_error _) ->
      replace p w;
      Died

let rec readable fd =
  match Unix.select [ fd ] [] [] 0.0 with
  | r, _, _ -> r <> []
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> readable fd

(* Read and discard the responses [w] still owes that have already arrived. *)
let rec drain_ready p w =
  if w.outstanding > 0 && readable w.fd then (
    ignore (recv p w);
    drain_ready p w)

(* Read and discard every response [w] still owes, waiting for them. *)
let rec settle p w =
  if w.outstanding > 0 then (
    ignore (recv p w);
    settle p w)

(* Bring every worker up to date: drain arrived responses, retire idle Cooling
   workers. *)
let tidy p =
  Array.iter
    (fun w ->
      drain_ready p w;
      if w.state = Cooling && w.outstanding = 0 then replace p w)
    p.workers

let is_except except w = match except with Some e -> e == w | None -> false

let pick_idle p ~except =
  let n = Array.length p.workers in
  let rec go k =
    if k >= n then None
    else
      let i = (p.rr + k) mod n in
      let w = p.workers.(i) in
      if (not (is_except except w)) && w.outstanding = 0 && w.state = Hot then (
        p.rr <- (i + 1) mod n;
        Some w)
      else go (k + 1)
  in
  go 0

(* A worker that owes nothing, other than [except]: an idle one if any, else the
   next one in round-robin order once it has delivered (and we have discarded)
   what it owes. [None] only when [except] is the sole worker. *)
let acquire p ~except =
  match pick_idle p ~except with
  | Some w -> Some w
  | None ->
      let n = Array.length p.workers in
      let rec go k =
        if k >= n then None
        else
          let i = (p.rr + k) mod n in
          let w = p.workers.(i) in
          if is_except except w then go (k + 1)
          else (
            p.rr <- (i + 1) mod n;
            settle p w;
            if w.state = Cooling then replace p w;
            Some w)
      in
      go 0

type svc_result = {
  status : int;
  n_tokens : int;
  issues_len : int;
  origin : [ `P | `H ];
  hedge_fired : bool;
}

let protocol_violation rid req_id =
  failwith
    (Printf.sprintf "broker: reply for req_id %Ld while awaiting %Ld" rid req_id)

let result ~origin ~hedge_fired (st, nt, iss) =
  { status = st; n_tokens = nt; issues_len = iss; origin; hedge_fired }

(* Wait for [w]'s reply to [req_id], no hedge. [None] if it died. *)
let await p w ~req_id =
  match recv p w with
  | Reply (rid, st, nt, iss) when rid = req_id -> Some (st, nt, iss)
  | Reply (rid, _, _, _) -> protocol_violation rid req_id
  | Died -> None

let fd_int = Fd_util.fd_to_int

(* After a worker died mid-request: one plain retry on another worker that owes
   nothing (or the replacement, in a one-worker pool). *)
let retry p ~dead ~req_id ~input =
  let w =
    match acquire p ~except:(Some dead) with
    | Some w -> w
    | None -> dead (* one-worker pool: [dead] is already its replacement *)
  in
  if not (send p w ~req_id ~input) then
    failwith "broker: request failed on two workers (write)"
  else
    match await p w ~req_id with
    | Some r -> result ~origin:`H ~hedge_fired:false r
    | None -> failwith "broker: request failed on two workers (EOF)"

let hedged_call_locked p ~(input : bytes) ~(hedge_ms : int) : svc_result =
  tidy p;
  let req_id = Int64.of_int p.requests in
  p.requests <- p.requests + 1;
  let primary =
    match acquire p ~except:None with
    | Some w -> w
    | None -> assert false (* init_pool refuses an empty pool *)
  in
  if not (send p primary ~req_id ~input) then
    retry p ~dead:primary ~req_id ~input
  else (
    Hedge_timer.arm p.timer ~ns:(Clock.ns_of_ms hedge_ms);
    let rec wait_primary () =
      let tf, ready =
        Hedge_timer.wait_two p.timer ~fd1:(fd_int primary.fd) ~fd2:(-1)
      in
      if ready = fd_int primary.fd then `Ready
      else if tf = 1 then `Hedge
      else wait_primary ()
    in
    let primary_reply () =
      match await p primary ~req_id with
      | Some r -> result ~origin:`P ~hedge_fired:false r
      | None -> retry p ~dead:primary ~req_id ~input
    in
    match wait_primary () with
    | `Ready -> primary_reply ()
    | `Hedge -> (
        (* Hedge only to a worker that owes nothing: one that is still busy
           would answer after the primary anyway. *)
        Array.iter (fun w -> if w != primary then drain_ready p w) p.workers;
        match pick_idle p ~except:(Some primary) with
        | None -> primary_reply ()
        | Some sec ->
            if not (send p sec ~req_id ~input) then primary_reply ()
            else (
              p.hedge_fired <- p.hedge_fired + 1;
              Metrics_prometheus.on_hedge_fired ();
              (* Both owe exactly one reply, to [req_id]. The first to answer
                 wins; the loser's reply is read and discarded before that
                 worker is used again (I2). *)
              let rec race () =
                let _tf, ready =
                  Hedge_timer.wait_two p.timer ~fd1:(fd_int primary.fd)
                    ~fd2:(fd_int sec.fd)
                in
                if ready = fd_int primary.fd then
                  match await p primary ~req_id with
                  | Some r -> result ~origin:`P ~hedge_fired:true r
                  | None -> (
                      match await p sec ~req_id with
                      | Some r ->
                          p.hedge_wins <- p.hedge_wins + 1;
                          Metrics_prometheus.on_hedge_win ();
                          result ~origin:`H ~hedge_fired:true r
                      | None -> failwith "broker: both hedged workers died")
                else if ready = fd_int sec.fd then
                  match await p sec ~req_id with
                  | Some r ->
                      p.hedge_wins <- p.hedge_wins + 1;
                      Metrics_prometheus.on_hedge_win ();
                      result ~origin:`H ~hedge_fired:true r
                  | None -> (
                      match await p primary ~req_id with
                      | Some r -> result ~origin:`P ~hedge_fired:true r
                      | None -> failwith "broker: both hedged workers died")
                else race ()
              in
              race ())))

let hedged_call p ~input ~hedge_ms =
  Mutex.protect p.mu (fun () -> hedged_call_locked p ~input ~hedge_ms)

(* Test/operator hook: retire worker [i] now (after it has answered what it
   owes) and replace it. Before (I1) this hung whenever another worker had been
   forked after worker [i]. *)
let retire p i =
  Mutex.protect p.mu (fun () ->
      let w = p.workers.(i) in
      settle p w;
      replace p w)

let worker_count p = Array.length p.workers
let requests (p : pool) = p.requests
let hedge_fired_count (p : pool) = p.hedge_fired
let hedge_wins_count (p : pool) = p.hedge_wins
let rotations_count (p : pool) = p.rotations
