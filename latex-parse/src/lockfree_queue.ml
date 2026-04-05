(* ══════════════════════════════════════════════════════════════════════
   Lockfree_queue — MPMC ring buffer using OCaml 5.x Atomic (spec W63)

   Multi-producer, multi-consumer bounded queue using compare-and-swap.
   Target: 8M events/sec on 4 cores.

   Design: power-of-two ring buffer with atomic head/tail indices.
   Each slot has a sequence number for ABA protection.
   ══════════════════════════════════════════════════════════════════════ *)

type 'a slot = { mutable data : 'a option; seq : int Atomic.t }

type 'a t = {
  buffer : 'a slot array;
  mask : int;
  head : int Atomic.t; (* consumer reads from head *)
  tail : int Atomic.t; (* producer writes to tail *)
}

let create (capacity : int) : 'a t =
  (* Round up to power of two *)
  let cap = ref 1 in
  while !cap < capacity do
    cap := !cap * 2
  done;
  let n = !cap in
  let buffer =
    Array.init n (fun i -> { data = None; seq = Atomic.make i })
  in
  { buffer; mask = n - 1; head = Atomic.make 0; tail = Atomic.make 0 }

let capacity (q : 'a t) : int = q.mask + 1

(** Try to enqueue [v]. Returns [true] on success, [false] if full. *)
let try_push (q : 'a t) (v : 'a) : bool =
  let rec loop () =
    let tail = Atomic.get q.tail in
    let idx = tail land q.mask in
    let slot = q.buffer.(idx) in
    let seq = Atomic.get slot.seq in
    let diff = seq - tail in
    if diff = 0 then (
      (* Slot is available for writing *)
      if Atomic.compare_and_set q.tail tail (tail + 1) then (
        slot.data <- Some v;
        Atomic.set slot.seq (tail + 1);
        true)
      else loop ())
    else if diff < 0 then false (* Queue full *)
    else loop ()
    (* Another producer claimed this slot, retry *)
  in
  loop ()

(** Try to dequeue. Returns [Some v] on success, [None] if empty. *)
let try_pop (q : 'a t) : 'a option =
  let rec loop () =
    let head = Atomic.get q.head in
    let idx = head land q.mask in
    let slot = q.buffer.(idx) in
    let seq = Atomic.get slot.seq in
    let diff = seq - (head + 1) in
    if diff = 0 then (
      (* Slot has data ready *)
      if Atomic.compare_and_set q.head head (head + 1) then (
        let v = slot.data in
        slot.data <- None;
        Atomic.set slot.seq (head + (q.mask + 1));
        v)
      else loop ())
    else if diff < 0 then None (* Queue empty *)
    else loop ()
    (* Another consumer claimed this slot, retry *)
  in
  loop ()

(** Blocking push: spins until slot available. *)
let push (q : 'a t) (v : 'a) : unit =
  while not (try_push q v) do
    Domain.cpu_relax ()
  done

(** Blocking pop: spins until data available. *)
let pop (q : 'a t) : 'a =
  let rec loop () =
    match try_pop q with
    | Some v -> v
    | None ->
        Domain.cpu_relax ();
        loop ()
  in
  loop ()

(** Current number of items (approximate, may race). *)
let length (q : 'a t) : int =
  let t = Atomic.get q.tail in
  let h = Atomic.get q.head in
  max 0 (t - h)

(** Is the queue empty? (approximate) *)
let is_empty (q : 'a t) : bool = length q = 0
