type t = {
  mutex : Mutex.t;
  cond : Condition.t;
  ready : bool ref;
}

let create () = {
  mutex = Mutex.create ();
  cond = Condition.create ();
  ready = ref false;
}

let release t =
  Mutex.lock t.mutex;
  t.ready := true;
  Condition.broadcast t.cond;
  Mutex.unlock t.mutex

let wait t =
  Mutex.lock t.mutex;
  while not !(t.ready) do
    Condition.wait t.cond t.mutex
  done;
  Mutex.unlock t.mutex