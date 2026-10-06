(* PROFILING ONLY (spike H.5 heap design, stage 1): coq-core 8.18.0 kernel/parray.ml's
   persistent array, the same algorithm, with counters, and a second mode.
   PS_PARRAY=persistent (default): coq-core's algorithm, counting sets, gets, reroot steps
     (Updated nodes traversed) and accesses through a superseded version.
   PS_PARRAY=linear: a set mutates the array in place; the superseded version becomes
     Invalid, and any later access to it aborts the run (exit 4). The candidate-A behaviour,
     measured; never a model build. *)
type 'a t = 'a kind ref
and 'a kind =
  | Array of Obj.t array * 'a
  | Updated of int * 'a * 'a t
  | Invalid

let linear = (Sys.getenv_opt "PS_PARRAY" = Some "linear")
let n_set = ref 0 and n_get = ref 0 and n_make = ref 0 and n_make_words = ref 0
and n_reroot_steps = ref 0 and n_stale = ref 0 and n_copy = ref 0

let max_array_length32 = 4194303
let trunc_size n =
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int max_array_length32) then
    snd (Uint63.to_int2 n) else max_array_length32

let invalid () = prerr_endline "PARRAYC: access through a superseded version (linear mode)"; exit 4

let rec rerootk t k =
  match !t with
  | Array (a, _) -> k a
  | Invalid -> invalid ()
  | Updated (i, v, p) ->
      incr n_reroot_steps;
      let k' a =
        let v' = Array.unsafe_get a i in
        Array.unsafe_set a i (Obj.repr v);
        t := !p;
        p := Updated (i, Obj.obj v', t);
        k a in
      rerootk p k'

let reroot t =
  (match !t with Updated _ -> incr n_stale | _ -> ());
  rerootk t (fun a -> a)

let get p n =
  incr n_get;
  let t = reroot p in
  let l = Array.length t in
  if Uint63.le Uint63.zero n && Uint63.lt n (Uint63.of_int l) then
    Obj.obj (Array.unsafe_get t (snd (Uint63.to_int2 n)))
  else match !p with Array (_, def) -> def | _ -> assert false

let set p n e =
  incr n_set;
  let a = reroot p in
  let l = Uint63.of_int (Array.length a) in
  if Uint63.le Uint63.zero n && Uint63.lt n l then begin
    let i = snd (Uint63.to_int2 n) in
    let v' = Array.unsafe_get a i in
    Array.unsafe_set a i (Obj.repr e);
    let t = ref !p in
    (if linear then p := Invalid else p := Updated (i, Obj.obj v', t));
    t
  end else p

let make n def =
  incr n_make;
  let n = trunc_size n in
  n_make_words := !n_make_words + n;
  let a = Array.make n (Obj.repr ()) in
  Array.fill a 0 n (Obj.repr def);
  ref (Array (a, def))

let length p = Uint63.of_int (Array.length (reroot p))
let default p = ignore (reroot p); match !p with Array (_, d) -> d | _ -> assert false
let copy p = incr n_copy; let a = reroot p in
  match !p with Array (_, d) -> ref (Array (Array.copy a, d)) | _ -> assert false

let counters () =
  Printf.sprintf "set %d get %d make %d make_words %d reroot_steps %d stale %d copy %d"
    !n_set !n_get !n_make !n_make_words !n_reroot_steps !n_stale !n_copy
