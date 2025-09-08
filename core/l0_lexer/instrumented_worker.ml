(* Instrumented worker with proper per-stage timing *)
open Ipc

type arenas = Arena.t
type t = { fd: Unix.file_descr; arenas: arenas; mutable slowest_traces: (float * float * float * float * int * string) list }

type stats = {
  mutable alloc_words_since_spawn : float;
  mutable major_cycles_since_spawn: int;
}
let stats = { alloc_words_since_spawn = 0.0; major_cycles_since_spawn = 0 }
let _alarm = Gc.create_alarm (fun () -> stats.major_cycles_since_spawn <- stats.major_cycles_since_spawn + 1)

let update_alloc () =
  let s = Gc.quick_stat () in
  stats.alloc_words_since_spawn <- s.minor_words +. s.major_words

let should_retire () =
  let bytes = stats.alloc_words_since_spawn *. (float Sys.word_size /. 8.0) in
  let mb    = bytes /. 1_048_576.0 in
  mb >= float Config.worker_alloc_budget_mb ||
  stats.major_cycles_since_spawn >= Config.worker_major_cycles_budget

let checksum_work arena n_tokens =
  let indices = [| 64; 128; 256; 512; 1024; 2048; 4096; 8192 |] in
  Array.fold_left (fun acc i -> 
    if i < n_tokens && i < Bigarray.Array1.dim arena.Arena.kinds then
      let kind = Int32.to_int (Bigarray.Array1.get arena.Arena.kinds i) in
      let code = Int32.to_int (Bigarray.Array1.get arena.Arena.codes i) in  
      acc lxor (kind lsl 16) lxor code
    else acc
  ) 0 indices

let respond fd ~req_id ~status ~n_tokens ~issues_len =
  let s = Gc.quick_stat () in
  let words = s.minor_words +. s.major_words in
  let bytes = words *. (float Sys.word_size /. 8.0) in
  let alloc_mb10 = int_of_float (10.0 *. (bytes /. 1_048_576.0)) in
  let major = stats.major_cycles_since_spawn in
  Ipc.write_resp fd ~req_id ~status ~n_tokens ~issues_len ~alloc_mb10 ~major

let handle (w:t) ~req_id (input:bytes) =
  let t0 = Clock.now_ns () in
  
  Gc_prep.prepay_gc_debt ();
  let t1 = Clock.now_ns () in
  
  Arena.swap w.arenas;
  let cur = Arena.current w.arenas in
  Pretouch.pre_touch_ba_1 cur.Arena.kinds ~elem_bytes:4 ~page:Config.page_bytes;
  Pretouch.pre_touch_ba_1 cur.Arena.codes ~elem_bytes:4 ~page:Config.page_bytes;
  Pretouch.pre_touch_ba_1 cur.Arena.offs  ~elem_bytes:4 ~page:Config.page_bytes;
  Pretouch.pre_touch_ba_1 cur.Arena.issues~elem_bytes:4 ~page:Config.page_bytes;
  Pretouch.pre_touch_bytes input ~page:Config.page_bytes;
  let t2 = Clock.now_ns () in

  let status, n_tokens, issues_len =
    Alloc_guard.with_no_alloc (fun () ->
      Real_processor.run input cur
    )
  in
  let t3 = Clock.now_ns () in
  
  let total_ms = Int64.to_float (Int64.sub t3 t0) /. 1_000_000.0 in
  let prep_ms = Int64.to_float (Int64.sub t1 t0) /. 1_000_000.0 in
  let pretouch_ms = Int64.to_float (Int64.sub t2 t1) /. 1_000_000.0 in  
  let process_ms = Int64.to_float (Int64.sub t3 t2) /. 1_000_000.0 in
  
  let checksum = checksum_work cur n_tokens in
  
  (* Track slowest 10 requests for debugging *)
  let trace = (total_ms, prep_ms, pretouch_ms, process_ms, checksum, Printf.sprintf "tok=%d" n_tokens) in
  let rec take n = function
    | [] -> []
    | h :: t when n > 0 -> h :: take (n-1) t
    | _ -> []
  in
  w.slowest_traces <- 
    (trace :: w.slowest_traces)
    |> List.sort (fun (t1,_,_,_,_,_) (t2,_,_,_,_,_) -> compare t2 t1)  (* descending *)
    |> (function l when List.length l > 10 -> take 10 l | l -> l);
  
  (* Log if in slowest 10 so far *)
  if List.length w.slowest_traces <= 10 || total_ms > (let (t,_,_,_,_,_) = List.nth w.slowest_traces 9 in t) then
    Printf.eprintf "SLOW[%d]: %.3fms (prep:%.3f pretouch:%.3f process:%.3f) checksum:%08x %s\n%!" 
      (List.length w.slowest_traces) total_ms prep_ms pretouch_ms process_ms checksum (snd (List.hd (List.rev (String.split_on_char '=' (Printf.sprintf "tok=%d" n_tokens)))));
  
  update_alloc ();
  respond w.fd ~req_id ~status ~n_tokens ~issues_len

let rec loop (w:t) =
  match Ipc.read_any w.fd with
  | `Req (req_id, payload) ->
      handle w ~req_id payload; if should_retire () then exit 0; loop w
  | `Cancel _ -> loop w
  | `Resp _ -> loop w
  | `Hup -> exit 0

let start fd ~core =
  Qos.init_for_worker ~core;
  Mlock.init ();
  Gc_prep.init_gc ();
  let arenas = Arena.create ~cap:Config.arenas_tokens_cap in
  loop { fd; arenas; slowest_traces = [] }