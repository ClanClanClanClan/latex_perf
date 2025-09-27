open Ipc

(* Fault injection (env): L0_FAULT_MS: integer milliseconds to sleep when
   triggered (default 0) L0_FAULT_RATE_PPM: events per million (default 0)
   L0_FAULT_PHASE: "pre" | "post" (default "pre") *)
let fault_ms =
  match Sys.getenv_opt "L0_FAULT_MS" with
  | Some s -> max 0 (int_of_string s)
  | None -> 0

let fault_rate_ppm =
  match Sys.getenv_opt "L0_FAULT_RATE_PPM" with
  | Some s -> max 0 (int_of_string s)
  | None -> 0

let fault_phase =
  match Sys.getenv_opt "L0_FAULT_PHASE" with Some "post" -> `Post | _ -> `Pre

let rng = ref 0x9e3779b9

let rand_ppm () =
  let x = !rng in
  let x = x lxor (x lsl 13) in
  let x = x lxor (x lsr 17) in
  let x = x lxor (x lsl 5) in
  rng := x;
  x land 0x0F_FFFF mod 1_000_000

let maybe_fault () =
  if fault_ms > 0 && fault_rate_ppm > 0 && rand_ppm () < fault_rate_ppm then
    ignore (Unix.select [] [] [] (float fault_ms /. 1000.0))

type stats = { mutable major_cycles : int }

let stats = { major_cycles = 0 }

type state = {
  fd : Unix.file_descr;
  arenas : Arena.t;
  mutable ibuf : bytes; (* reusable input buffer *)
  mutable ibuf_cap : int;
  mutable cur_req : int64 option;
  mutable cancelled : bool;
  mutable reqs : int;
  mutable words_at_spawn : float;
  mutable majors_at_spawn : int;
}

let live_words () = (Gc.quick_stat ()).live_words

let words_total () =
  let s = Gc.quick_stat () in
  s.minor_words +. s.major_words

let major_collections () = (Gc.stat ()).major_collections

let reset_spawn_counters st =
  st.words_at_spawn <- words_total ();
  st.majors_at_spawn <- major_collections ()

let alloc_mb_since_spawn st =
  let words = words_total () -. st.words_at_spawn in
  words *. (float Sys.word_size /. 8.0) /. 1.048_576

let majors_since_spawn st = major_collections () - st.majors_at_spawn

let should_retire st =
  alloc_mb_since_spawn st >= float Config.worker_alloc_budget_mb
  || majors_since_spawn st >= Config.worker_major_cycles_budget

let ensure_ibuf st need =
  if need <= st.ibuf_cap then ()
  else
    let cap = max need (max 1 st.ibuf_cap * 2) in
    st.ibuf <- Bytes.create cap;
    st.ibuf_cap <- cap

let _alarm =
  Gc.create_alarm (fun () -> stats.major_cycles <- stats.major_cycles + 1)

(* CRITICAL FIX: Optimized monitoring for P99.9 performance *)
let update_and_log st =
  st.reqs <- st.reqs + 1;
  (* CRITICAL FIX: Ultra-reduced logging frequency to minimize P99.9 overhead *)
  if st.reqs mod 5000 = 0 then
    (* Reduced frequency to every 5k requests *)
    let rss = Meminfo.rss_mb () in
    let live_mb =
      float (live_words ()) *. float Sys.word_size /. 8.0 /. 1.0e6
    in
    let alloc_mb = alloc_mb_since_spawn st in
    let majors = majors_since_spawn st in
    Printf.eprintf
      "[worker] req=%d rss=%.1fMB live=%.1fMB alloc_since=%.0fMB majors_since=%d\n\
       %!"
      st.reqs rss live_mb alloc_mb majors
(* CRITICAL FIX: Remove all forced GC to prevent latency spikes *)
(* Let OCaml's automatic GC + prepay handle all collections for optimal P99.9 *)

let handle_req st ~req_id (input : bytes) =
  st.cur_req <- Some req_id;
  st.cancelled <- false;
  Gc_prep.prepay ();
  Arena.swap st.arenas;
  let cur = Arena.current st.arenas in
  (* CRITICAL FIX: Ultra-minimal pre-touching for P99.9 latency *)
  let input_len = Bytes.length input in
  (* Skip input pre-touching entirely to avoid page fault bursts *)
  let est_tokens = int_of_float (1.10 *. float input_len) in
  (* Minimal estimate *)
  (* CRITICAL FIX: Ultra-minimal pre-touching - only touch first few pages *)
  let touch_elems = min est_tokens 20000 in
  (* Reduced cap to minimize page faults *)
  (* Only touch the most critical arrays with minimal size *)
  if touch_elems > 1000 then (
    (* Only for reasonably sized inputs *)
    Pretouch.pre_touch_ba_1 cur.Arena.kinds ~elem_bytes:4
      ~elems:(min touch_elems 15000) ~page:Config.page_bytes;
    Pretouch.pre_touch_ba_1 cur.Arena.codes ~elem_bytes:4
      ~elems:(min touch_elems 15000) ~page:Config.page_bytes);
  (* Skip issues array pre-touching to avoid overhead *)
  (* Optional fault injection: pre-tokenize *)
  (match fault_phase with `Pre -> maybe_fault () | `Post -> ());

  (* SIMD Processing (real work) *)
  let status, n_tokens, issues_len = Real_processor.run input cur in

  (* Optional fault injection: post-tokenize *)
  (match fault_phase with `Post -> maybe_fault () | `Pre -> ());
  let s = Gc.quick_stat () in
  let words = s.minor_words +. s.major_words in
  let bytes = words *. (float Sys.word_size /. 8.0) in
  let alloc_mb10 = int_of_float (10.0 *. (bytes /. 1.048_576)) in
  let majors = majors_since_spawn st in
  (match st.cur_req with
  | Some id when not st.cancelled ->
      Ipc.write_resp st.fd ~req_id:id ~status ~n_tokens ~issues_len ~alloc_mb10
        ~major_cycles:majors
  | _ -> ());
  st.cur_req <- None;
  st.cancelled <- false;
  update_and_log st;
  if should_retire st then exit 0 else ()

let start_loop fd ~core:_ =
  Mlock.init ();
  Gc_prep.init_gc ();
  let st =
    {
      fd;
      arenas = Arena.create ~cap:Config.arenas_tokens_cap;
      ibuf = Bytes.create 0;
      ibuf_cap = 0;
      cur_req = None;
      cancelled = false;
      reqs = 0;
      words_at_spawn = 0.0;
      majors_at_spawn = 0;
    }
  in
  reset_spawn_counters st;
  let rec loop () =
    match Ipc.read_any st.fd with
    | Any_req (id, payload) ->
        ensure_ibuf st (Bytes.length payload);
        Bytes.blit payload 0 st.ibuf 0 (Bytes.length payload);
        let view = Bytes.sub st.ibuf 0 (Bytes.length payload) in
        handle_req st ~req_id:id view;
        loop ()
    | Any_cancel id ->
        (match st.cur_req with
        | Some cur when cur = id -> st.cancelled <- true
        | _ -> ());
        loop ()
    | Any_resp _ -> loop ()
    | Any_hup -> exit 0
  in
  loop ()
