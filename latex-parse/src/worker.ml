open Ipc

type stats = { mutable major_cycles : int }
let stats = { major_cycles = 0 }

type state = {
  fd        : Unix.file_descr;
  arenas    : Arena.t;
  mutable ibuf     : bytes;  (* reusable input buffer *)
  mutable ibuf_cap : int;
  mutable cur_req  : int64 option;
  mutable cancelled: bool;
  mutable reqs     : int;
  mutable words_at_spawn  : float;
  mutable majors_at_spawn : int;
}

let live_words ()  = (Gc.quick_stat ()).live_words
let words_total () = let s = Gc.quick_stat () in s.minor_words +. s.major_words
let major_collections () = (Gc.stat ()).major_collections

let reset_spawn_counters st =
  st.words_at_spawn  <- words_total ();
  st.majors_at_spawn <- major_collections ()

let alloc_mb_since_spawn st =
  let words = (words_total ()) -. st.words_at_spawn in
  words *. (float Sys.word_size /. 8.0) /. 1.048_576

let majors_since_spawn st =
  (major_collections ()) - st.majors_at_spawn

let should_retire st =
  alloc_mb_since_spawn st >= float Config.worker_alloc_budget_mb
  || majors_since_spawn st >= Config.worker_major_cycles_budget

let ensure_ibuf st need =
  if need <= st.ibuf_cap then () else
    let cap = max need (max 1 st.ibuf_cap * 2) in
    st.ibuf <- Bytes.create cap; st.ibuf_cap <- cap

let _alarm = Gc.create_alarm (fun () -> stats.major_cycles <- stats.major_cycles + 1)

let update_and_log st =
  st.reqs <- st.reqs + 1;
  if st.reqs mod 1000 = 0 then begin
    let rss = Meminfo.rss_mb () in
    let live_mb = (float (live_words ()) *. float Sys.word_size /. 8.0) /. 1.0e6 in
    let alloc_mb = alloc_mb_since_spawn st in
    let majors   = majors_since_spawn st in
    Printf.eprintf "[worker] req=%d rss=%.1fMB live=%.1fMB alloc_since=%.0fMB majors_since=%d\n%!"
      st.reqs rss live_mb alloc_mb majors
  end

let handle_req st ~req_id (input:bytes) =
  st.cur_req <- Some req_id; st.cancelled <- false;
  Gc_prep.prepay ();
  Arena.swap st.arenas;
  let cur = Arena.current st.arenas in
  Pretouch.pre_touch_bytes input ~page:Config.page_bytes;
  let est_tokens = int_of_float (1.30 *. float (Bytes.length input)) in
  Pretouch.pre_touch_ba_1 cur.Arena.kinds  ~elem_bytes:4 ~elems:est_tokens ~page:Config.page_bytes;
  Pretouch.pre_touch_ba_1 cur.Arena.codes  ~elem_bytes:4 ~elems:est_tokens ~page:Config.page_bytes;
  Pretouch.pre_touch_ba_1 cur.Arena.offs   ~elem_bytes:4 ~elems:est_tokens ~page:Config.page_bytes;
  Pretouch.pre_touch_ba_1 cur.Arena.issues ~elem_bytes:4 ~elems:1024        ~page:Config.page_bytes;
  (match Sys.getenv_opt "L0_FAULT_MS" with
   | Some s -> let d = try int_of_string s with _ -> 0 in if d>0 && (Random.bits () land 1023 = 0)
               then Unix.sleepf (float d /. 1000.)
   | None -> ());
  let (status, n_tokens, issues_len) = Real_processor.run input cur in
  let s = Gc.quick_stat () in
  let words = s.minor_words +. s.major_words in
  let bytes = words *. (float Sys.word_size /. 8.0) in
  let alloc_mb10 = int_of_float (10.0 *. (bytes /. 1.048_576)) in
  let majors = majors_since_spawn st in
  (match st.cur_req with
   | Some id when not st.cancelled ->
       Ipc.write_resp st.fd ~req_id:id ~status ~n_tokens ~issues_len ~alloc_mb10 ~major_cycles:majors
   | _ -> ());
  st.cur_req <- None; st.cancelled <- false;
  update_and_log st;
  if should_retire st then exit 0 else ()

let start_loop fd ~core:_ =
  Mlock.init (); Gc_prep.init_gc ();
  let st = {
    fd; arenas = Arena.create ~cap:Config.arenas_tokens_cap;
    ibuf=Bytes.create 0; ibuf_cap=0; cur_req=None; cancelled=false; reqs=0;
    words_at_spawn=0.0; majors_at_spawn=0;
  } in
  reset_spawn_counters st;
  let rec loop () =
    match Ipc.read_any st.fd with
    | Any_req (id, payload) ->
        ensure_ibuf st (Bytes.length payload);
        Bytes.blit payload 0 st.ibuf 0 (Bytes.length payload);
        let view = Bytes.sub st.ibuf 0 (Bytes.length payload) in
        handle_req st ~req_id:id view; loop ()
    | Any_cancel id ->
        (match st.cur_req with Some cur when cur = id -> st.cancelled <- true | _ -> ());
        loop ()
    | Any_resp _ -> loop ()
    | Any_hup -> exit 0
  in loop ()