external now_ns : unit -> int64 = "ocaml_clock_monotonic_ns"
let now () = now_ns ()
let ns_of_ms ms = Int64.mul 1_000_000L (Int64.of_int ms)
let ms_of_ns ns = Int64.to_float ns /. 1.0e6

type stamps = {
  mutable t_in_start   : int64;
  mutable t_in_done    : int64;
  mutable t_proc_start : int64;
  mutable t_proc_done  : int64;
  mutable t_reply_ready: int64;
}
let make_stamps () = { t_in_start=0L; t_in_done=0L; t_proc_start=0L; t_proc_done=0L; t_reply_ready=0L }
