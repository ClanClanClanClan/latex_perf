external task_meminfo : unit -> (int64 * int64) = "ocaml_task_meminfo"
let rss_mb () = let (rss, _) = task_meminfo () in Int64.to_float rss /. 1.0e6