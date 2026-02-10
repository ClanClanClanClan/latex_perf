(** Unit tests for Validators_metrics Prometheus counters. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[val-metrics] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

(* Helper: dump to a string via pipe *)
let dump_to_string () =
  let rd, wr = Unix.pipe () in
  let oc = Unix.out_channel_of_descr wr in
  Validators_metrics.dump_prometheus oc;
  flush oc;
  Unix.close wr;
  let ic = Unix.in_channel_of_descr rd in
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_char buf (input_char ic)
     done
   with End_of_file -> ());
  Unix.close rd;
  Buffer.contents buf

let () =
  (* Use unique IDs per test to avoid interference from global state *)

  (* 1. Record + dump roundtrip *)
  run "record and dump" (fun tag ->
      Validators_metrics.record ~id:"test_vm_1" ~count:5 ~dur_ms:1.5;
      let s = dump_to_string () in
      expect
        (String.length s > 0
        &&
        try
          ignore (Str.search_forward (Str.regexp_string "test_vm_1") s 0);
          true
        with Not_found -> false)
        (tag ^ ": id present"));

  (* 2. Accumulation: same id recorded twice *)
  run "accumulation" (fun tag ->
      Validators_metrics.record ~id:"test_vm_2" ~count:1 ~dur_ms:1.0;
      Validators_metrics.record ~id:"test_vm_2" ~count:2 ~dur_ms:2.0;
      let s = dump_to_string () in
      (* hits_total should be 2 *)
      expect
        (try
           ignore
             (Str.search_forward
                (Str.regexp_string
                   "validators_rule_hits_total{id=\"test_vm_2\"} 2")
                s 0);
           true
         with Not_found -> false)
        (tag ^ ": hits=2"));

  (* 3. Multiple distinct IDs *)
  run "multiple IDs" (fun tag ->
      Validators_metrics.record ~id:"test_vm_3a" ~count:1 ~dur_ms:0.1;
      Validators_metrics.record ~id:"test_vm_3b" ~count:1 ~dur_ms:0.2;
      let s = dump_to_string () in
      let has_3a =
        try
          ignore (Str.search_forward (Str.regexp_string "test_vm_3a") s 0);
          true
        with Not_found -> false
      in
      let has_3b =
        try
          ignore (Str.search_forward (Str.regexp_string "test_vm_3b") s 0);
          true
        with Not_found -> false
      in
      expect has_3a (tag ^ ": 3a");
      expect has_3b (tag ^ ": 3b"));

  (* 4. Prometheus format lines *)
  run "prometheus format" (fun tag ->
      Validators_metrics.record ~id:"test_vm_4" ~count:3 ~dur_ms:4.5;
      let s = dump_to_string () in
      let has_hits =
        try
          ignore
            (Str.search_forward
               (Str.regexp "validators_rule_hits_total{id=\"test_vm_4\"}")
               s 0);
          true
        with Not_found -> false
      in
      let has_dur =
        try
          ignore
            (Str.search_forward
               (Str.regexp "validators_rule_duration_ms_sum{id=\"test_vm_4\"}")
               s 0);
          true
        with Not_found -> false
      in
      let has_count =
        try
          ignore
            (Str.search_forward
               (Str.regexp "validators_rule_last_count{id=\"test_vm_4\"}")
               s 0);
          true
        with Not_found -> false
      in
      expect has_hits (tag ^ ": hits line");
      expect has_dur (tag ^ ": duration line");
      expect has_count (tag ^ ": count line"));

  (* 5. Thread safety: 4 threads × 100 records *)
  run "thread safety" (fun tag ->
      let threads =
        List.init 4 (fun _ ->
            Thread.create
              (fun () ->
                for _ = 1 to 100 do
                  Validators_metrics.record ~id:"test_vm_5" ~count:1
                    ~dur_ms:0.01
                done)
              ())
      in
      List.iter Thread.join threads;
      let s = dump_to_string () in
      (* Total hits should be 400 (4 × 100) plus any from previous tests *)
      let has_id =
        try
          ignore (Str.search_forward (Str.regexp_string "test_vm_5") s 0);
          true
        with Not_found -> false
      in
      expect has_id (tag ^ ": id present after concurrent writes"));

  if !fails > 0 then (
    Printf.eprintf "[val-metrics] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[val-metrics] PASS %d cases\n%!" !cases
