open Unix
open Latex_parse_lib

let read_file path =
  let ic = open_in_bin path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  Bytes.unsafe_of_string s

let write_u32 oc n =
  output_byte oc (n land 0xff);
  output_byte oc ((n lsr 8) land 0xff);
  output_byte oc ((n lsr 16) land 0xff);
  output_byte oc ((n lsr 24) land 0xff)

let read_u32 ic =
  let b0 = input_byte ic in
  let b1 = input_byte ic in
  let b2 = input_byte ic in
  let b3 = input_byte ic in
  b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24)

let connect_service () =
  let sock = socket PF_UNIX SOCK_STREAM 0 in
  connect sock (ADDR_UNIX "/tmp/l0_lex_svc.sock");
  sock

let send_request sock data =
  let oc = out_channel_of_descr sock in
  let ic = in_channel_of_descr sock in
  write_u32 oc (Bytes.length data);
  output oc data 0 (Bytes.length data);
  flush oc;
  let resp_len = read_u32 ic in
  let resp = Bytes.create resp_len in
  really_input ic resp 0 resp_len;
  resp

let worker_task sock data results start_idx count barrier =
  (* Wait at barrier *)
  Mutex.lock barrier.Barrier.mutex;
  while not !(barrier.Barrier.ready) do
    Condition.wait barrier.Barrier.cond barrier.Barrier.mutex
  done;
  Mutex.unlock barrier.Barrier.mutex;

  (* Run requests *)
  for i = 0 to count - 1 do
    let t0 = Clock.now () in
    ignore (send_request sock data);
    let dt_ms = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) in
    results.(start_idx + i) <- dt_ms
  done

let () =
  if Array.length Sys.argv < 4 then begin
    Printf.eprintf "usage: run_service_bench_keepalive FILE ITERS THREADS [--out FILE]\n";
    exit 2
  end;

  let file = Sys.argv.(1) in
  let iters = int_of_string Sys.argv.(2) in
  let threads = int_of_string Sys.argv.(3) in
  let out_file =
    try
      let args = Array.to_list Sys.argv in
      let rec find_out idx = function
        | [] -> None
        | "--out" :: file :: _ -> Some file
        | _ :: rest -> find_out (idx + 1) rest
      in
      find_out 0 args
    with _ -> None
  in

  let data = read_file file in
  let per_thread = iters / threads in
  let results = Array.make iters 0.0 in

  Printf.printf "[keepalive] file=%s iters=%d threads=%d\n%!" file iters threads;

  (* Create persistent connections *)
  let sockets = Array.init threads (fun _ -> connect_service ()) in

  (* Create barrier for synchronized start *)
  let barrier = Barrier.create () in

  (* Launch threads *)
  let workers = Array.mapi (fun i sock ->
    Thread.create (fun () ->
      worker_task sock data results (i * per_thread) per_thread barrier
    ) ()
  ) sockets in

  (* Start all threads *)
  Thread.delay 0.01;
  Barrier.release barrier;

  (* Wait for completion *)
  Array.iter Thread.join workers;

  (* Close connections *)
  Array.iter close sockets;

  (* Sort and compute percentiles *)
  Array.sort compare results;
  Bench_utils.Percentiles_strict.dump "Service(keepalive)" results;

  (* Write output file if requested *)
  begin match out_file with
  | Some path ->
      let oc = open_out path in
      Array.iter (Printf.fprintf oc "%.6f\n") results;
      close_out oc;
      Printf.printf "[keepalive] wrote %d samples to %s\n%!" (Array.length results) path
  | None -> ()
  end;

  (* Write tail CSV for slow queries *)
  let tail_size = min 100 (Array.length results) in
  let tail_start = Array.length results - tail_size in
  let oc = open_out "/tmp/l0_service_tail.csv" in
  Printf.fprintf oc "idx,latency_ms\n";
  for i = 0 to tail_size - 1 do
    Printf.fprintf oc "%d,%.6f\n" (tail_start + i) results.(tail_start + i)
  done;
  close_out oc