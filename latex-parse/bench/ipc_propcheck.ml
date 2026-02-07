open Latex_parse_lib.Ipc

let rand_buf n =
  let b = Bytes.create n in
  for i = 0 to n - 1 do
    Bytes.set b i (Char.chr (Random.int 256))
  done;
  b

let roundtrip_once () =
  let sv, sc = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  match Unix.fork () with
  | 0 ->
      Unix.close sv;
      let rec loop () =
        match read_any sc with
        | Any_req (id, payload) ->
            write_resp sc ~req_id:id ~status:0 ~n_tokens:(Bytes.length payload)
              ~issues_len:0 ~alloc_mb10:0 ~major_cycles:0;
            loop ()
        | Any_hup -> exit 0
        | _ -> loop ()
      in
      loop ()
  | pid ->
      Unix.close sc;
      for _ = 1 to 1000 do
        let len = Random.int 65536 in
        let p = rand_buf len in
        let id = Int64.of_int (Random.bits ()) in
        write_req sv ~req_id:id ~bytes:p;
        match read_any sv with
        | Any_resp (rid, _st, nt, _iss, _mb, _maj)
          when rid = id && nt = Bytes.length p ->
            ()
        | _ -> failwith "IPC roundtrip mismatch"
      done;
      Unix.close sv;
      ignore (Unix.waitpid [] pid)

let () =
  Random.init 42;
  for _ = 1 to 100 do
    roundtrip_once ()
  done;
  print_endline "IPC property check: OK"
