type msg_ty = Req | Resp | Cancel
let ty_to_u32 = function Req->1 | Resp->2 | Cancel->3
let u32_to_ty = function 1l->Req | 2l->Resp | 3l->Cancel | _->failwith "bad ty"
type header = { ty:msg_ty; req_id:int64; len:int }
let header_bytes = 16

let be32_put b off v =
  Bytes.set b off     (Char.chr ((v lsr 24) land 0xFF));
  Bytes.set b (off+1) (Char.chr ((v lsr 16) land 0xFF));
  Bytes.set b (off+2) (Char.chr ((v lsr  8) land 0xFF));
  Bytes.set b (off+3) (Char.chr ( v        land 0xFF))
let be32_get b off =
  ((Char.code (Bytes.get b off)) lsl 24)
  lor ((Char.code (Bytes.get b (off+1))) lsl 16)
  lor ((Char.code (Bytes.get b (off+2))) lsl 8)
  lor (Char.code (Bytes.get b (off+3)))

let be64_put b off v =
  let open Int64 in
  Bytes.set b (off+0) (Char.chr (to_int (shift_right_logical v 56)));
  Bytes.set b (off+1) (Char.chr (to_int (shift_right_logical v 48)));
  Bytes.set b (off+2) (Char.chr (to_int (shift_right_logical v 40)));
  Bytes.set b (off+3) (Char.chr (to_int (shift_right_logical v 32)));
  Bytes.set b (off+4) (Char.chr (to_int (shift_right_logical v 24)));
  Bytes.set b (off+5) (Char.chr (to_int (shift_right_logical v 16)));
  Bytes.set b (off+6) (Char.chr (to_int (shift_right_logical v  8)));
  Bytes.set b (off+7) (Char.chr (to_int v))

let rec write_all fd b o l =
  if l=0 then () else
  let n = Unix.write fd b o l in
  if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)

let rec read_exact fd b o l =
  if l=0 then () else
  let n = Unix.read fd b o l in
  if n=0 then failwith "eof" else read_exact fd b (o+n) (l-n)

let write_header fd (h:header) =
  let b = Bytes.create header_bytes in
  be32_put b 0 (ty_to_u32 h.ty); be64_put b 4 h.req_id; be32_put b 12 h.len;
  write_all fd b 0 header_bytes

let read_header fd : header option =
  let b = Bytes.create header_bytes in
  try
    read_exact fd b 0 header_bytes;
    let ty = u32_to_ty (Int32.of_int (be32_get b 0)) in
    let open Int64 in
    let id =
      logor (shift_left (of_int (Char.code (Bytes.get b 4))) 56)
      (logor (shift_left (of_int (Char.code (Bytes.get b 5))) 48)
      (logor (shift_left (of_int (Char.code (Bytes.get b 6))) 40)
      (logor (shift_left (of_int (Char.code (Bytes.get b 7))) 32)
      (logor (shift_left (of_int (Char.code (Bytes.get b 8))) 24)
      (logor (shift_left (of_int (Char.code (Bytes.get b 9))) 16)
      (logor (shift_left (of_int (Char.code (Bytes.get b 10))) 8)
             (of_int (Char.code (Bytes.get b 11))))))))) in
    Some { ty; req_id=id; len=be32_get b 12 }
  with _ -> None

let write_req fd ~req_id ~(bytes:bytes) =
  let len = 4 + Bytes.length bytes in
  let p = Bytes.create len in
  be32_put p 0 (Bytes.length bytes); Bytes.blit bytes 0 p 4 (Bytes.length bytes);
  write_header fd { ty=Req; req_id; len }; write_all fd p 0 len

let write_resp fd ~req_id ~status ~n_tokens ~issues_len ~alloc_mb10 ~major_cycles =
  let p = Bytes.create 20 in
  be32_put p 0 status; be32_put p 4 n_tokens; be32_put p 8 issues_len;
  be32_put p 12 alloc_mb10; be32_put p 16 major_cycles;
  write_header fd { ty=Resp; req_id; len=20 }; write_all fd p 0 20

let write_cancel fd ~req_id = write_header fd { ty=Cancel; req_id; len=0 }

type any =
  | Any_req of int64 * bytes
  | Any_resp of int64 * int * int * int * int * int
  | Any_cancel of int64
  | Any_hup

let read_any fd =
  match read_header fd with
  | None -> Any_hup
  | Some h ->
    begin match h.ty with
    | Req ->
        let p = Bytes.create h.len in read_exact fd p 0 h.len;
        let ilen = be32_get p 0 in
        Any_req (h.req_id, Bytes.sub p 4 ilen)
    | Resp ->
        let p = Bytes.create h.len in read_exact fd p 0 h.len;
        let g off = be32_get p off in
        Any_resp (h.req_id, g 0, g 4, g 8, g 12, g 16)
    | Cancel -> Any_cancel h.req_id
    end