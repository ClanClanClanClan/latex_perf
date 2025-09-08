open Unix

type request = {
  doc_len: int;
  doc_content: bytes;
}

type response = {
  token_count: int;
  digest: int64;
  process_ns: int64;
}

let marshal_request req =
  let buf = Buffer.create (8 + Bytes.length req.doc_content) in
  Buffer.add_int32_le buf (Int32.of_int req.doc_len);
  Buffer.add_bytes buf req.doc_content;
  Buffer.contents buf

let unmarshal_request data =
  if String.length data < 4 then failwith "Request too short";
  let doc_len = Int32.to_int (String.get_int32_le data 0) in
  let doc_content = Bytes.create doc_len in
  Bytes.blit_string data 4 doc_content 0 doc_len;
  { doc_len; doc_content }

let marshal_response resp =
  let buf = Buffer.create 20 in
  Buffer.add_int32_le buf (Int32.of_int resp.token_count);
  Buffer.add_int64_le buf resp.digest;
  Buffer.add_int64_le buf resp.process_ns;
  Buffer.contents buf

let unmarshal_response data =
  if String.length data < 20 then failwith "Response too short";
  let token_count = Int32.to_int (String.get_int32_le data 0) in
  let digest = String.get_int64_le data 4 in
  let process_ns = String.get_int64_le data 12 in
  { token_count; digest; process_ns }

let send_all sock data =
  let len = String.length data in
  let data_bytes = Bytes.of_string data in
  let rec loop sent =
    if sent < len then
      let n = send sock data_bytes sent (len - sent) [] in
      loop (sent + n)
  in
  loop 0

let recv_all sock len =
  let buf = Bytes.create len in
  let rec loop recvd =
    if recvd < len then
      let n = recv sock buf recvd (len - recvd) [] in
      if n = 0 then failwith "Connection closed";
      loop (recvd + n)
  in
  loop 0;
  Bytes.to_string buf

let create_server_socket path =
  (try unlink path with Unix_error _ -> ());
  let sock = socket PF_UNIX SOCK_STREAM 0 in
  bind sock (ADDR_UNIX path);
  listen sock 5;
  sock

let connect_to_server path =
  let sock = socket PF_UNIX SOCK_STREAM 0 in
  connect sock (ADDR_UNIX path);
  sock
