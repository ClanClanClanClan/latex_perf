(** Tests for ipc — binary IPC message protocol. Tests only the exported API
    (header_bytes, msg_ty type). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_ipc]\n%!";

  (* Test 1: header_bytes constant *)
  check "header_bytes = 16" (Latex_parse_lib.Ipc.header_bytes = 16);

  (* Test 2: msg_ty constructors exist *)
  let _req = Latex_parse_lib.Ipc.Req in
  let _resp = Latex_parse_lib.Ipc.Resp in
  let _cancel = Latex_parse_lib.Ipc.Cancel in
  check "msg_ty constructors" true;

  (* Test 3: header record construction *)
  let h : Latex_parse_lib.Ipc.header =
    { ty = Latex_parse_lib.Ipc.Req; req_id = 42L; len = 100 }
  in
  check "header.ty = Req" (h.ty = Latex_parse_lib.Ipc.Req);
  check "header.req_id = 42" (h.req_id = 42L);
  check "header.len = 100" (h.len = 100);

  (* Test 4: header with zero values *)
  let h0 : Latex_parse_lib.Ipc.header =
    { ty = Latex_parse_lib.Ipc.Resp; req_id = 0L; len = 0 }
  in
  check "zero header" (h0.req_id = 0L && h0.len = 0);

  (* Test 5: header with max req_id *)
  let h_max : Latex_parse_lib.Ipc.header =
    { ty = Latex_parse_lib.Ipc.Cancel; req_id = Int64.max_int; len = 0 }
  in
  check "max req_id" (h_max.req_id = Int64.max_int);

  (* Note: write_header/read_header require Unix.file_descr (pipe or socket) and
     are tested via integration tests in rest-smoke and service tests. *)
  Printf.printf "[test_ipc] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_ipc] %d failures\n%!" !fails;
    exit 1)
