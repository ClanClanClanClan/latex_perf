(** Binary IPC protocol for the tokeniser service.

    Defines a 16-byte big-endian header followed by a variable-length payload.
    Three message types are supported: request, response, and cancel. *)

type msg_ty = Req | Resp | Cancel
type header = { ty : msg_ty; req_id : int64; len : int }

val header_bytes : int
(** Size of the on-wire header (16 bytes). *)

(** {2 Writing} *)

val write_header : Unix.file_descr -> header -> unit

val write_req : Unix.file_descr -> req_id:int64 -> bytes:bytes -> unit
(** Write a length-prefixed request payload. *)

val write_resp :
  Unix.file_descr ->
  req_id:int64 ->
  status:int ->
  n_tokens:int ->
  issues_len:int ->
  alloc_mb10:int ->
  major_cycles:int ->
  unit

val write_cancel : Unix.file_descr -> req_id:int64 -> unit

(** {2 Reading} *)

val read_header : Unix.file_descr -> header option
(** Returns [None] on EOF or protocol error. *)

type any =
  | Any_req of int64 * bytes
  | Any_resp of int64 * int * int * int * int * int
  | Any_cancel of int64
  | Any_hup  (** Decoded message. [Any_hup] indicates connection close. *)

val read_any : Unix.file_descr -> any
