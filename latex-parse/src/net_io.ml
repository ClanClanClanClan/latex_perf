(** Robust socket I/O helpers.

    All functions retry on {!Unix.EINTR} and return [Error] on EOF or
    short-write instead of raising exceptions. *)

type error = Eof | Short_write

let error_to_string = function
  | Eof -> "unexpected EOF"
  | Short_write -> "short write (0 bytes written)"

let rec read_exact fd buf ofs len =
  if len = 0 then Ok ()
  else
    try
      let n = Unix.read fd buf ofs len in
      if n = 0 then Error Eof else read_exact fd buf (ofs + n) (len - n)
    with Unix.Unix_error (Unix.EINTR, _, _) -> read_exact fd buf ofs len

let rec write_all fd buf ofs len =
  if len = 0 then Ok ()
  else
    try
      let n = Unix.write fd buf ofs len in
      if n = 0 then Error Short_write else write_all fd buf (ofs + n) (len - n)
    with Unix.Unix_error (Unix.EINTR, _, _) -> write_all fd buf ofs len

(** Convenience wrappers that raise [Failure] on error.

    Use these when callers already have a top-level [try ... with] that converts
    exceptions to connection-close / error-result behaviour. *)

let read_exact_exn fd buf ofs len =
  match read_exact fd buf ofs len with
  | Ok () -> ()
  | Error e -> failwith (error_to_string e)

let write_all_exn fd buf ofs len =
  match write_all fd buf ofs len with
  | Ok () -> ()
  | Error e -> failwith (error_to_string e)
