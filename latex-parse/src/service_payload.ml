type origin = Primary | Hedge | Unknown

type t = {
  status : int;
  n_tokens : int;
  issues_len : int;
  origin : origin;
}

let be32 (b:bytes) off =
  (int_of_char (Bytes.get b off) lsl 24)
  lor (int_of_char (Bytes.get b (off+1)) lsl 16)
  lor (int_of_char (Bytes.get b (off+2)) lsl 8)
  lor (int_of_char (Bytes.get b (off+3)))

let parse_payload (resp:bytes) : (t, string) result =
  let len = Bytes.length resp in
  if len <> 13 then Error (Printf.sprintf "payload_len=%d expected=13" len) else
  let status    = be32 resp 0 in
  let n_tokens  = be32 resp 4 in
  let issues_len = be32 resp 8 in
  let origin =
    match int_of_char (Bytes.get resp 12) with
    | 1 -> Primary
    | 2 -> Hedge
    | _ -> Unknown
  in
  Ok { status; n_tokens; issues_len; origin }

