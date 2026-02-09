(** Parsing of the 13-byte service response payload. *)

type origin = Primary | Hedge | Unknown
type t = { status : int; n_tokens : int; issues_len : int; origin : origin }

val parse_payload : bytes -> (t, string) result
(** Decode a 13-byte response. Returns [Error] if the length is wrong. *)
