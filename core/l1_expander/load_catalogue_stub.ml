(* Load_catalogue stub - fallback when Yojson is not available *)

type token = TText of string | TOp of string | TDelim of string
type macro = string * token list

let load file : macro list =
  (* Always fail to trigger fallback mechanism *)
  raise (Sys_error "Yojson not available - using fallback macros")
