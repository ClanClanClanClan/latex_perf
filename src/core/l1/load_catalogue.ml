(* load_catalogue.ml — parse macro_catalogue.json into in-memory list *)
open Yojson.Basic
open Yojson.Basic.Util

type token = TText of string | TOp of string | TDelim of string
type macro = string * token list

let token_of_json = function
  | `Assoc [("TText", `String s)] -> TText s
  | `Assoc [("TOp", `String s)] -> TOp s
  | `Assoc [("TDelim", `String s)] -> TDelim s
  | _ -> failwith "unknown token"

let load file : macro list =
  let j = Yojson.Basic.from_file file in
  j |> member "macros" |> to_list |> List.map (fun m ->
    let name = m |> member "name" |> to_string in
    let body = m |> member "body" |> to_list |> List.map token_of_json in
    (name, body)
  )
