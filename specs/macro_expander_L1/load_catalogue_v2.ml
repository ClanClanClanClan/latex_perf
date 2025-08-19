(* load_catalogue_v2.ml — load v25r2 JSON (backward compatible) *)
open Yojson.Basic

type token =
  | TText of string
  | TOp of string
  | TDelim of string

type mode = Math | Text | Any

type entry = {
  name : string;
  mode : mode;
  category : string;
  arity : int;
  expansion : token list;
  expand_in_math : bool;
  expand_in_text : bool;
  non_expandable : bool;
}

let token_of_json = function
  | `Assoc [("TText", `String s)] -> TText s
  | `Assoc [("TOp", `String s)] -> TOp s
  | `Assoc [("TDelim", `String s)] -> TDelim s
  | j -> failwith ("bad token: " ^ Yojson.Basic.to_string j)

let mode_of_string = function
  | "math" -> Math
  | "text" -> Text
  | "any"  -> Any
  | s -> failwith ("bad mode: "^s)

let list_assoc_exn k = function
  | `Assoc props -> (match List.assoc_opt k props with Some v -> v | None -> failwith ("missing "^k))
  | _ -> failwith "expected object"

let entry_of_json j =
  match j with
  | `Assoc _ ->
      let name = match list_assoc_exn "name" j with `String s -> s | _ -> failwith "name" in
      (* "expansion" (new) if present, else legacy "body" *)
      let body_json =
        match list_assoc_exn "expansion" j with
        | (`List _ as l) -> l
        | _ -> list_assoc_exn "body" j
      in
      let expansion =
        match body_json with
        | `List xs -> List.map token_of_json xs
        | _ -> failwith "expansion must be list"
      in
      let mode =
        match list_assoc_exn "mode" j with
        | `String s -> mode_of_string s
        | _ -> Any
      in
      let category =
        match list_assoc_exn "category" j with
        | `String s -> s
        | _ -> "symbol"
      in
      let arity =
        match list_assoc_exn "arity" j with
        | `Int n -> n
        | _ -> 0
      in
      let expand_in_math =
        match list_assoc_exn "expand_in_math" j with
        | `Bool b -> b
        | _ -> true
      in
      let expand_in_text =
        match list_assoc_exn "expand_in_text" j with
        | `Bool b -> b
        | _ -> true
      in
      let non_expandable =
        match list_assoc_exn "non_expandable" j with
        | `Bool b -> b
        | _ -> true
      in
      { name; mode; category; arity; expansion; expand_in_math; expand_in_text; non_expandable }
  | _ -> failwith "entry not an object"

let load path =
  let json = Yojson.Basic.from_file path in
  match json with
  | `Assoc props ->
      let items =
        match List.assoc_opt "macros" props with
        | Some (`List xs) -> xs
        | _ -> failwith "missing macros"
      in
      List.map entry_of_json items
  | _ -> failwith "root must be object"
