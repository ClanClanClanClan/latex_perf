(* check_catalogue_v2.ml — v25r2 validator for macro_catalogue.v25r2.json *)
open Yojson.Basic

let name_ok s =
  let n = String.length s in
  n > 0
  &&
  let ok = ref true in
  for i = 0 to n - 1 do
    match s.[i] with 'A' .. 'Z' | 'a' .. 'z' | '@' -> () | _ -> ok := false
  done;
  !ok

let token_ok = function
  | `Assoc [ ("TText", `String _) ] -> true
  | `Assoc [ ("TOp", `String _) ] -> true
  | `Assoc [ ("TDelim", `String _) ] -> true
  | _ -> false

let body_ok j = match j with `List ts -> List.for_all token_ok ts | _ -> false

let check_entry idx = function
  | `Assoc props as entry -> (
      let find k = List.assoc_opt k props in
      let err msg = Printf.sprintf "entry[%d]: %s" idx msg in
      match find "name" with
      | Some (`String name) -> (
          if not (name_ok name) then Error (err "invalid macro name")
          else
            (* mode *)
            (match find "mode" with
            | Some (`String ("math" | "text" | "any")) -> Ok ()
            | _ -> Error (err "mode must be math|text|any"))
            |> function
            | Error e -> Error e
            | Ok () -> (
                (* arity *)
                (match find "arity" with
                | Some (`Int a) when 0 <= a && a <= 9 -> Ok ()
                | _ -> Error (err "arity must be 0..9"))
                |> function
                | Error e -> Error e
                | Ok () -> (
                    (* safety *)
                    (match find "safety" with
                    | Some (`String "pure") -> Ok ()
                    | _ -> Error (err "safety must be \"pure\""))
                    |> function
                    | Error e -> Error e
                    | Ok () -> (
                        (* side_effects *)
                        (match find "side_effects" with
                        | Some (`List []) -> Ok ()
                        | _ -> Error (err "side_effects must be []"))
                        |> function
                        | Error e -> Error e
                        | Ok () -> (
                            (* expansion/body *)
                            (match find "expansion" with
                            | Some b when body_ok b -> Ok ()
                            | _ ->
                                Error
                                  (err "expansion invalid (must be token list)"))
                            |> function
                            | Error e -> Error e
                            | Ok () -> (
                                (* non_expandable *)
                                match find "non_expandable" with
                                | Some (`Bool true) -> Ok ()
                                | _ ->
                                    Error
                                      (err
                                         "non_expandable must be true for L1 \
                                          catalogue")))))))
      | _ -> Error (err "missing name"))
  | _ -> Error (Printf.sprintf "entry[%d]: not an object" idx)

let check_file path =
  let json = Yojson.Basic.from_file path in
  match json with
  | `Assoc props -> (
      (match List.assoc_opt "schema_version" props with
      | Some (`String "v25r2") -> ()
      | _ -> failwith "schema_version must be v25r2");
      match List.assoc_opt "macros" props with
      | Some (`List items) ->
          let rec loop i = function
            | [] -> Ok ()
            | x :: xs -> (
                match check_entry i x with
                | Ok () -> loop (i + 1) xs
                | Error e -> Error e)
          in
          loop 0 items
      | _ -> Error "missing macros array")
  | _ -> Error "root must be an object"

let () =
  match check_file Sys.argv.(1) with
  | Ok () -> print_endline "OK: catalogue valid (v25r2)"
  | Error e ->
      prerr_endline e;
      exit 1
