(* check_catalogue.ml — enforce invariants on macro_catalogue.json *)
open Yojson.Basic.Util

let token_is_l1 = function
  | `Assoc [("TText", `String _)] -> true
  | `Assoc [("TOp", `String _)] -> true
  | `Assoc [("TDelim", `String _)] -> true
  | _ -> false

let name_ok s =
  let n = String.length s in
  let is_start c =
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
  in
  let is_tail c =
    is_start c || ('0' <= c && c <= '9') || c = '_'
  in
  n >= 1 && is_start s.[0] &&
  let ok = ref true in
  for i = 1 to n - 1 do if not (is_tail s.[i]) then ok := false done;
  !ok

let () =
  let j = Yojson.Basic.from_file "macro_catalogue.json" in
  let ms = j |> member "macros" |> to_list in
  let tbl = Hashtbl.create (2 * List.length ms) in
  List.iter (fun m ->
    let name = m |> member "name" |> to_string in
    if not (name_ok name) then (Printf.eprintf "Bad name: %s\n" name; exit 2);
    if Hashtbl.mem tbl name then (Printf.eprintf "Duplicate: %s\n" name; exit 2);
    Hashtbl.add tbl name ();
    let body = m |> member "body" |> to_list in
    if List.length body <> 1 then (Printf.eprintf "Non-singleton body: %s\n" name; exit 3);
    List.iter (fun tok -> if not (token_is_l1 tok) then
      (Printf.eprintf "Non-L1 token in body: %s\n" name; exit 4)) body
  ) ms;
  print_endline "CATALOGUE OK"
