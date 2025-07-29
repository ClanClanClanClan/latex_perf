(** Stub implementation of expander for v25
    This is a placeholder until we extract from Coq *)

open Types

(** Macro definition *)
type macro_definition = {
  macro_name : string;
  macro_body : token list;
  is_builtin : bool;
}

(** Macro environment *)
type macro_env = (string * macro_definition) list

(** Empty environment *)
let empty_env = []

(* Import common macro definitions *)
(* Note: Common_macros is loaded separately *)

(* Create lookup table for all built-in macros *)
let builtin_macro_table = 
  let tbl = Hashtbl.create (List.length Common_macros.builtin_macro_list) in
  List.iter (fun (name, body) ->
    let macro = {
      macro_name = name;
      macro_body = body;
      is_builtin = true;
    } in
    Hashtbl.add tbl name macro
  ) Common_macros.builtin_macro_list;
  tbl

(* For compatibility, expose individual macros *)
let find_macro name =
  try Some (Hashtbl.find builtin_macro_table name)
  with Not_found -> None

(** Add macro to environment *)
let add_macro env name def =
  (name, def) :: env

(** Lookup macro - first check environment, then built-ins *)
let lookup_macro env name =
  try Some (List.assoc name env)
  with Not_found -> find_macro name

let get_builtin_macro name =
  match find_macro name with
  | Some m -> m
  | None -> failwith (Printf.sprintf "Built-in macro %s not found" name)

let latex_macro = get_builtin_macro "LaTeX"
let tex_macro = get_builtin_macro "TeX"  
let textbf_macro = get_builtin_macro "textbf"
let emph_macro = get_builtin_macro "emph"
let ldots_macro = get_builtin_macro "ldots"
let textit_macro = get_builtin_macro "textit"

(** Expand one step *)
let expand_one_step env tokens =
  let rec scan acc = function
    | [] -> None
    | TCommand cmd :: rest ->
        (match lookup_macro env cmd with
         | Some macro ->
             Some (List.rev_append acc (macro.macro_body @ rest), cmd)
         | None ->
             scan (TCommand cmd :: acc) rest)
    | tok :: rest ->
        scan (tok :: acc) rest
  in
  scan [] tokens

(** Expand with fuel *)
let rec expand_with_fuel env tokens fuel =
  if fuel <= 0 then
    (tokens, [])
  else
    match expand_one_step env tokens with
    | None -> (tokens, [])
    | Some (tokens', macro_used) ->
        let (final_tokens, macros) = expand_with_fuel env tokens' (fuel - 1) in
        (final_tokens, macro_used :: macros)

(** Exception for recursive macros *)
exception Recursive_macro of string

(** Catalog module - just an alias to this module for compatibility *)
module Catalog = struct
  let latex_macro = latex_macro
  let tex_macro = tex_macro  
  let textbf_macro = textbf_macro
  let emph_macro = emph_macro
  let ldots_macro = ldots_macro
  let textit_macro = textit_macro
end