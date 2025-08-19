
(* load_catalogue_v3.ml — load & validate the epsilon-safe L1 macro catalogue *)
open Yojson.Safe

type mode = Text | Math | Both
type category = Style | Emphasis | Verbatim | Mathstyle | Boxing

type template =
  | Inline of string
  | Builtin of string

type macro = {
  name : string;
  aliases : string list;
  mode : mode;
  category : category;
  positional : int;
  kinds : string list;
  template : template;
  epsilon_allowed : bool;
  notes : string option;
}

type catalogue = {
  id : string;
  version : string;
  macros : macro list;
}

let mode_of_string = function
  | "text" -> Text | "math" -> Math | "both" -> Both
  | s -> failwith ("unknown mode: " ^ s)

let category_of_string = function
  | "style" -> Style | "emphasis" -> Emphasis | "verbatim" -> Verbatim
  | "mathstyle" -> Mathstyle | "boxing" -> Boxing
  | s -> failwith ("unknown category: " ^ s)

let string_member key = function `Assoc kv -> (try match List.assoc key kv with `String s -> s | _ -> raise Not_found with Not_found -> failwith ("missing string "^key)) | _ -> failwith "expected object"
let opt_string_member key = function `Assoc kv -> (try match List.assoc key kv with `String s -> Some s | `Null -> None | _ -> None with Not_found -> None) | _ -> None
let bool_member key = function `Assoc kv -> (try match List.assoc key kv with `Bool b -> b | _ -> raise Not_found with Not_found -> failwith ("missing bool "^key)) | _ -> failwith "expected object"
let int_member key = function `Assoc kv -> (try match List.assoc key kv with `Int i -> i | _ -> raise Not_found with Not_found -> failwith ("missing int "^key)) | _ -> failwith "expected object"
let list_member key = function `Assoc kv -> (try match List.assoc key kv with `List xs -> xs | _ -> raise Not_found with Not_found -> failwith ("missing array "^key)) | _ -> failwith "expected object"
let assoc_member key = function `Assoc kv -> (try List.assoc key kv with Not_found -> failwith ("missing object "^key)) | _ -> failwith "expected object"

let parse_macro (j: Yojson.Safe.t) : macro =
  let name = string_member "name" j in
  let aliases =
    match j with
    | `Assoc kv -> (match List.assoc_opt "aliases" kv with Some (`List xs) -> List.filter_map (function `String s -> Some s | _ -> None) xs | _ -> [])
    | _ -> []
  in
  let mode = mode_of_string (string_member "mode" j) in
  let category = category_of_string (string_member "category" j) in
  let epsilon_allowed = bool_member "epsilon_allowed" j in
  let args = assoc_member "args" j in
  let positional = int_member "positional" args in
  let kinds = list_member "kinds" args |> List.filter_map (function `String s -> Some s | _ -> None) in
  let templ = assoc_member "template" j in
  let template =
    match string_member "kind" templ with
    | "inline" -> Inline (string_member "body" templ)
    | "builtin" -> Builtin (string_member "builtin" templ)
    | k -> failwith ("unknown template kind " ^ k)
  in
  let notes = opt_string_member "notes" j in
  { name; aliases; mode; category; positional; kinds; template; epsilon_allowed; notes }

let allowed_inline_css = [
  "\\bfseries"; "\\itshape"; "\\ttfamily"; "\\sffamily"; "\\scshape";
  "\\mdseries"; "\\normalfont"; "\\rmfamily"; "\\slshape"; "\\upshape";
  "\\mathrm"; "\\mathbf"; "\\mathsf"; "\\mathtt"; "\\mathit"; "\\mathnormal"
]

let eps_inline_safe (s: string) : bool =
  (* very simple checker: only braces, spaces, $1..$3, and the allowed control sequences *)
  let re_placeholder = Str.regexp "\\$[123]" in
  let s' = Str.global_replace re_placeholder "" s in
  let re_cs = Str.regexp "\\\\[A-Za-z@]+" in
  let rec check pos =
    if pos >= String.length s' then true
    else if String.get s' pos = '{' || String.get s' pos = '}' || String.get s' pos = ' ' then
      check (pos+1)
    else if Str.string_match re_cs s' pos then
      let cs = Str.matched_string s' in
      if List.mem cs allowed_inline_css then
        check (Str.match_end ())
      else false
    else false
  in
  check 0

let validate_macro (m: macro) : (bool * string option) =
  if not m.epsilon_allowed then (false, Some "epsilon_allowed=false")
  else match m.template with
  | Builtin "verb" | Builtin "verb_star" | Builtin "mbox" | Builtin "textsuperscript" | Builtin "textsubscript" | Builtin "ensuremath" -> (true, None)
  | Builtin other -> (false, Some ("unknown builtin "^other))
  | Inline body -> if eps_inline_safe body then (true, None) else (false, Some ("inline template not epsilon-safe: "^body))

let load_catalogue (file: string) : catalogue =
  let j = Yojson.Safe.from_file file in
  let cat = assoc_member "catalog" j in
  let id = string_member "id" cat in
  let version = string_member "version" cat in
  let macros = list_member "macros" cat |> List.map parse_macro in
  { id; version; macros }
