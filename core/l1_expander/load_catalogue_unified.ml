(* load_catalogue_unified.ml - Unified loader for v25r2 and argsafe catalogs *)

module V25R2 = struct
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
  
  let load path =
    let json = Yojson.Basic.from_file path in
    match json with
    | `Assoc props ->
        let items =
          match List.assoc_opt "macros" props with
          | Some (`List xs) -> xs
          | _ -> failwith "missing macros"
        in
        List.map (fun j ->
          let open Yojson.Basic.Util in
          let name = j |> member "name" |> to_string in
          let expansion = 
            j |> member "expansion" |> to_list |> List.map token_of_json in
          let mode = 
            j |> member "mode" |> to_string |> mode_of_string in
          let category = 
            j |> member "category" |> to_string_option |> Option.value ~default:"symbol" in
          let arity = 
            j |> member "arity" |> to_int in
          let expand_in_math = 
            j |> member "expand_in_math" |> to_bool_option |> Option.value ~default:true in
          let expand_in_text = 
            j |> member "expand_in_text" |> to_bool_option |> Option.value ~default:true in
          let non_expandable = 
            j |> member "non_expandable" |> to_bool_option |> Option.value ~default:true in
          { name; mode; category; arity; expansion; 
            expand_in_math; expand_in_text; non_expandable }
        ) items
    | _ -> failwith "root must be object"
end

module ArgSafe = struct
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
  
  let load path =
    (* Implementation from load_catalogue_v3.ml *)
    failwith "ArgSafe loader not yet integrated - use load_catalogue_v3.ml"
end

(* Unified interface *)
type unified_macro =
  | Symbol of V25R2.entry
  | Argumentful of ArgSafe.macro

let load_all () =
  let symbols = 
    try V25R2.load "macro_catalogue.v25r2.json" 
        |> List.map (fun e -> Symbol e)
    with _ -> [] in
  let argumentful = 
    try ArgSafe.load "macro_catalogue.argsafe.v25r1.json"
        |> List.map (fun m -> Argumentful m) 
    with _ -> [] in
  symbols @ argumentful

let count_macros () =
  let all = load_all () in
  Printf.printf "Total macros loaded: %d\n" (List.length all);
  let symbols = List.filter (function Symbol _ -> true | _ -> false) all in
  let args = List.filter (function Argumentful _ -> true | _ -> false) all in
  Printf.printf "  Symbol macros: %d\n" (List.length symbols);
  Printf.printf "  Argumentful macros: %d\n" (List.length args)
