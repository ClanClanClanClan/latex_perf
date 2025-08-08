(* L1 Expander - Macro expansion implementation *)

open Lexer_v25

(* Macro definition *)
type macro_def = {
  name: string;
  params: int;
  replacement: token list;
  is_long: bool;
  is_outer: bool;
}

(* Expansion options *)
type options = {
  max_expansion_depth: int;
  max_expansions: int;
  track_source: bool;
}

(* Expansion statistics *)
type expansion_stats = {
  expansions_performed: int;
  max_depth_reached: int;
  time_ms: float;
}

(* Expansion result *)
type result = {
  tokens: token list;
  state: state;
  stats: expansion_stats;
}

(* Expansion state *)
and state = {
  macros: (string, macro_def) Hashtbl.t;
  counters: (string, int) Hashtbl.t;
  environments: string list;  (* Stack of active environments *)
  no_expand: bool;           (* \noexpand flag *)
  expand_after: int;         (* \expandafter count *)
}

(* Default options *)
let default_options = {
  max_expansion_depth = 1000;
  max_expansions = 100000;
  track_source = false;
}

(* Create initial state *)
let initial_state () = {
  macros = Hashtbl.create 1024;
  counters = Hashtbl.create 64;
  environments = [];
  no_expand = false;
  expand_after = 0;
}

(* Define a macro *)
let define_macro state name macro_def =
  Hashtbl.replace state.macros name macro_def;
  state

(* Check if macro is defined *)
let is_defined state name =
  Hashtbl.mem state.macros name

(* Get macro definition *)
let get_macro state name =
  try Some (Hashtbl.find state.macros name)
  with Not_found -> None

(* Register built-in TeX primitives *)
let register_primitives state =
  (* Register common TeX primitives *)
  let primitives = [
    ("def", 0);
    ("let", 0);
    ("newcommand", 0);
    ("renewcommand", 0);
    ("newenvironment", 0);
    ("begin", 1);
    ("end", 1);
    ("if", 0);
    ("else", 0);
    ("fi", 0);
    ("expandafter", 0);
    ("noexpand", 0);
  ] in
  
  List.fold_left (fun st (name, params) ->
    define_macro st name {
      name;
      params;
      replacement = [];  (* Primitives have special handling *)
      is_long = false;
      is_outer = false;
    }
  ) state primitives

(* Parse macro parameters from token list *)
let rec parse_parameters tokens n acc =
  if n = 0 then (List.rev acc, tokens)
  else match tokens with
  | [] -> (List.rev acc, [])
  | TGroupOpen :: rest ->
      (* Parse balanced group as parameter *)
      let (group, remaining) = parse_balanced_group rest 1 [] in
      parse_parameters remaining (n-1) (group :: acc)
  | t :: rest ->
      (* Single token as parameter *)
      parse_parameters rest (n-1) ([t] :: acc)

and parse_balanced_group tokens depth acc =
  match tokens with
  | [] -> (List.rev acc, [])
  | TGroupOpen :: rest ->
      parse_balanced_group rest (depth + 1) (TGroupOpen :: acc)
  | TGroupClose :: rest when depth = 1 ->
      (List.rev acc, rest)
  | TGroupClose :: rest ->
      parse_balanced_group rest (depth - 1) (TGroupClose :: acc)
  | t :: rest ->
      parse_balanced_group rest depth (t :: acc)

(* Substitute parameters in replacement text *)
let substitute_params replacement params =
  List.concat_map (fun token ->
    match token with
    | TParam n when n >= 1 && n <= List.length params ->
        List.nth params (n - 1)
    | t -> [t]
  ) replacement

(* Main expansion function *)
let expand_tokens ?(options=default_options) state tokens =
  let start_time = Unix.gettimeofday () in
  let expansion_count = ref 0 in
  let max_depth = ref 0 in
  
  let rec expand_list depth tokens acc =
    if depth > options.max_expansion_depth then
      failwith "Maximum expansion depth exceeded"
    else if !expansion_count > options.max_expansions then
      failwith "Maximum expansion count exceeded"
    else
      match tokens with
      | [] -> List.rev acc
      | TMacro name :: rest when not state.no_expand ->
          (match get_macro state name with
          | None -> expand_list depth rest (TMacro name :: acc)
          | Some macro ->
              incr expansion_count;
              max_depth := max depth !max_depth;
              
              if macro.params = 0 then
                (* No parameters - simple expansion *)
                let expanded = expand_list (depth + 1) macro.replacement [] in
                expand_list depth (expanded @ rest) acc
              else
                (* Parse parameters *)
                let (params, remaining) = parse_parameters rest macro.params [] in
                let substituted = substitute_params macro.replacement params in
                let expanded = expand_list (depth + 1) substituted [] in
                expand_list depth (expanded @ remaining) acc)
      | t :: rest ->
          expand_list depth rest (t :: acc)
  in
  
  let expanded_tokens = expand_list 0 tokens [] in
  let elapsed = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  
  {
    tokens = expanded_tokens;
    state;
    stats = {
      expansions_performed = !expansion_count;
      max_depth_reached = !max_depth;
      time_ms = elapsed;
    }
  }

(* Expand token array (for L0 integration) *)
let expand_chunk ?(options=default_options) ?state chunk =
  let st = match state with
    | Some s -> s
    | None -> initial_state ()
  in
  let tokens = Array.to_list chunk in
  let result = expand_tokens ~options st tokens in
  (Array.of_list result.tokens, result.state)

(* Expansion control *)
let no_expand_next state =
  { state with no_expand = true }

let expand_after state =
  { state with expand_after = state.expand_after + 1 }

(* Environment management *)
let begin_environment state name =
  { state with environments = name :: state.environments }

let end_environment state name =
  match state.environments with
  | [] -> failwith (Printf.sprintf "No environment to end: %s" name)
  | h :: t when h = name -> { state with environments = t }
  | h :: _ -> failwith (Printf.sprintf "Environment mismatch: expected %s, got %s" h name)

let in_environment state name =
  List.mem name state.environments

(* Counter management *)
let new_counter state name =
  Hashtbl.replace state.counters name 0;
  state

let set_counter state name value =
  Hashtbl.replace state.counters name value;
  state

let get_counter state name =
  try Some (Hashtbl.find state.counters name)
  with Not_found -> None

let step_counter state name =
  match get_counter state name with
  | None -> new_counter state name
  | Some n -> set_counter state name (n + 1)

(* State serialization *)
let state_to_string state =
  (* Simple serialization - could use Marshal for production *)
  let macros_list = Hashtbl.fold (fun k v acc -> (k, v) :: acc) state.macros [] in
  let counters_list = Hashtbl.fold (fun k v acc -> (k, v) :: acc) state.counters [] in
  Printf.sprintf "MACROS:%d;COUNTERS:%d;ENVS:%d"
    (List.length macros_list)
    (List.length counters_list)
    (List.length state.environments)

let state_of_string s =
  (* Stub - would implement proper deserialization *)
  Some (initial_state ())