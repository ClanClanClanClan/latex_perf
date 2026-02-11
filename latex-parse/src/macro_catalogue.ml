(** Production L1 macro expander with v25r2 + argsafe catalogue support.

    Loads 383 symbol macros (arity-0, Unicode expansions) and 23 argumentful
    macros (epsilon-safe templates) from JSON catalogues. Performs mode-aware
    expansion with bounded iteration. *)

(* ── Token types ────────────────────────────────────────────────────── *)

type token = TText of string | TOp of string | TDelim of string

type mode =
  | Math
  | Text
  | Any
  | Both
      (** [Math] = expand only in math context, [Text] = only in text context,
          [Any]/[Both] = expand in either context. *)

(* ── Catalogue entry types ──────────────────────────────────────────── *)

type symbol_entry = {
  name : string;
  mode : mode;
  expansion : token list;
  expand_in_math : bool;
  expand_in_text : bool;
}

type template = Inline of string | Builtin of string

type argsafe_entry = {
  name : string;
  mode : mode;
  category : string;
  positional : int;
  kinds : string list;
  template : template;
}

type entry = Symbol of symbol_entry | Argsafe of argsafe_entry

type catalogue = {
  symbols : (string, symbol_entry) Hashtbl.t;
  argsafe : (string, argsafe_entry) Hashtbl.t;
  all_names : (string, entry) Hashtbl.t;
}

(* ── Helpers ────────────────────────────────────────────────────────── *)

let token_to_string = function TText s | TOp s | TDelim s -> s
let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let take_ident s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && is_letter s.[!j] do
    incr j
  done;
  !j

(** Find balanced brace block starting at position [i]. Returns
    [Some (content_offset, content_length)] or [None]. *)
let find_brace_block s i =
  let n = String.length s in
  if i >= n || s.[i] <> '{' then None
  else
    let j = ref (i + 1) in
    let depth = ref 1 in
    while !j < n && !depth > 0 do
      (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
      incr j
    done;
    if !depth = 0 then Some (i + 1, !j - i - 2) else None

(* ── JSON loaders ───────────────────────────────────────────────────── *)

module Y = Yojson.Safe
module U = Yojson.Safe.Util

let mode_of_string = function
  | "math" -> Math
  | "text" -> Text
  | "any" -> Any
  | "both" -> Both
  | s -> failwith ("macro_catalogue: unknown mode: " ^ s)

let token_of_json = function
  | `Assoc [ ("TText", `String s) ] -> TText s
  | `Assoc [ ("TOp", `String s) ] -> TOp s
  | `Assoc [ ("TDelim", `String s) ] -> TDelim s
  | j -> failwith ("macro_catalogue: bad token: " ^ Y.to_string j)

let string_field k j =
  try U.to_string (U.member k j)
  with _ -> failwith ("macro_catalogue: missing string field: " ^ k)

let int_field k j =
  try U.to_int (U.member k j)
  with _ -> failwith ("macro_catalogue: missing int field: " ^ k)

let bool_field_opt k default j =
  try match U.member k j with `Bool b -> b | `Null -> default | _ -> default
  with _ -> default

(** Load v25r2 symbol catalogue (383 arity-0 macros). *)
let load_v25r2 path =
  let json = Y.from_file path in
  let macros =
    try U.to_list (U.member "macros" json) with _ -> failwith "missing macros"
  in
  List.map
    (fun j ->
      let name = string_field "name" j in
      let mode = mode_of_string (string_field "mode" j) in
      let expansion_json =
        try U.to_list (U.member "expansion" j)
        with _ -> (
          try U.to_list (U.member "body" j)
          with _ -> failwith ("no expansion for " ^ name))
      in
      let expansion = List.map token_of_json expansion_json in
      let expand_in_math = bool_field_opt "expand_in_math" true j in
      let expand_in_text = bool_field_opt "expand_in_text" true j in
      { name; mode; expansion; expand_in_math; expand_in_text })
    macros

(** Load argsafe catalogue (23 argumentful epsilon-safe macros). *)
let load_argsafe path =
  let json = Y.from_file path in
  let cat =
    try U.member "catalog" json
    with _ -> failwith "missing catalog in argsafe"
  in
  let macros =
    try U.to_list (U.member "macros" cat) with _ -> failwith "missing macros"
  in
  List.map
    (fun j ->
      let name = string_field "name" j in
      let mode =
        let s = string_field "mode" j in
        match s with
        | "text" -> Text
        | "math" -> Math
        | "both" -> Both
        | _ -> mode_of_string s
      in
      let category = string_field "category" j in
      let args = U.member "args" j in
      let positional = int_field "positional" args in
      let kinds =
        try
          U.to_list (U.member "kinds" args)
          |> List.filter_map (function `String s -> Some s | _ -> None)
        with _ -> []
      in
      let templ = U.member "template" j in
      let template =
        match string_field "kind" templ with
        | "inline" -> Inline (string_field "body" templ)
        | "builtin" -> Builtin (string_field "builtin" templ)
        | k -> failwith ("unknown template kind: " ^ k)
      in
      { name; mode; category; positional; kinds; template })
    macros

(* ── Epsilon safety validation ──────────────────────────────────────── *)

let allowed_inline_css =
  [
    "\\bfseries";
    "\\itshape";
    "\\ttfamily";
    "\\sffamily";
    "\\scshape";
    "\\mdseries";
    "\\normalfont";
    "\\rmfamily";
    "\\slshape";
    "\\upshape";
    "\\mathrm";
    "\\mathbf";
    "\\mathsf";
    "\\mathtt";
    "\\mathit";
    "\\mathnormal";
    (* Math alphabets added in v25r2 expansion *)
    "\\mathbb";
    "\\mathcal";
    "\\mathfrak";
    "\\mathscr";
  ]

let eps_inline_safe (s : string) : bool =
  (* Strip $1..$3 placeholders, then check remaining characters are only braces,
     spaces, and allowed control sequences. *)
  let buf = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && s.[!i] = '$' && s.[!i + 1] >= '1' && s.[!i + 1] <= '3' then
      i := !i + 2
    else (
      Buffer.add_char buf s.[!i];
      incr i)
  done;
  let s' = Buffer.contents buf in
  let n' = String.length s' in
  let pos = ref 0 in
  let ok = ref true in
  while !pos < n' && !ok do
    let c = s'.[!pos] in
    if c = '{' || c = '}' || c = ' ' then incr pos
    else if c = '\\' then
      let j = take_ident s' (!pos + 1) in
      if j > !pos + 1 then
        let cs = String.sub s' !pos (j - !pos) in
        if List.mem cs allowed_inline_css then pos := j else ok := false
      else ok := false
    else ok := false
  done;
  !ok

let validate_epsilon (m : argsafe_entry) : bool * string option =
  match m.template with
  | Builtin "verb"
  | Builtin "verb_star"
  | Builtin "mbox"
  | Builtin "textsuperscript"
  | Builtin "textsubscript"
  | Builtin "ensuremath"
  (* New builtins added in v25r2 expansion *)
  | Builtin "underline"
  | Builtin "math_accent"
  | Builtin "passthrough" ->
      (true, None)
  | Builtin other -> (false, Some ("unknown builtin " ^ other))
  | Inline body ->
      if eps_inline_safe body then (true, None)
      else (false, Some ("inline template not epsilon-safe: " ^ body))

(* ── Catalogue construction ─────────────────────────────────────────── *)

let create sym_list arg_list =
  let symbols = Hashtbl.create (List.length sym_list) in
  let argsafe = Hashtbl.create (List.length arg_list) in
  let all_names =
    Hashtbl.create (List.length sym_list + List.length arg_list)
  in
  List.iter
    (fun (e : symbol_entry) ->
      Hashtbl.replace symbols e.name e;
      Hashtbl.replace all_names e.name (Symbol e))
    sym_list;
  List.iter
    (fun (e : argsafe_entry) ->
      Hashtbl.replace argsafe e.name e;
      Hashtbl.replace all_names e.name (Argsafe e))
    arg_list;
  { symbols; argsafe; all_names }

let load ~v25r2_path ~argsafe_path =
  let sym_list = load_v25r2 v25r2_path in
  let arg_list = load_argsafe argsafe_path in
  (* Validate epsilon safety for all argsafe entries *)
  List.iter
    (fun (m : argsafe_entry) ->
      let ok, reason = validate_epsilon m in
      if not ok then
        Printf.eprintf
          "[macro-catalogue] WARNING: %s failed epsilon check: %s\n%!" m.name
          (Option.value ~default:"unknown" reason))
    arg_list;
  create sym_list arg_list

(* ── Query ──────────────────────────────────────────────────────────── *)

let symbol_count cat = Hashtbl.length cat.symbols
let argsafe_count cat = Hashtbl.length cat.argsafe

let lookup cat name =
  match Hashtbl.find_opt cat.all_names name with
  | Some _ as r -> r
  | None -> None

(* ── Expansion engine ───────────────────────────────────────────────── *)

let max_expansions = 256

(** Should we expand a symbol entry given the current math/text context? *)
let should_expand_symbol (e : symbol_entry) ~in_math =
  if in_math then
    e.expand_in_math
    && (e.mode = Math || e.mode = Any || e.mode = Both || e.mode = Text)
  else
    e.expand_in_text
    && (e.mode = Text || e.mode = Any || e.mode = Both || e.mode = Math)

(** Should we expand an argsafe entry given the current math/text context? *)
let should_expand_argsafe (e : argsafe_entry) ~in_math =
  match e.mode with Both | Any -> true | Math -> in_math | Text -> not in_math

(** Apply an inline template by substituting $1 with the argument content. *)
let apply_inline_template body arg =
  let buf = Buffer.create (String.length body + String.length arg) in
  let n = String.length body in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && body.[!i] = '$' && body.[!i + 1] = '1' then (
      Buffer.add_string buf arg;
      i := !i + 2)
    else (
      Buffer.add_char buf body.[!i];
      incr i)
  done;
  Buffer.contents buf

(** Apply a builtin template to the parsed argument. *)
let apply_builtin builtin_name arg =
  match builtin_name with
  | "mbox" | "textsuperscript" | "textsubscript" | "ensuremath" -> arg
  | "verb" | "verb_star" -> arg
  | "underline" | "math_accent" | "passthrough" -> arg
  | _ -> arg (* unknown builtins: passthrough *)

(** Single-pass expansion: scans the string, expanding known macros once.
    Returns the expanded string. Tracks math/text context for mode filtering. *)
let expand_once cat s =
  let buf = Buffer.create (String.length s + 64) in
  let n = String.length s in
  let i = ref 0 in
  let in_math = ref false in
  let math_delim =
    ref
      ' ' (* '$' for $...$, 'D' for $$...$$, '[' for \[...\], '(' for \(...\) *)
  in
  while !i < n do
    let c = s.[!i] in
    (* Math-mode tracking *)
    if c = '$' then
      if !i + 1 < n && s.[!i + 1] = '$' then
        if (* $$ display math toggle *)
           !in_math && !math_delim = 'D' then (
          in_math := false;
          Buffer.add_string buf "$$";
          i := !i + 2)
        else if not !in_math then (
          in_math := true;
          math_delim := 'D';
          Buffer.add_string buf "$$";
          i := !i + 2)
        else (
          Buffer.add_char buf c;
          incr i)
      else if !in_math && !math_delim = '$' then (
        (* Closing inline math $ *)
        in_math := false;
        Buffer.add_char buf c;
        incr i)
      else if not !in_math then (
        (* Opening inline math $ *)
        in_math := true;
        math_delim := '$';
        Buffer.add_char buf c;
        incr i)
      else (
        Buffer.add_char buf c;
        incr i)
    else if c = '\\' then
      let j = take_ident s (!i + 1) in
      if j > !i + 1 then
        let name = String.sub s (!i + 1) (j - (!i + 1)) in
        (* Check for \[, \], \(, \) delimiters *)
        if false then ()
        else
          (* Look up in catalogue *)
          match Hashtbl.find_opt cat.argsafe name with
          | Some e when should_expand_argsafe e ~in_math:!in_math ->
              (* Try to parse argument *)
              let consumed = ref false in
              (if e.positional >= 1 then
                 match find_brace_block s j with
                 | Some (off, len) ->
                     let arg = String.sub s off len in
                     let result =
                       match e.template with
                       | Inline body -> apply_inline_template body arg
                       | Builtin b -> apply_builtin b arg
                     in
                     Buffer.add_string buf result;
                     i := j + len + 2;
                     consumed := true
                 | None -> ());
              if not !consumed then (
                Buffer.add_char buf c;
                incr i)
          | _ -> (
              match Hashtbl.find_opt cat.symbols name with
              | Some e when should_expand_symbol e ~in_math:!in_math ->
                  let expanded =
                    String.concat "" (List.map token_to_string e.expansion)
                  in
                  Buffer.add_string buf expanded;
                  i := j
              | _ ->
                  (* Not in catalogue or mode mismatch: pass through *)
                  Buffer.add_char buf c;
                  incr i)
      else if (* Check for \[ \] \( \) *)
              !i + 1 < n then
        let next = s.[!i + 1] in
        if next = '[' && not !in_math then (
          in_math := true;
          math_delim := '[';
          Buffer.add_string buf "\\[";
          i := !i + 2)
        else if next = ']' && !in_math && !math_delim = '[' then (
          in_math := false;
          Buffer.add_string buf "\\]";
          i := !i + 2)
        else if next = '(' && not !in_math then (
          in_math := true;
          math_delim := '(';
          Buffer.add_string buf "\\(";
          i := !i + 2)
        else if next = ')' && !in_math && !math_delim = '(' then (
          in_math := false;
          Buffer.add_string buf "\\)";
          i := !i + 2)
        else (
          Buffer.add_char buf c;
          incr i)
      else (
        Buffer.add_char buf c;
        incr i)
    else (
      Buffer.add_char buf c;
      incr i)
  done;
  Buffer.contents buf

(** Iterate [expand_once] until fixed point or max iterations reached. *)
let expand cat s =
  let rec loop s n =
    if n >= max_expansions then s
    else
      let s' = expand_once cat s in
      if String.equal s s' then s else loop s' (n + 1)
  in
  loop s 0

(** Expand to fixed point, then tokenise the result. *)
let expand_and_tokenize cat s =
  let expanded = expand cat s in
  let tokens = Tokenizer_lite.tokenize expanded in
  (expanded, tokens)
