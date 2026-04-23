(* ══════════════════════════════════════════════════════════════════════
   Parser_l2 — comprehensive LaTeX parser (spec §4, W40-52)

   PEG-style recursive descent parser producing a located AST. Features: -
   Location tracking (line, column) on every node - Environment parsing
   (\begin{env}...\end{env}) - Math mode ($...$, \(...\), \[...\], equation,
   align, etc.) - Comment handling (% to end of line) - Verbatim environments
   (lstlisting, minted, verbatim — opaque) - Document structure (preamble/body,
   sections, floats, labels, refs) - Error recovery (continues on malformed
   input) - Dirty region tracking for incremental re-parse
   ══════════════════════════════════════════════════════════════════════ *)

(* ── Location tracking ──────────────────────────────────────── *)

type loc = { line : int; col : int; offset : int; end_offset : int }

let _loc0 = { line = 1; col = 0; offset = 0; end_offset = 0 }

(* ── AST node types ─────────────────────────────────────────── *)

type cmd = { name : string; opts : string list; args : string list }

type node =
  | Word of string
  | Cmd of cmd
  | Group of node list
  | Environment of { env_name : string; opts : string list; body : node list }
  | MathInline of string (* $...$ or \(...\) *)
  | MathDisplay of string (* $$...$$ or \[...\] or equation env *)
  | Comment of string (* % to EOL *)
  | Verbatim of { env_name : string; content : string } (* opaque block *)
  | Whitespace of string
  | Newline
  | Error of { message : string; position : int }

type located_node = { node : node; loc : loc }

(* ── Document structure ─────────────────────────────────────── *)

type doc_section = {
  level : int; (* 0=chapter, 1=section, 2=subsection, etc. *)
  title : string;
  label : string option;
  children : doc_element list;
}

and doc_element =
  | Section of doc_section
  | Paragraph of located_node list
  | Float of {
      kind : string;
      label : string option;
      caption : string option;
      body : located_node list;
    }
  | MathBlock of { env_name : string; content : string }
  | RawNodes of located_node list

type document = {
  preamble : located_node list;
  body : doc_element list;
  labels : (string * loc) list;
  refs : (string * loc) list;
  errors : (string * loc) list;
  packages : (string * string option * loc) list;
  documentclass : (string * string option) option;
}

(* ── Parser state ───────────────────────────────────────────── *)

type parse_state = {
  src : string;
  len : int;
  mutable pos : int;
  mutable line : int;
  mutable col : int;
  mutable errors : (string * loc) list;
}

let make_state (src : string) : parse_state =
  { src; len = String.length src; pos = 0; line = 1; col = 0; errors = [] }

let current_loc (st : parse_state) : loc =
  { line = st.line; col = st.col; offset = st.pos; end_offset = st.pos }

(** Close [loc] to the parser's current position. Called at each emission site
    so [end_offset] reflects the actual end of the node. *)
let close_loc (loc : loc) (st : parse_state) : loc =
  { loc with end_offset = st.pos }

let peek (st : parse_state) : char option =
  if st.pos < st.len then Some (String.unsafe_get st.src st.pos) else None

let advance (st : parse_state) : unit =
  if st.pos < st.len then (
    if String.unsafe_get st.src st.pos = '\n' then (
      st.line <- st.line + 1;
      st.col <- 0)
    else st.col <- st.col + 1;
    st.pos <- st.pos + 1)

let advance_n (st : parse_state) (n : int) : unit =
  for _ = 1 to n do
    advance st
  done

let starts_with (st : parse_state) (prefix : string) : bool =
  let plen = String.length prefix in
  st.pos + plen <= st.len && String.sub st.src st.pos plen = prefix

let record_error (st : parse_state) (msg : string) : unit =
  st.errors <- (msg, current_loc st) :: st.errors

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

(* ── Verbatim environments (opaque) ─────────────────────────── *)

let verbatim_envs =
  [ "verbatim"; "lstlisting"; "minted"; "Verbatim"; "tikzpicture" ]

let is_verbatim_env name = List.mem name verbatim_envs

(* ── Math environment names ─────────────────────────────────── *)

let math_envs =
  [
    "equation";
    "equation*";
    "align";
    "align*";
    "gather";
    "gather*";
    "multline";
    "multline*";
    "eqnarray";
    "eqnarray*";
    "math";
    "displaymath";
    "flalign";
    "flalign*";
    (* amsmath inner-math environments *)
    "split";
    "cases";
    "matrix";
    "pmatrix";
    "bmatrix";
    "Bmatrix";
    "vmatrix";
    "Vmatrix";
    "smallmatrix";
    "aligned";
    "alignedat";
    "gathered";
  ]

let is_math_env name = List.mem name math_envs

(* ── Comment parsing ────────────────────────────────────────── *)

let parse_comment (st : parse_state) : located_node =
  let loc = current_loc st in
  advance st;
  (* skip % *)
  let start = st.pos in
  while st.pos < st.len && String.unsafe_get st.src st.pos <> '\n' do
    advance st
  done;
  let text = String.sub st.src start (st.pos - start) in
  { node = Comment text; loc = close_loc loc st }

(* ── Math mode parsing ──────────────────────────────────────── *)

let parse_inline_math (st : parse_state) : located_node =
  let loc = current_loc st in
  advance st;
  (* skip opening $ *)
  let buf = Buffer.create 64 in
  let found_close = ref false in
  while st.pos < st.len && not !found_close do
    let c = String.unsafe_get st.src st.pos in
    if c = '$' then (
      found_close := true;
      advance st)
    else if c = '\\' && st.pos + 1 < st.len then (
      Buffer.add_char buf c;
      advance st;
      Buffer.add_char buf (String.unsafe_get st.src st.pos);
      advance st)
    else (
      Buffer.add_char buf c;
      advance st)
  done;
  if not !found_close then record_error st "Unclosed inline math $";
  { node = MathInline (Buffer.contents buf); loc = close_loc loc st }

let parse_display_math_bracket (st : parse_state) : located_node =
  let loc = current_loc st in
  advance_n st 2;
  (* skip \[ *)
  let buf = Buffer.create 64 in
  let found_close = ref false in
  while st.pos < st.len && not !found_close do
    if starts_with st "\\]" then (
      found_close := true;
      advance_n st 2)
    else (
      Buffer.add_char buf (String.unsafe_get st.src st.pos);
      advance st)
  done;
  if not !found_close then record_error st "Unclosed display math \\[";
  { node = MathDisplay (Buffer.contents buf); loc = close_loc loc st }

let parse_paren_math (st : parse_state) : located_node =
  let loc = current_loc st in
  advance_n st 2;
  (* skip \( *)
  let buf = Buffer.create 64 in
  let found_close = ref false in
  while st.pos < st.len && not !found_close do
    if starts_with st "\\)" then (
      found_close := true;
      advance_n st 2)
    else (
      Buffer.add_char buf (String.unsafe_get st.src st.pos);
      advance st)
  done;
  if not !found_close then record_error st "Unclosed paren math \\(";
  { node = MathInline (Buffer.contents buf); loc = close_loc loc st }

(* ── Environment body parsing ───────────────────────────────── *)

let parse_env_body (st : parse_state) (env_name : string) : string =
  let end_tag = "\\end{" ^ env_name ^ "}" in
  let elen = String.length end_tag in
  let buf = Buffer.create 256 in
  let found = ref false in
  while st.pos < st.len && not !found do
    if starts_with st end_tag then (
      found := true;
      advance_n st elen)
    else (
      Buffer.add_char buf (String.unsafe_get st.src st.pos);
      advance st)
  done;
  if not !found then record_error st ("Unclosed environment: " ^ env_name);
  Buffer.contents buf

(* ── Command name parsing ───────────────────────────────────── *)

let parse_cmd_name (st : parse_state) : string =
  let start = st.pos in
  while st.pos < st.len && is_letter (String.unsafe_get st.src st.pos) do
    advance st
  done;
  if st.pos > start then
    (* Check for starred variant: \section* etc. *)
    let name = String.sub st.src start (st.pos - start) in
    if st.pos < st.len && String.unsafe_get st.src st.pos = '*' then (
      advance st;
      name ^ "*")
    else name
  else if st.pos < st.len then (
    let c = String.unsafe_get st.src st.pos in
    advance st;
    String.make 1 c)
  else ""

(* ── Optional argument [..] parsing ─────────────────────────── *)

let parse_opt_arg (st : parse_state) : string option =
  if st.pos < st.len && String.unsafe_get st.src st.pos = '[' then (
    advance st;
    let buf = Buffer.create 32 in
    let depth = ref 1 in
    while st.pos < st.len && !depth > 0 do
      let c = String.unsafe_get st.src st.pos in
      if c = '[' then incr depth else if c = ']' then decr depth;
      if !depth > 0 then Buffer.add_char buf c;
      advance st
    done;
    Some (Buffer.contents buf))
  else None

(* ── Brace argument {...} parsing ───────────────────────────── *)

let parse_brace_arg (st : parse_state) : string option =
  (* skip whitespace *)
  while
    st.pos < st.len
    &&
    let c = String.unsafe_get st.src st.pos in
    c = ' ' || c = '\t' || c = '\n'
  do
    advance st
  done;
  if st.pos < st.len && String.unsafe_get st.src st.pos = '{' then (
    advance st;
    let buf = Buffer.create 32 in
    let depth = ref 1 in
    while st.pos < st.len && !depth > 0 do
      let c = String.unsafe_get st.src st.pos in
      if c = '{' then incr depth else if c = '}' then decr depth;
      if !depth > 0 then Buffer.add_char buf c;
      advance st
    done;
    Some (Buffer.contents buf))
  else None

(* ── Main recursive parser ──────────────────────────────────── *)

let max_nesting_depth = 500

let rec parse_nodes ?(depth = 0) (st : parse_state)
    (stop_at_end : string option) : located_node list =
  if depth > max_nesting_depth then (
    record_error st
      (Printf.sprintf "Maximum nesting depth %d exceeded" max_nesting_depth);
    [])
  else
    let nodes = ref [] in
    let running = ref true in
    while st.pos < st.len && !running do
      let loc = current_loc st in
      match peek st with
      | None -> running := false
      | Some '%' ->
          let n = parse_comment st in
          nodes := n :: !nodes
      | Some '$' ->
          if st.pos + 1 < st.len && String.unsafe_get st.src (st.pos + 1) = '$'
          then (
            (* Display math $$ *)
            advance_n st 2;
            let buf = Buffer.create 64 in
            let found = ref false in
            while st.pos < st.len && not !found do
              if
                st.pos + 1 < st.len
                && String.unsafe_get st.src st.pos = '$'
                && String.unsafe_get st.src (st.pos + 1) = '$'
              then (
                found := true;
                advance_n st 2)
              else (
                Buffer.add_char buf (String.unsafe_get st.src st.pos);
                advance st)
            done;
            nodes :=
              {
                node = MathDisplay (Buffer.contents buf);
                loc = close_loc loc st;
              }
              :: !nodes)
          else
            let n = parse_inline_math st in
            nodes := n :: !nodes
      | Some '\\' ->
          if starts_with st "\\[" then
            let n = parse_display_math_bracket st in
            nodes := n :: !nodes
          else if starts_with st "\\(" then
            let n = parse_paren_math st in
            nodes := n :: !nodes
          else if starts_with st "\\begin{" then (
            advance_n st 7;
            (* skip \begin{ *)
            let name_start = st.pos in
            while st.pos < st.len && String.unsafe_get st.src st.pos <> '}' do
              advance st
            done;
            let env_name = String.sub st.src name_start (st.pos - name_start) in
            if st.pos < st.len then advance st;
            (* skip } *)
            if is_verbatim_env env_name then
              (* Parse verbatim content as opaque string *)
              let content = parse_env_body st env_name in
              nodes :=
                {
                  node = Verbatim { env_name; content };
                  loc = close_loc loc st;
                }
                :: !nodes
            else if is_math_env env_name then
              let content = parse_env_body st env_name in
              nodes :=
                { node = MathDisplay content; loc = close_loc loc st } :: !nodes
            else
              (* Parse environment body recursively *)
              let body_lnodes =
                parse_nodes ~depth:(depth + 1) st (Some env_name)
              in
              let body = List.map (fun ln -> ln.node) body_lnodes in
              nodes :=
                {
                  node = Environment { env_name; opts = []; body };
                  loc = close_loc loc st;
                }
                :: !nodes)
          else if starts_with st "\\end{" then (
            advance_n st 5;
            let name_start = st.pos in
            while st.pos < st.len && String.unsafe_get st.src st.pos <> '}' do
              advance st
            done;
            let env_name = String.sub st.src name_start (st.pos - name_start) in
            if st.pos < st.len then advance st;
            match stop_at_end with
            | Some expected when expected = env_name -> running := false
            | Some expected ->
                record_error st
                  ("Expected \\end{"
                  ^ expected
                  ^ "} but got \\end{"
                  ^ env_name
                  ^ "}");
                running := false
            | None -> record_error st ("Unexpected \\end{" ^ env_name ^ "}"))
          else (
            advance st;
            (* skip \ *)
            let name = parse_cmd_name st in
            if name = "" then
              nodes := { node = Word "\\"; loc = close_loc loc st } :: !nodes
            else if name = "verb" || name = "verb*" then
              if
                (* \verb|...| — arbitrary delimiter, opaque content *)
                st.pos < st.len
              then (
                let delim = String.unsafe_get st.src st.pos in
                advance st;
                let buf = Buffer.create 64 in
                let found_close = ref false in
                while st.pos < st.len && not !found_close do
                  let c = String.unsafe_get st.src st.pos in
                  if c = delim then (
                    found_close := true;
                    advance st)
                  else (
                    Buffer.add_char buf c;
                    advance st)
                done;
                if not !found_close then record_error st "Unclosed \\verb";
                nodes :=
                  {
                    node =
                      Verbatim
                        { env_name = name; content = Buffer.contents buf };
                    loc = close_loc loc st;
                  }
                  :: !nodes)
              else record_error st "\\verb at end of input"
            else
              let opts = ref [] in
              let more_opts = ref true in
              while !more_opts do
                match parse_opt_arg st with
                | Some o -> opts := o :: !opts
                | None -> more_opts := false
              done;
              let args = ref [] in
              let more_args = ref true in
              while !more_args do
                match parse_brace_arg st with
                | Some a -> args := a :: !args
                | None -> more_args := false
              done;
              nodes :=
                {
                  node =
                    Cmd { name; opts = List.rev !opts; args = List.rev !args };
                  loc = close_loc loc st;
                }
                :: !nodes)
      | Some '{' ->
          advance st;
          let inner = parse_nodes ~depth:(depth + 1) st None in
          (* Find closing } *)
          (* The recursive call should have consumed up to } *)
          nodes :=
            {
              node = Group (List.map (fun n -> n.node) inner);
              loc = close_loc loc st;
            }
            :: !nodes
      | Some '}' -> (
          advance st;
          match stop_at_end with
          | None -> running := false (* closing a group *)
          | Some _ -> running := false)
      | Some '\n' ->
          advance st;
          nodes := { node = Newline; loc = close_loc loc st } :: !nodes
      | Some c when c = ' ' || c = '\t' ->
          let start = st.pos in
          while
            st.pos < st.len
            &&
            let c = String.unsafe_get st.src st.pos in
            c = ' ' || c = '\t'
          do
            advance st
          done;
          nodes :=
            {
              node = Whitespace (String.sub st.src start (st.pos - start));
              loc = close_loc loc st;
            }
            :: !nodes
      | Some _ ->
          let start = st.pos in
          while
            st.pos < st.len
            &&
            let c = String.unsafe_get st.src st.pos in
            c <> '\\'
            && c <> '{'
            && c <> '}'
            && c <> '$'
            && c <> '%'
            && c <> '\n'
            && c <> ' '
            && c <> '\t'
          do
            advance st
          done;
          if st.pos > start then
            nodes :=
              {
                node = Word (String.sub st.src start (st.pos - start));
                loc = close_loc loc st;
              }
              :: !nodes
    done;
    List.rev !nodes

(* ── Public parse API ───────────────────────────────────────── *)

let parse_located (s : string) : located_node list * (string * loc) list =
  let st = make_state s in
  let nodes = parse_nodes st None in
  (nodes, List.rev st.errors)

let parse (s : string) : node list =
  let nodes, _errors = parse_located s in
  List.map (fun ln -> ln.node) nodes

let parse_with_envs (s : string) : node list = parse s

(* ── Document structure extraction ──────────────────────────── *)

let section_level name =
  match name with
  | "part" | "part*" -> Some (-1)
  | "chapter" | "chapter*" -> Some 0
  | "section" | "section*" -> Some 1
  | "subsection" | "subsection*" -> Some 2
  | "subsubsection" | "subsubsection*" -> Some 3
  | "paragraph" | "paragraph*" -> Some 4
  | "subparagraph" | "subparagraph*" -> Some 5
  | _ -> None

let is_float_env name =
  name = "figure"
  || name = "figure*"
  || name = "table"
  || name = "table*"
  || name = "algorithm"
  || name = "algorithm*"

let extract_document (s : string) : document =
  let nodes, errors = parse_located s in
  let preamble = ref [] in
  let body_nodes = ref [] in
  let in_body = ref false in
  let labels = ref [] in
  let refs = ref [] in
  let packages = ref [] in
  let docclass = ref None in
  List.iter
    (fun ln ->
      (match ln.node with
      | Environment { env_name = "document"; body; _ } ->
          in_body := true;
          body_nodes := List.map (fun n -> { node = n; loc = ln.loc }) body
      | Cmd { name = "label"; args = lbl :: _; _ } ->
          labels := (lbl, ln.loc) :: !labels
      | Cmd { name; args = r :: _; _ }
        when name = "ref"
             || name = "eqref"
             || name = "autoref"
             || name = "cref"
             || name = "Cref"
             || name = "pageref"
             || name = "nameref"
             || name = "href" ->
          refs := (r, ln.loc) :: !refs
      | Cmd { name = "usepackage"; args; opts; _ } ->
          let opt_str = match opts with o :: _ -> Some o | [] -> None in
          List.iter
            (fun pkg_str ->
              let pkgs =
                String.split_on_char ',' pkg_str
                |> List.map String.trim
                |> List.filter (fun s -> String.length s > 0)
              in
              List.iter
                (fun pkg -> packages := (pkg, opt_str, ln.loc) :: !packages)
                pkgs)
            args
      | Cmd { name = "documentclass"; args; opts; _ } ->
          let cls = match args with c :: _ -> c | [] -> "" in
          let opt_str = match opts with o :: _ -> Some o | [] -> None in
          docclass := Some (cls, opt_str)
      | Cmd { name = "bibliography"; args = bib :: _; _ } ->
          (* Track bibliography files as package-like metadata *)
          packages := (bib, Some "bibliography", ln.loc) :: !packages
      | Cmd { name = "bibliographystyle"; args = sty :: _; _ } ->
          packages := (sty, Some "bibliographystyle", ln.loc) :: !packages
      | _ -> ());
      if not !in_body then preamble := ln :: !preamble)
    nodes;
  (* Also scan body nodes for labels/refs (they are children of the document
     env) *)
  List.iter
    (fun ln ->
      match ln.node with
      | Cmd { name = "label"; args = lbl :: _; _ } ->
          labels := (lbl, ln.loc) :: !labels
      | Cmd { name; args = r :: _; _ }
        when name = "ref"
             || name = "eqref"
             || name = "autoref"
             || name = "cref"
             || name = "Cref"
             || name = "pageref"
             || name = "nameref"
             || name = "href" ->
          refs := (r, ln.loc) :: !refs
      | _ -> ())
    !body_nodes;
  let elements =
    List.map
      (fun ln ->
        match ln.node with
        | Environment { env_name; body; _ } when is_float_env env_name ->
            let caption =
              List.find_map
                (function
                  | Cmd { name = "caption"; args = c :: _; _ } -> Some c
                  | _ -> None)
                body
            in
            let label =
              List.find_map
                (function
                  | Cmd { name = "label"; args = l :: _; _ } -> Some l
                  | _ -> None)
                body
            in
            Float { kind = env_name; label; caption; body = [ ln ] }
        | Cmd c -> (
            match section_level c.name with
            | Some level ->
                let title = match c.args with t :: _ -> t | [] -> "" in
                Section { level; title; label = None; children = [] }
            | None -> RawNodes [ ln ])
        | MathDisplay content -> MathBlock { env_name = "display"; content }
        | _ -> RawNodes [ ln ])
      !body_nodes
  in
  {
    preamble = List.rev !preamble;
    body = elements;
    labels = List.rev !labels;
    refs = List.rev !refs;
    errors;
    packages = List.rev !packages;
    documentclass = !docclass;
  }

(* ── Parse success metric ───────────────────────────────────── *)

let parse_success (s : string) : bool =
  let _nodes, errors = parse_located s in
  errors = []

(* ── Dirty region tracking for incremental re-parse ─────────── *)

type dirty_region = { dr_start : int; dr_end : int }

let find_dirty_region (old_src : string) (new_src : string) : dirty_region =
  let old_len = String.length old_src in
  let new_len = String.length new_src in
  let min_len = min old_len new_len in
  (* Find first differing position *)
  let start = ref 0 in
  while !start < min_len && old_src.[!start] = new_src.[!start] do
    incr start
  done;
  (* Find last differing position from the end *)
  let old_end = ref (old_len - 1) in
  let new_end = ref (new_len - 1) in
  while
    !old_end >= !start
    && !new_end >= !start
    && old_src.[!old_end] = new_src.[!new_end]
  do
    decr old_end;
    decr new_end
  done;
  { dr_start = !start; dr_end = !new_end + 1 }

(* ── Legacy API compatibility ───────────────────────────────── *)

let normalize_ws (s : string) : string =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let in_ws = ref false in
  for i = 0 to n - 1 do
    let c = String.unsafe_get s i in
    if c = ' ' || c = '\n' || c = '\t' then (
      if not !in_ws then Buffer.add_char b ' ';
      in_ws := true)
    else (
      Buffer.add_char b c;
      in_ws := false)
  done;
  String.trim (Buffer.contents b)

let normalize_punct (s : string) : string =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let is_close_punct = function
    | ',' | '.' | ';' | ':' | '!' | '?' | ')' | ']' | '}' -> true
    | _ -> false
  in
  let is_open = function '(' | '[' | '{' -> true | _ -> false in
  let prev = ref None in
  for i = 0 to n - 1 do
    let c = String.unsafe_get s i in
    if c = ' ' then (
      let skip =
        (i + 1 < n && is_close_punct (String.unsafe_get s (i + 1)))
        || match !prev with Some p -> is_open p | None -> false
      in
      if not skip then Buffer.add_char b ' ')
    else Buffer.add_char b c;
    prev := Some c
  done;
  String.trim (Buffer.contents b)

let serialize (nodes : node list) : string =
  let b = Buffer.create 256 in
  let rec go = function
    | [] -> ()
    | Word w :: rest ->
        Buffer.add_string b w;
        Buffer.add_char b ' ';
        go rest
    | Cmd c :: rest ->
        Buffer.add_char b '\\';
        Buffer.add_string b c.name;
        List.iter
          (fun o ->
            Buffer.add_char b '[';
            Buffer.add_string b o;
            Buffer.add_char b ']')
          c.opts;
        List.iter
          (fun a ->
            Buffer.add_char b '{';
            Buffer.add_string b a;
            Buffer.add_char b '}')
          c.args;
        Buffer.add_char b ' ';
        go rest
    | Group g :: rest ->
        Buffer.add_char b '{';
        go g;
        Buffer.add_string b "} ";
        go rest
    | Environment { env_name; body; _ } :: rest ->
        Buffer.add_string b ("\\begin{" ^ env_name ^ "} ");
        go body;
        Buffer.add_string b ("\\end{" ^ env_name ^ "} ");
        go rest
    | MathInline s :: rest ->
        Buffer.add_char b '$';
        Buffer.add_string b s;
        Buffer.add_string b "$ ";
        go rest
    | MathDisplay s :: rest ->
        Buffer.add_string b "\\[";
        Buffer.add_string b s;
        Buffer.add_string b "\\] ";
        go rest
    | Comment s :: rest ->
        Buffer.add_char b '%';
        Buffer.add_string b s;
        Buffer.add_char b '\n';
        go rest
    | Verbatim { env_name; content } :: rest ->
        Buffer.add_string b ("\\begin{" ^ env_name ^ "}");
        Buffer.add_string b content;
        Buffer.add_string b ("\\end{" ^ env_name ^ "} ");
        go rest
    | Whitespace s :: rest ->
        Buffer.add_string b s;
        go rest
    | Newline :: rest ->
        Buffer.add_char b '\n';
        go rest
    | Error { message; _ } :: rest ->
        Buffer.add_string b ("(* ERROR: " ^ message ^ " *)");
        go rest
  in
  go nodes;
  normalize_punct (normalize_ws (Buffer.contents b))
