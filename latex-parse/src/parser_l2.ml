type cmd = { name : string; opts : string list; args : string list }

type node =
  | Word of string
  | Cmd of cmd
  | Group of node list
  | Environment of { env_name : string; opts : string list; body : node list }
  | MathInline of string
  | MathDisplay of string
  | Comment of string

(* ── Structured document representation ──────────────────────── *)

type doc_section = {
  level : int; (* 0=chapter, 1=section, 2=subsection, etc. *)
  title : string;
  label : string option;
  children : doc_element list;
}

and doc_element =
  | Section of doc_section
  | Paragraph of node list
  | Float of {
      kind : string;
      label : string option;
      caption : string option;
      body : node list;
    }
  | MathBlock of string
  | RawNodes of node list

type document = {
  preamble : node list;
  body : doc_element list;
  labels : (string * int) list; (* label -> position *)
  refs : (string * int) list; (* ref -> position *)
}

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let normalize_ws (s : string) : string =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let rec loop i in_ws =
    if i >= n then ()
    else
      let c = String.unsafe_get s i in
      if c = ' ' || c = '\n' || c = '\t' then (
        if not in_ws then Buffer.add_char b ' ';
        loop (i + 1) true)
      else (
        Buffer.add_char b c;
        loop (i + 1) false)
  in
  loop 0 false;
  (* trim *)
  let out = Buffer.contents b in
  let m = String.length out in
  let a = ref 0 and z = ref (m - 1) in
  while
    !a < m
    &&
    let c = out.[!a] in
    c = ' ' || c = '\n' || c = '\t'
  do
    incr a
  done;
  while
    !z >= !a
    &&
    let c = out.[!z] in
    c = ' ' || c = '\n' || c = '\t'
  do
    decr z
  done;
  if !z < !a then "" else String.sub out !a (!z - !a + 1)

let normalize_punct (s : string) : string =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let is_open = function
    | '(' | '[' | '{' -> true
    | '"' | '\'' -> true
    | _ -> false
  in
  let is_close_punct = function
    | ',' | '.' | ';' | ':' | '!' | '?' | ')' | ']' | '}' | '\'' | '"' -> true
    | _ -> false
  in
  let rec loop i prev =
    if i >= n then ()
    else
      let c = String.unsafe_get s i in
      if c = ' ' then
        let next_c =
          if i + 1 < n then Some (String.unsafe_get s (i + 1)) else None
        in
        match next_c with
        | Some d when is_close_punct d ->
            loop (i + 1) prev (* drop space before punctuation *)
        | _ -> (
            match prev with
            | Some p when is_open p ->
                loop (i + 1) prev (* drop space after opening bracket *)
            | _ ->
                Buffer.add_char b ' ';
                loop (i + 1) (Some ' '))
      else (
        Buffer.add_char b c;
        loop (i + 1) (Some c))
  in
  loop 0 None;
  let out = Buffer.contents b in
  (* trim trailing space *)
  let m = String.length out in
  let z = ref (m - 1) in
  while !z >= 0 && out.[!z] = ' ' do
    decr z
  done;
  if !z < 0 then "" else String.sub out 0 (!z + 1)

let rec parse_word s i n =
  if i < n then
    let c = String.unsafe_get s i in
    if is_letter c then
      let j, w = parse_word s (i + 1) n in
      (j, String.make 1 c ^ w)
    else (i, "")
  else (i, "")

let rec skip_spaces s i n =
  if
    i < n
    &&
    let c = String.unsafe_get s i in
    c = ' ' || c = '\n' || c = '\t'
  then skip_spaces s (i + 1) n
  else i

let rec parse_group s i n =
  let rec loop i acc =
    let i = skip_spaces s i n in
    if i >= n then (i, List.rev acc)
    else
      match String.unsafe_get s i with
      | '}' -> (i + 1, List.rev acc)
      | '{' ->
          let j, g = parse_group s (i + 1) n in
          loop j (Group g :: acc)
      | '\\' ->
          let j = i + 1 in
          let rec name k =
            if k < n && is_letter (String.unsafe_get s k) then name (k + 1)
            else k
          in
          let k = name j in
          if k = j then
            (* Escaped single char e.g. \{ or \] or \\ *)
            if k < n then
              loop (k + 1) (Word (String.make 1 (String.unsafe_get s k)) :: acc)
            else loop k acc
          else
            let name_str = String.sub s j (k - j) in
            let k = skip_spaces s k n in
            (* \verb and \verb* passthrough (epsilon-safe): next char is
               delimiter, read until next delimiter (escape-aware) *)
            if name_str = "verb" then
              let star = k < n && String.unsafe_get s k = '*' in
              let k = if star then k + 1 else k in
              if k < n then (
                let delim = String.unsafe_get s k in
                let j = ref (k + 1) in
                let buf = Buffer.create 16 in
                let rec scan () =
                  if !j >= n then ()
                  else
                    let c = String.unsafe_get s !j in
                    if c = '\\' && !j + 1 < n then (
                      Buffer.add_char buf c;
                      incr j;
                      Buffer.add_char buf (String.unsafe_get s !j);
                      incr j;
                      scan ())
                    else if c = delim then incr j
                    else (
                      Buffer.add_char buf c;
                      incr j;
                      scan ())
                in
                scan ();
                let opt_star = if star then [ "*" ] else [] in
                loop !j
                  (Cmd
                     {
                       name = name_str;
                       opts = opt_star;
                       args = [ Buffer.contents buf ];
                     }
                  :: acc))
              else loop k acc
            else
              (* collect zero or more [opt] args (non-nested, escape-aware) *)
              let rec collect_opts k acc =
                if k < n && String.unsafe_get s k = '[' then (
                  let j = ref (k + 1) in
                  let buf = Buffer.create 16 in
                  let rec scan () =
                    if !j >= n then ()
                    else
                      let c = String.unsafe_get s !j in
                      if c = '\\' && !j + 1 < n then (
                        Buffer.add_char buf c;
                        incr j;
                        Buffer.add_char buf (String.unsafe_get s !j);
                        incr j;
                        scan ())
                      else if c = ']' then incr j
                      else (
                        Buffer.add_char buf c;
                        incr j;
                        scan ())
                  in
                  scan ();
                  let opt = Buffer.contents buf in
                  collect_opts !j (opt :: acc))
                else (k, List.rev acc)
              in
              let k, opts = collect_opts k [] in
              let k = skip_spaces s k n in
              (* collect zero or more {arg} (nested groups) *)
              let rec collect_args k acc =
                if k < n && String.unsafe_get s k = '{' then
                  let k', g = parse_group s (k + 1) n in
                  collect_args k' (serialize g :: acc)
                else (k, List.rev acc)
              in
              let k, args = collect_args k [] in
              loop k (Cmd { name = name_str; opts; args } :: acc)
      | c ->
          let j, _w = parse_word s i n in
          if j > i then loop j (Word (String.sub s i (j - i)) :: acc)
          else loop (i + 1) (Word (String.make 1 c) :: acc)
  and serialize nodes =
    let buf = Buffer.create 32 in
    let rec go = function
      | [] -> ()
      | Word w :: xs ->
          Buffer.add_string buf w;
          go xs
      | Cmd c :: xs ->
          Buffer.add_char buf '\\';
          Buffer.add_string buf c.name;
          List.iter
            (fun o ->
              Buffer.add_char buf '[';
              Buffer.add_string buf o;
              Buffer.add_char buf ']')
            c.opts;
          List.iter
            (fun a ->
              Buffer.add_char buf '{';
              Buffer.add_string buf a;
              Buffer.add_char buf '}')
            c.args;
          go xs
      | Group g :: xs ->
          Buffer.add_char buf '{';
          List.iter
            (fun n ->
              match n with Word w -> Buffer.add_string buf w | _ -> ())
            g;
          Buffer.add_char buf '}';
          go xs
      | Environment { env_name; body; _ } :: xs ->
          Buffer.add_string buf ("\\begin{" ^ env_name ^ "}");
          go body;
          Buffer.add_string buf ("\\end{" ^ env_name ^ "}");
          go xs
      | MathInline s :: xs ->
          Buffer.add_char buf '$';
          Buffer.add_string buf s;
          Buffer.add_char buf '$';
          go xs
      | MathDisplay s :: xs ->
          Buffer.add_string buf "\\[";
          Buffer.add_string buf s;
          Buffer.add_string buf "\\]";
          go xs
      | Comment s :: xs ->
          Buffer.add_char buf '%';
          Buffer.add_string buf s;
          go xs
    in
    go nodes;
    Buffer.contents buf
  in
  loop i []

(* ── Environment-aware parsing ────────────────────────────────── *)

let parse_with_envs (s : string) : node list =
  let n = String.length s in
  let _, raw_nodes = parse_group ("{" ^ s ^ "}") 1 (n + 2) in
  (* Post-process: match \begin{env}...\end{env} pairs *)
  let rec process = function
    | [] -> []
    | Cmd { name = "begin"; args = env_name :: _; opts; _ } :: rest ->
        let body, remaining = collect_env_body env_name rest in
        Environment { env_name; opts; body = process body } :: process remaining
    | node :: rest -> node :: process rest
  and collect_env_body env_name nodes =
    let rec loop acc = function
      | [] -> (List.rev acc, [])
      | Cmd { name = "end"; args = en :: _; _ } :: rest when en = env_name ->
          (List.rev acc, rest)
      | Cmd { name = "begin"; args = inner :: _; opts; _ } :: rest ->
          let inner_body, after_inner = collect_env_body inner rest in
          let env_node =
            Environment { env_name = inner; opts; body = process inner_body }
          in
          loop (env_node :: acc) after_inner
      | node :: rest -> loop (node :: acc) rest
    in
    loop [] nodes
  in
  process raw_nodes

(* ── Document structure extraction ──────────────────────────── *)

let section_level name =
  match name with
  | "chapter" -> Some 0
  | "section" -> Some 1
  | "subsection" -> Some 2
  | "subsubsection" -> Some 3
  | "paragraph" -> Some 4
  | _ -> None

let extract_document (nodes : node list) : document =
  let preamble = ref [] in
  let body_nodes = ref [] in
  let in_body = ref false in
  let labels = ref [] in
  let refs = ref [] in
  let pos = ref 0 in
  let rec scan = function
    | [] -> ()
    | Environment { env_name = "document"; body; _ } :: rest ->
        in_body := true;
        body_nodes := body;
        scan rest
    | Cmd { name = "label"; args = lbl :: _; _ } :: rest ->
        labels := (lbl, !pos) :: !labels;
        incr pos;
        if not !in_body then
          preamble :=
            Cmd { name = "label"; args = [ lbl ]; opts = [] } :: !preamble;
        scan rest
    | Cmd { name; args = r :: _; _ } :: rest
      when name = "ref" || name = "eqref" || name = "autoref" || name = "cref"
      ->
        refs := (r, !pos) :: !refs;
        incr pos;
        scan rest
    | node :: rest ->
        incr pos;
        if not !in_body then preamble := node :: !preamble;
        scan rest
  in
  scan nodes;
  (* Build doc_elements from body nodes *)
  let elements =
    List.map
      (fun node ->
        match node with
        | Environment { env_name; body; _ }
          when env_name = "figure"
               || env_name = "figure*"
               || env_name = "table"
               || env_name = "table*" ->
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
            Float { kind = env_name; label; caption; body }
        | Cmd c -> (
            match section_level c.name with
            | Some level ->
                let title = match c.args with t :: _ -> t | [] -> "" in
                Section { level; title; label = None; children = [] }
            | None -> RawNodes [ Cmd c ])
        | Environment { env_name; body = _; _ }
          when env_name = "equation"
               || env_name = "equation*"
               || env_name = "align"
               || env_name = "align*" ->
            MathBlock env_name
        | _ -> RawNodes [ node ])
      !body_nodes
  in
  {
    preamble = List.rev !preamble;
    body = elements;
    labels = List.rev !labels;
    refs = List.rev !refs;
  }

(* ── Parse success metric ───────────────────────────────────── *)

let parse_success (s : string) : bool =
  try
    let nodes = parse_with_envs s in
    (* Success if we got at least 1 node and no unparsed remainder *)
    List.length nodes > 0
  with _ -> false

let parse s =
  let n = String.length s in
  let _, nodes = parse_group ("{" ^ s ^ "}") 1 (n + 2) in
  nodes

let serialize (nodes : node list) : string =
  let b = Buffer.create 64 in
  let rec go = function
    | [] -> ()
    | Word w :: xs ->
        Buffer.add_string b w;
        Buffer.add_char b ' ';
        go xs
    | Cmd c :: xs ->
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
        go xs
    | Group g :: xs ->
        Buffer.add_char b '{';
        go g;
        Buffer.add_char b '}';
        Buffer.add_char b ' ';
        go xs
    | Environment { env_name; body; _ } :: xs ->
        Buffer.add_string b ("\\begin{" ^ env_name ^ "} ");
        go body;
        Buffer.add_string b ("\\end{" ^ env_name ^ "} ");
        go xs
    | MathInline s :: xs ->
        Buffer.add_char b '$';
        Buffer.add_string b s;
        Buffer.add_string b "$ ";
        go xs
    | MathDisplay s :: xs ->
        Buffer.add_string b "\\[";
        Buffer.add_string b s;
        Buffer.add_string b "\\] ";
        go xs
    | Comment s :: xs ->
        Buffer.add_char b '%';
        Buffer.add_string b s;
        Buffer.add_char b ' ';
        go xs
  in
  go nodes;
  normalize_punct (normalize_ws (Buffer.contents b))
