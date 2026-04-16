(* ══════════════════════════════════════════════════════════════════════
   User_macro_registry — parse, classify, and track user-defined commands

   Parses \newcommand, \renewcommand, and \providecommand from LaTeX source.
   Classifies each as supported (safe for expansion) or unsupported (diagnosed
   with reason). Builds def-use dependency graph and detects cycles via DFS
   topological sort.
   ══════════════════════════════════════════════════════════════════════ *)

type macro_kind = Newcommand | Renewcommand | Providecommand

type user_macro_def = {
  kind : macro_kind;
  name : string;
  arity : int;
  opt_default : string option;
  body : string;
  loc : int;
}

type support_status = Supported | Unsupported of string
type classified_def = { def : user_macro_def; status : support_status }
type dep_edge = { from_name : string; to_name : string }

type registry = {
  defs : classified_def list;
  edges : dep_edge list;
  has_cycle : bool;
  cycle_path : string list;
  supported_count : int;
  unsupported_count : int;
}

(* ── Helpers ─────────────────────────────────────────────────────── *)

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

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

let skip_ws s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\n') do
    incr j
  done;
  !j

let take_ident s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && is_letter s.[!j] do
    incr j
  done;
  if !j > i then Some (String.sub s i (!j - i), !j) else None

(* ── Parsing ─────────────────────────────────────────────────────── *)

let re_def =
  Re_compat.regexp {|\\\(newcommand\|renewcommand\|providecommand\)\*?|}

let kind_of_string = function
  | "newcommand" -> Newcommand
  | "renewcommand" -> Renewcommand
  | "providecommand" -> Providecommand
  | _ -> Newcommand

let parse_definitions (src : string) : user_macro_def list =
  let defs = ref [] in
  let i = ref 0 in
  let n = String.length src in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re_def src !i in
       let kind_str = Re_compat.matched_group _mr 1 src in
       let kind = kind_of_string kind_str in
       let loc = pos in
       let after_cmd = Re_compat.match_end _mr in
       (* Skip optional * and whitespace *)
       let p = ref after_cmd in
       p := skip_ws src !p;
       (* Extract macro name: either {\name} or \name *)
       let name_opt =
         if !p < n && src.[!p] = '{' then
           (* {\name} form *)
           let inside = !p + 1 in
           if inside < n && src.[inside] = '\\' then
             match take_ident src (inside + 1) with
             | Some (name, after_name) ->
                 (* skip closing brace *)
                 let q = ref after_name in
                 q := skip_ws src !q;
                 if !q < n && src.[!q] = '}' then (
                   p := !q + 1;
                   Some name)
                 else None
             | None -> None
           else None
         else if !p < n && src.[!p] = '\\' then
           (* \name form (no braces) *)
           match take_ident src (!p + 1) with
           | Some (name, after_name) ->
               p := after_name;
               Some name
           | None -> None
         else None
       in
       (match name_opt with
       | None -> i := after_cmd
       | Some name -> (
           p := skip_ws src !p;
           (* Optional arity [N] *)
           let arity =
             if !p < n && src.[!p] = '[' then (
               let q = ref (!p + 1) in
               while !q < n && src.[!q] <> ']' do
                 incr q
               done;
               if !q < n then (
                 let arity_str = String.sub src (!p + 1) (!q - !p - 1) in
                 p := !q + 1;
                 try int_of_string (String.trim arity_str) with Failure _ -> 0)
               else 0)
             else 0
           in
           p := skip_ws src !p;
           (* Optional default [default] *)
           let opt_default =
             if !p < n && src.[!p] = '[' then (
               let q = ref (!p + 1) in
               let depth = ref 1 in
               while !q < n && !depth > 0 do
                 (match src.[!q] with
                 | '[' -> incr depth
                 | ']' -> decr depth
                 | _ -> ());
                 if !depth > 0 then incr q
               done;
               if !depth = 0 then (
                 let def_str = String.sub src (!p + 1) (!q - !p - 1) in
                 p := !q + 1;
                 Some def_str)
               else None)
             else None
           in
           p := skip_ws src !p;
           (* Body {....} *)
           match find_brace_block src !p with
           | Some (start, len) ->
               let body = String.sub src start len in
               defs := { kind; name; arity; opt_default; body; loc } :: !defs;
               i := start + len + 1
           | None -> i := !p + 1));
       i := max !i (pos + 1)
     done
   with Not_found -> ());
  List.rev !defs

(* ── Classification ──────────────────────────────────────────────── *)

let _blocklist =
  [
    ("\\catcode", "body contains \\catcode");
    ("\\makeatletter", "body contains \\makeatletter");
    ("\\def", "body contains \\def");
    ("\\edef", "body contains \\edef");
    ("\\gdef", "body contains \\gdef");
    ("\\xdef", "body contains \\xdef");
    ("\\let", "body contains \\let");
    ("\\expandafter", "body contains \\expandafter");
    ("\\csname", "body contains \\csname");
    ("\\noexpand", "body contains \\noexpand");
    ("\\string", "body contains \\string");
    ("\\meaning", "body contains \\meaning");
    ("\\ifx", "body contains conditional \\ifx");
    ("\\ifnum", "body contains conditional \\ifnum");
    ("\\ifcase", "body contains conditional \\ifcase");
    ("\\ifdim", "body contains conditional \\ifdim");
    ("\\ifcat", "body contains conditional \\ifcat");
    ("\\if", "body contains conditional \\if");
    ("\\else", "body contains \\else");
    ("\\fi", "body contains \\fi");
    ("\\input", "body contains \\input");
    ("\\include", "body contains \\include");
    ("\\read", "body contains \\read");
    ("\\write", "body contains \\write");
    ("\\count", "body contains register \\count");
    ("\\dimen", "body contains register \\dimen");
    ("\\skip", "body contains register \\skip");
    ("\\toks", "body contains register \\toks");
    ("\\futurelet", "body contains \\futurelet");
  ]

(** Check if body contains a blocklisted control sequence. We need to verify the
    match is actually a control sequence (followed by non-letter or end). *)
let check_blocklist body =
  let check (pattern, reason) =
    let plen = String.length pattern in
    let blen = String.length body in
    let rec scan i =
      if i > blen - plen then None
      else if String.sub body i plen = pattern then
        (* Verify it's a complete control sequence *)
        let after = i + plen in
        if after >= blen || not (is_letter body.[after]) then Some reason
        else scan (i + 1)
      else scan (i + 1)
    in
    scan 0
  in
  List.find_map check _blocklist

let classify (def : user_macro_def) : classified_def =
  if def.arity < 0 || def.arity > 9 then
    { def; status = Unsupported "arity out of range (must be 0-9)" }
  else
    match check_blocklist def.body with
    | Some reason -> { def; status = Unsupported reason }
    | None -> { def; status = Supported }

(* ── Dependency edges ────────────────────────────────────────────── *)

let extract_control_seqs body =
  let refs = ref [] in
  let n = String.length body in
  let i = ref 0 in
  while !i < n do
    if body.[!i] = '\\' && !i + 1 < n && is_letter body.[!i + 1] then (
      let start = !i + 1 in
      let j = ref start in
      while !j < n && is_letter body.[!j] do
        incr j
      done;
      refs := String.sub body start (!j - start) :: !refs;
      i := !j)
    else incr i
  done;
  !refs

let build_dep_edges (defs : user_macro_def list) : dep_edge list =
  let name_set =
    let tbl = Hashtbl.create 32 in
    List.iter (fun d -> Hashtbl.replace tbl d.name ()) defs;
    tbl
  in
  List.concat_map
    (fun d ->
      let refs = extract_control_seqs d.body in
      List.filter_map
        (fun r ->
          if Hashtbl.mem name_set r && r <> d.name then
            Some { from_name = d.name; to_name = r }
          else None)
        refs)
    defs

(* ── Cycle detection via DFS ─────────────────────────────────────── *)

type color = White | Gray | Black

let detect_cycle (edges : dep_edge list) (names : string list) :
    bool * string list =
  let adj = Hashtbl.create 32 in
  List.iter (fun n -> Hashtbl.replace adj n []) names;
  List.iter
    (fun e ->
      if Hashtbl.mem adj e.from_name && Hashtbl.mem adj e.to_name then
        Hashtbl.replace adj e.from_name
          (e.to_name
          :: (try Hashtbl.find adj e.from_name with Not_found -> [])))
    edges;
  let color = Hashtbl.create 32 in
  List.iter (fun n -> Hashtbl.replace color n White) names;
  let cycle_path = ref [] in
  let has_cycle = ref false in
  let rec dfs node path =
    if !has_cycle then ()
    else (
      Hashtbl.replace color node Gray;
      let neighbors = try Hashtbl.find adj node with Not_found -> [] in
      List.iter
        (fun nb ->
          if !has_cycle then ()
          else
            match Hashtbl.find_opt color nb with
            | Some Gray ->
                has_cycle := true;
                cycle_path := nb :: node :: path
            | Some White -> dfs nb (node :: path)
            | _ -> ())
        neighbors;
      if not !has_cycle then Hashtbl.replace color node Black)
  in
  List.iter
    (fun n -> if (not !has_cycle) && Hashtbl.find color n = White then dfs n [])
    names;
  (!has_cycle, List.rev !cycle_path)

(* ── Orchestrator ────────────────────────────────────────────────── *)

let create (src : string) : registry =
  let raw_defs = parse_definitions src in
  let classified = List.map classify raw_defs in
  let supported_defs =
    List.filter_map
      (fun cd ->
        match cd.status with Supported -> Some cd.def | Unsupported _ -> None)
      classified
  in
  let edges = build_dep_edges supported_defs in
  let user_names = List.map (fun d -> d.name) supported_defs in
  let has_cycle, cycle_path = detect_cycle edges user_names in
  let supported_count =
    List.length (List.filter (fun cd -> cd.status = Supported) classified)
  in
  let unsupported_count =
    List.length
      (List.filter
         (fun cd -> match cd.status with Unsupported _ -> true | _ -> false)
         classified)
  in
  {
    defs = classified;
    edges;
    has_cycle;
    cycle_path;
    supported_count;
    unsupported_count;
  }

(* ── Parameter placeholder conversion ─────────────────────────────── *)

let param_to_placeholder body =
  let buf = Buffer.create (String.length body + 16) in
  let n = String.length body in
  let i = ref 0 in
  while !i < n do
    if
      !i + 1 < n
      && body.[!i] = '#'
      && body.[!i + 1] >= '1'
      && body.[!i + 1] <= '9'
    then (
      Buffer.add_char buf '$';
      Buffer.add_char buf body.[!i + 1];
      i := !i + 2)
    else (
      Buffer.add_char buf body.[!i];
      incr i)
  done;
  Buffer.contents buf
