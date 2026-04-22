(** Parse pdflatex `.aux` files. See [aux_state.mli].

    Parser strategy: line-oriented. Each top-level macro typically lives on one
    line in pdflatex output. We match each recognized macro with a regex;
    unmatched non-blank lines land in [parse_warnings]. *)

type label_entry = {
  name : string;
  ref_number : string;
  page_number : string;
  raw : string;
}

type bibcite_entry = { key : string; number : string }

type t = {
  source_path : string;
  labels : label_entry list;
  bibcites : bibcite_entry list;
  bibstyle : string option;
  bibdata : string list;
  parse_warnings : string list;
}

(* Match \newlabel{NAME}{ARGS}. ARGS is a group literal that may itself nest
   braces, which vanilla regex can't fully handle. Use a two-stage approach:
   capture everything up to the matching closing brace of \newlabel's second arg
   by walking the line. *)

let find_arg_group (s : string) (start : int) : (string * int) option =
  (* Starting at [start], if s.[start] = '{', return the substring between the
     matching braces and the index AFTER the closer. Balanced brace walk.
     Returns None if unbalanced. *)
  let n = String.length s in
  if start >= n || s.[start] <> '{' then None
  else
    let depth = ref 1 in
    let i = ref (start + 1) in
    let found_end = ref None in
    while !i < n && !found_end = None do
      let c = s.[!i] in
      if c = '{' then incr depth
      else if c = '}' then (
        decr depth;
        if !depth = 0 then found_end := Some !i);
      incr i
    done;
    match !found_end with
    | Some e -> Some (String.sub s (start + 1) (e - start - 1), e + 1)
    | None -> None

(* \newlabel{NAME}{{REF}{PAGE}{TITLE}{ANCHOR}{...}} We extract NAME and then the
   outer inner-args group, then split that into its own subgroups to get REF and
   PAGE. *)
let parse_newlabel (line : string) : label_entry option =
  let prefix = "\\newlabel" in
  let plen = String.length prefix in
  let n = String.length line in
  if n < plen || String.sub line 0 plen <> prefix then None
  else
    match find_arg_group line plen with
    | None -> None
    | Some (name, after_name) -> (
        match find_arg_group line after_name with
        | None -> None
        | Some (args_group, _) -> (
            (* args_group looks like: {REF}{PAGE}{TITLE}{ANCHOR}{...} Extract
               the first two subgroups. *)
            match find_arg_group args_group 0 with
            | None -> None
            | Some (ref_num, after_ref) -> (
                match find_arg_group args_group after_ref with
                | None -> None
                | Some (page_num, _) ->
                    Some
                      {
                        name;
                        ref_number = ref_num;
                        page_number = page_num;
                        raw = args_group;
                      })))

(* \bibcite{KEY}{NUMBER} *)
let parse_bibcite (line : string) : bibcite_entry option =
  let prefix = "\\bibcite" in
  let plen = String.length prefix in
  let n = String.length line in
  if n < plen || String.sub line 0 plen <> prefix then None
  else
    match find_arg_group line plen with
    | None -> None
    | Some (key, after_key) -> (
        match find_arg_group line after_key with
        | None -> None
        | Some (number, _) -> Some { key; number })

(* \bibstyle{STYLE} or \bibdata{FILE1,FILE2,...} — extract single group arg. *)
let parse_single_group (prefix : string) (line : string) : string option =
  let plen = String.length prefix in
  let n = String.length line in
  if n < plen || String.sub line 0 plen <> prefix then None
  else
    match find_arg_group line plen with
    | Some (arg, _) -> Some arg
    | None -> None

let split_on_comma (s : string) : string list =
  String.split_on_char ',' s
  |> List.map String.trim
  |> List.filter (fun s -> s <> "")

let of_string ~source_path (content : string) : t =
  let lines = String.split_on_char '\n' content in
  let labels = ref [] in
  let bibcites = ref [] in
  let bibstyle = ref None in
  let bibdata = ref [] in
  let warnings = ref [] in
  List.iter
    (fun raw_line ->
      let line = String.trim raw_line in
      if line = "" then ()
      else if String.length line >= 1 && line.[0] <> '\\' then
        warnings := raw_line :: !warnings
      else
        match parse_newlabel line with
        | Some l -> labels := l :: !labels
        | None -> (
            match parse_bibcite line with
            | Some b -> bibcites := b :: !bibcites
            | None -> (
                match parse_single_group "\\bibstyle" line with
                | Some s -> bibstyle := Some s
                | None -> (
                    match parse_single_group "\\bibdata" line with
                    | Some entries ->
                        bibdata := !bibdata @ split_on_comma entries
                    | None ->
                        (* Recognized-but-ignored macros we don't warn on. *)
                        let recognized_ignored =
                          [
                            "\\relax";
                            "\\@writefile";
                            "\\@input";
                            "\\@setckpt";
                            "\\providecommand";
                            "\\gdef";
                            "\\@tfor";
                          ]
                        in
                        let is_ignored =
                          List.exists
                            (fun p ->
                              let plen = String.length p in
                              String.length line >= plen
                              && String.sub line 0 plen = p)
                            recognized_ignored
                        in
                        if not is_ignored then warnings := raw_line :: !warnings
                    ))))
    lines;
  {
    source_path;
    labels = List.rev !labels;
    bibcites = List.rev !bibcites;
    bibstyle = !bibstyle;
    bibdata = !bibdata;
    parse_warnings = List.rev !warnings;
  }

let of_file (path : string) :
    (t, [ `File_not_found of string | `Read_error of string ]) result =
  if not (Sys.file_exists path) then Error (`File_not_found path)
  else
    try
      let ic = open_in path in
      let n = in_channel_length ic in
      let buf = Bytes.create n in
      really_input ic buf 0 n;
      close_in ic;
      Ok (of_string ~source_path:path (Bytes.to_string buf))
    with Sys_error msg ->
      (* EXN-OK: file IO failure reported as Read_error. *)
      Error (`Read_error msg)

let find_label (t : t) (name : string) : label_entry option =
  List.find_opt (fun l -> l.name = name) t.labels

let find_bibcite (t : t) (key : string) : bibcite_entry option =
  List.find_opt (fun b -> b.key = key) t.bibcites

let labels_unique (t : t) : bool =
  let names = List.map (fun l -> l.name) t.labels in
  let sorted = List.sort compare names in
  let rec no_adjacent_dup = function
    | [] | [ _ ] -> true
    | a :: b :: rest -> a <> b && no_adjacent_dup (b :: rest)
  in
  no_adjacent_dup sorted
