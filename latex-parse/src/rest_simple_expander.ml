(** Simple LaTeX control-sequence expander with configurable stripping rules.

    Supports two modes:
    - Legacy: strip a fixed list of commands (backward compatible)
    - Catalogue: delegate to {!Latex_parse_lib.Macro_catalogue.expand} for full
      v25r2 + argsafe expansion *)

type cfg = {
  strip_controls : string list;
  bfseries_until_brace : bool;
  catalogue : Latex_parse_lib.Macro_catalogue.catalogue option;
}

let default =
  {
    strip_controls = [ "textbf"; "emph"; "section" ];
    bfseries_until_brace = true;
    catalogue = None;
  }

let of_json (j : Yojson.Safe.t) : cfg =
  let open Yojson.Safe.Util in
  try
    let strip = j |> member "strip_controls" |> to_list |> List.map to_string in
    let bf = j |> member "bfseries_until_brace" |> to_bool in
    { strip_controls = strip; bfseries_until_brace = bf; catalogue = None }
  with _ -> default

let of_catalogue (cat : Latex_parse_lib.Macro_catalogue.catalogue) : cfg =
  { default with catalogue = Some cat }

let with_catalogue cfg (cat : Latex_parse_lib.Macro_catalogue.catalogue option)
    =
  { cfg with catalogue = cat }

(* ── Legacy expansion (backward compatible) ─────────────────────────── *)

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let take_ident s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && is_letter s.[!j] do
    incr j
  done;
  !j

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

let expand_once_legacy cfg s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if s.[!i] = '\\' then
      let j = take_ident s (!i + 1) in
      let name =
        if j > !i + 1 then String.sub s (!i + 1) (j - (!i + 1)) else ""
      in
      if List.mem name cfg.strip_controls then (
        match find_brace_block s j with
        | Some (off, len) ->
            Buffer.add_substring b s off len;
            i := j + len + 2
        | None ->
            Buffer.add_char b s.[!i];
            incr i)
      else if name = "bfseries" && cfg.bfseries_until_brace then (
        let k = ref j in
        while !k < n && s.[!k] <> '}' do
          incr k
        done;
        Buffer.add_substring b s j (!k - j);
        i := if !k < n then !k + 1 else !k)
      else (
        Buffer.add_char b s.[!i];
        incr i)
    else (
      Buffer.add_char b s.[!i];
      incr i)
  done;
  Buffer.contents b

let rec expand_fix_legacy cfg s =
  let s' = expand_once_legacy cfg s in
  if String.equal s s' then s else expand_fix_legacy cfg s'

(* ── Public API ─────────────────────────────────────────────────────── *)

let expand_once cfg s =
  match cfg.catalogue with
  | Some _cat ->
      (* Catalogue mode: single-pass is not meaningful; delegate to
         expand_fix *)
      s
  | None -> expand_once_legacy cfg s

let expand_fix cfg s =
  match cfg.catalogue with
  | Some cat -> Latex_parse_lib.Macro_catalogue.expand cat s
  | None -> expand_fix_legacy cfg s

let expand_and_tokenize cfg s =
  let expanded = expand_fix cfg s in
  let tokens = Latex_parse_lib.Tokenizer_lite.tokenize expanded in
  (expanded, tokens)
