(** Typed project representation. See [project_model.mli]. *)

type file_id = int
type file_entry = { id : file_id; path : string; is_root : bool }
type engine_profile = Pdflatex | Xelatex | Lualatex | Ptex_uptex

type declared_feature =
  | UTF8_inputenc
  | UTF8_direct
  | Babel_standard
  | Polyglossia
  | Amsmath
  | Hyperref
  | Graphicx_eps_only
  | Graphicx_multi
  | Bibtex
  | Natbib
  | Biblatex
  | Unicode_math
  | Opentype_fonts
  | Lua_scripting
  | Japanese_cjk
  | Other of string

type t = {
  files : file_entry list;
  root : file_id;
  engine : engine_profile;
  declared_features : declared_feature list;
}

let engine_to_string = function
  | Pdflatex -> "pdflatex"
  | Xelatex -> "xelatex"
  | Lualatex -> "lualatex"
  | Ptex_uptex -> "ptex_uptex"

let feature_to_string = function
  | UTF8_inputenc -> "utf8_inputenc"
  | UTF8_direct -> "utf8_direct"
  | Babel_standard -> "babel_standard"
  | Polyglossia -> "polyglossia"
  | Amsmath -> "amsmath"
  | Hyperref -> "hyperref"
  | Graphicx_eps_only -> "graphicx_eps_only"
  | Graphicx_multi -> "graphicx_multi"
  | Bibtex -> "bibtex"
  | Natbib -> "natbib"
  | Biblatex -> "biblatex"
  | Unicode_math -> "unicode_math"
  | Opentype_fonts -> "opentype_fonts"
  | Lua_scripting -> "lua_scripting"
  | Japanese_cjk -> "japanese_cjk"
  | Other s -> s

(* Engine from a Build_profile.t. Build_profile.engine constructors differ from
   ours; map conservatively. LaTeX (plain) and Unknown both fall back to
   Pdflatex as the safest v26.2 assumption. *)
let engine_of_build_profile (bp : Build_profile.t) : engine_profile =
  match bp.Build_profile.engine with
  | Build_profile.PDFLaTeX -> Pdflatex
  | Build_profile.XeLaTeX -> Xelatex
  | Build_profile.LuaLaTeX -> Lualatex
  | Build_profile.LaTeX -> Pdflatex
  | Build_profile.Unknown -> Pdflatex

(* Delegate include-scanning to Include_resolver (shipped v26.1). One source of
   truth for this logic. *)
let scan_includes (src : string) : string list =
  List.map
    (fun (e : Include_resolver.include_entry) -> e.raw_path)
    (Include_resolver.extract_includes src)

let read_file_safe (path : string) :
    (string, [ `File_not_found of string | `Not_latex of string ]) result =
  if not (Sys.file_exists path) then Error (`File_not_found path)
  else if not (Filename.check_suffix path ".tex") then Error (`Not_latex path)
  else
    try
      let ic = open_in path in
      let n = in_channel_length ic in
      let buf = Bytes.create n in
      really_input ic buf 0 n;
      close_in ic;
      Ok (Bytes.to_string buf)
    with Sys_error msg ->
      (* EXN-OK: file IO failure reported as File_not_found. *)
      Error (`File_not_found msg)

let of_root ?(engine = Pdflatex) ?(declared_features = []) (root_path : string)
    : (t, [ `File_not_found of string | `Not_latex of string ]) result =
  match read_file_safe root_path with
  | Error e -> Error e
  | Ok src ->
      let base_dir = Filename.dirname root_path in
      let next_id = ref 0 in
      let mk_id () =
        let i = !next_id in
        next_id := i + 1;
        i
      in
      let root_id = mk_id () in
      let files = ref [ { id = root_id; path = root_path; is_root = true } ] in
      (* One pass: enumerate direct includes of the root. v26.2 does NOT recurse
         (plan §2.6: include analysis at project_model layer stays single-level;
         deep graphs are build_graph's job). *)
      List.iter
        (fun rel ->
          let candidate =
            let p = Filename.concat base_dir rel in
            if Sys.file_exists p then p
            else if Sys.file_exists (p ^ ".tex") then p ^ ".tex"
            else p
          in
          let entry = { id = mk_id (); path = candidate; is_root = false } in
          files := entry :: !files)
        (scan_includes src);
      Ok { files = List.rev !files; root = root_id; engine; declared_features }

let root_file (t : t) : file_entry = List.find (fun f -> f.id = t.root) t.files
let all_files (t : t) : file_entry list = t.files

let find (t : t) (id : file_id) : file_entry option =
  List.find_opt (fun f -> f.id = id) t.files
