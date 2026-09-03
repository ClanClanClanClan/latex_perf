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

(* Include_resolver.extract_includes is COMMENT-BLIND: a commented `% \input
   foo` (e.g. tcilatex.tex's `% the \input tcilatex`, ubiquitous in
   Scientific-Word output) would be read as a real edge and manufacture a FALSE
   self-cycle on a document pdflatex compiles cleanly. Blank
   comment/verbatim/\verb/url ranges to spaces (offset-preserving) before
   scanning so only LIVE includes count. Blanking can only REMOVE edges → for
   cycle detection it can only UNDER-detect (sound), never invent a cycle. *)
let live_blanked (src : string) : string =
  let vcu = Validators_common.find_verbatim_comment_url_ranges src in
  if vcu = [] then src
  else
    let b = Bytes.of_string src in
    let len = Bytes.length b in
    List.iter
      (fun (a, z) ->
        for k = a to z - 1 do
          if k >= 0 && k < len then Bytes.set b k ' '
        done)
      vcu;
    Bytes.unsafe_to_string b

let scan_includes_live_entries (src : string) :
    Include_resolver.include_entry list =
  Include_resolver.extract_includes (live_blanked src)

let scan_includes_live (src : string) : string list =
  List.map
    (fun (e : Include_resolver.include_entry) -> e.raw_path)
    (scan_includes_live_entries src)

(* ── OPEN-007 T2 gate probe (2026-09-02) ───────────────────────────── The
   comment-semantics breaker gate below must NOT probe the root alone: a
   `%`-catcode breaker carried in an \input child or a local .sty/.cls changes
   the ROOT's later `%`-semantics, so a root-only gate blanks a live
   `%\input{missing}` and manufactures a false-READY (two measured vectors: a
   local `pctignore.sty` doing `\catcode`\%=9`, and an \input child doing the
   same — both pdflatex-fatal, both READY under a root-only gate). The first
   draft called root-only gating "structural"; it is not: candidates from the
   COMMENT-BLIND scan are a SUPERSET of the live edges (blanking only removes),
   so probing that superset is conservative and complete. Bounded like the
   closure walk (48 files, depth 6). Children are read as RAW BYTES with no
   extension filter — an [\input{macros.def}] can carry catcode surgery exactly
   like a .tex child. Returns the collected sources AND an [all_readable] flag:
   a candidate that EXISTS but cannot be read cannot be probed, and skipping it
   would degrade toward BLANKING — the fail-OPEN direction (the first draft's
   wildcard-swallow read did exactly that while its comment claimed the
   opposite) — so the caller must treat [all_readable = false] as
   breaker-present. A NONEXISTENT candidate is skipped without tripping the
   flag: a file TeX cannot read either cannot change catcodes, and if it is a
   LIVE missing include the live scan still records it for T2. *)
let collect_probe_sources ~(base_dir : string) (root_src : string) :
    string list * bool =
  let all_readable = ref true in
  let read_raw (path : string) : string option =
    try
      let ic = open_in_bin path in
      let len = in_channel_length ic in
      let b = really_input_string ic len in
      close_in ic;
      Some b
    with Sys_error _ ->
      (* EXN-OK: existing-but-unreadable is reported via [all_readable]; the
         caller fails CLOSED on it. *)
      None
  in
  let fuel = ref 48 in
  let seen = Hashtbl.create 16 in
  let out = ref [] in
  let sty_names (src : string) : string list =
    (* \usepackage[..]{a,b} / \RequirePackage / \documentclass — names only;
       resolution to local files happens at the caller. Comment-BLIND on purpose
       (superset). *)
    let n = String.length src in
    let names = ref [] in
    let read_names_at j cls =
      (* j points at '['-or-'{'; skip one optional [..] then read {..} *)
      let j = ref j in
      if !j < n && src.[!j] = '[' then (
        while !j < n && src.[!j] <> ']' do
          incr j
        done;
        if !j < n then incr j);
      if !j < n && src.[!j] = '{' then (
        let k = ref (!j + 1) in
        while !k < n && src.[!k] <> '}' do
          incr k
        done;
        if !k < n then
          String.split_on_char ',' (String.sub src (!j + 1) (!k - !j - 1))
          |> List.iter (fun s -> names := (String.trim s, cls) :: !names))
    in
    let scan needle cls =
      let m = String.length needle in
      let i = ref 0 in
      while !i + m <= n do
        if String.sub src !i m = needle then (
          read_names_at (!i + m) cls;
          i := !i + m)
        else incr i
      done
    in
    scan "\\usepackage" false;
    scan "\\RequirePackage" false;
    scan "\\documentclass" true;
    List.rev_map
      (fun (name, cls) -> name ^ if cls then ".cls" else ".sty")
      !names
  in
  let rec walk (dir : string) (src : string) (depth : int) : unit =
    if depth <= 0 then ()
    else (
      (* local style/class files referenced from THIS file *)
      List.iter
        (fun fname ->
          let path = Filename.concat dir fname in
          if
            !fuel > 0
            && (not (Hashtbl.mem seen path))
            && Sys.file_exists path
            && not (Sys.is_directory path)
          then (
            Hashtbl.replace seen path ();
            decr fuel;
            match read_raw path with
            | Some b -> out := b :: !out
            | None -> all_readable := false))
        (sty_names src);
      (* transitive .tex children via the comment-BLIND candidate scan *)
      List.iter
        (fun rel ->
          let p0 = Filename.concat dir rel in
          let path = if Sys.file_exists p0 then p0 else p0 ^ ".tex" in
          if
            !fuel > 0
            && (not (Hashtbl.mem seen path))
            && Sys.file_exists path
            && not (Sys.is_directory path)
          then (
            Hashtbl.replace seen path ();
            decr fuel;
            match read_raw path with
            | Some child ->
                out := child :: !out;
                walk (Filename.dirname path) child (depth - 1)
            | None -> all_readable := false))
        (scan_includes src))
  in
  walk base_dir root_src 6;
  (List.rev !out, !all_readable)

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
         deep graphs are build_graph's job).

         OPEN-007 T2 channel (2026-09-02): only LIVE includes are project edges.
         A commented `% \input{ghost}` (or one inside verbatim) is dead to TeX —
         pdflatex compiles without the file — yet the raw scan recorded it and
         T2 rejected the document ("project not closed: missing file"), the
         single biggest residual comment-blind channel on the 199-root frame.
         [scan_includes_live] blanks comment/verbatim/url ranges first, exactly
         as the cycle check has since R7-4. FAIL-CLOSED under a
         comment-semantics breaker ([Validators_common]): catcode surgery can
         make a `%`-prefixed \input EXECUTE, so under any breaker the raw scan
         is kept — today's behaviour, at worst an over-rejection, never a missed
         live edge (a missed live \input{missing} would be a manufactured
         false-READY, the cardinal direction). The gate probes the root PLUS
         [collect_probe_sources] (transitive raw-scan children + local
         .sty/.cls, bounded): a breaker carried in a child changes the ROOT's
         later %-semantics, and a root-only gate was a MEASURED false-READY (two
         pdflatex-fatal vectors, C-34). *)
      let breaker_present =
        let probes, all_readable = collect_probe_sources ~base_dir src in
        (not all_readable)
        || Validators_common.comment_blanking_breakers (src :: probes)
      in
      let live_entries =
        if breaker_present then Include_resolver.extract_includes src
        else scan_includes_live_entries src
      in
      (* OPEN-040 (2026-09-04): a locally-missing [\input] target that the
         PINNED TeX tree ships ([Texmf_tree_allowlist]) is not a missing project
         file — kpsewhich resolves it and the doc compiles with no local copy
         (every entry compile-verified; 20 frame papers rescued, 0
         manufactured). Guards, each measured: [\input] edges only
         ([\include{xy}] is fatal); EXACT-byte name match (case-folding
         manufactures); PREAMBLE position only (body-position [\input xy] is
         fatal; all 28 real occurrences are preamble). The position test runs on
         the live-blanked view, whose offsets equal the raw ones. *)
      let live_begin_off =
        let blanked = live_blanked src in
        let needle = "\\begin{document}" in
        let m = String.length needle in
        let n = String.length blanked in
        let rec go i =
          if i + m > n then max_int
          else if String.sub blanked i m = needle then i
          else go (i + 1)
        in
        go 0
      in
      let tree_shipped (e : Include_resolver.include_entry) =
        e.command = "input"
        && Texmf_tree_allowlist.mem (String.trim e.raw_path)
        && e.position < live_begin_off
      in
      List.iter
        (fun (entry : Include_resolver.include_entry) ->
          let rel = entry.raw_path in
          let candidate =
            (* DIR-SHADOW (OPEN-007 T2, 2026-09-02): when `p` exists but is a
               DIRECTORY and `p.tex` also exists, kpathsea reads the FILE —
               preferring the directory made t2_check reject two compiling
               papers (Content/Appendix dir + Content/Appendix.tex). A directory
               with NO .tex sibling still resolves to `p`, keeping the
               fr_dir_target fatal correctly rejected. *)
            let p = Filename.concat base_dir rel in
            if Sys.file_exists p && not (Sys.is_directory p) then p
            else if Sys.file_exists (p ^ ".tex") then p ^ ".tex"
            else p
          in
          let locally_resolved =
            Sys.file_exists candidate && not (Sys.is_directory candidate)
          in
          if (not locally_resolved) && tree_shipped entry then ()
          else
            let fe = { id = mk_id (); path = candidate; is_root = false } in
            files := fe :: !files)
        live_entries;
      Ok { files = List.rev !files; root = root_id; engine; declared_features }

(* v27.1.62 (R7-4): detect an \input/\include CYCLE reachable from [root_path].
   [of_root] enumerates only the root's DIRECT includes (single-level, plan
   §2.6), so a cycle that closes through a child (a→b→a) is invisible to the
   artefact-level [Build_graph.is_acyclic] check. pdflatex follows \input
   recursively; a cycle exhausts TeX's input nesting → "! TeX capacity exceeded,
   sorry [text input levels=15]", a deterministic fatal (exit 1, no PDF).

   Recursive DFS over the resolved include graph: a path-stack is the GREY set
   (back-edge ⇒ cycle) and a hashtable is the BLACK set (fully-explored ⇒ skip).
   The stack membership test runs BEFORE the black-set test, so a back-edge onto
   a grey node is never masked by memoisation. SOUND BY UNDER-APPROXIMATION /
   add-NOT-READY-only: paths are normalised to ABSOLUTE form (never collapsing
   two distinct files into one, which is the only way a false cycle could
   arise), and any unresolvable / non-.tex child simply ends that branch — so
   the detector can only UNDER-detect a real cycle, never invent one on an
   acyclic project. Fuel-bounded against pathological fan-out. *)
let normalize_path (p : string) : string =
  let p =
    if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p
  in
  let parts = String.split_on_char '/' p in
  let rec go acc = function
    | [] -> List.rev acc
    | ("" | ".") :: tl -> go acc tl
    | ".." :: tl -> ( match acc with _ :: r -> go r tl | [] -> go acc tl)
    | seg :: tl -> go (seg :: acc) tl
  in
  "/" ^ String.concat "/" (go [] parts)

let has_include_cycle (root_path : string) : bool =
  let resolve (base : string) (rel : string) : string option =
    let p = Filename.concat base rel in
    if
      Sys.file_exists p
      && (not (Sys.is_directory p))
      && Filename.check_suffix p ".tex"
    then Some p
    else if Sys.file_exists (p ^ ".tex") then Some (p ^ ".tex")
    else None
  in
  let visited = Hashtbl.create 64 in
  let rec dfs (path : string) (stack : string list) (fuel : int) : bool =
    if fuel <= 0 then false
    else
      let cpath = normalize_path path in
      if List.mem cpath stack then true (* back edge → include cycle *)
      else if Hashtbl.mem visited cpath then false (* fully explored, acyclic *)
      else (
        Hashtbl.replace visited cpath ();
        match read_file_safe path with
        | Error _ -> false (* unresolvable/non-.tex child ends this branch *)
        | Ok src ->
            let base = Filename.dirname path in
            List.exists
              (fun rel ->
                match resolve base rel with
                | Some child -> dfs child (cpath :: stack) (fuel - 1)
                | None -> false)
              (scan_includes_live src))
  in
  dfs root_path [] 10000

let root_file (t : t) : file_entry = List.find (fun f -> f.id = t.root) t.files
let all_files (t : t) : file_entry list = t.files

let find (t : t) (id : file_id) : file_entry option =
  List.find_opt (fun f -> f.id = id) t.files
