(** Typed project representation for compile_contract (memo §5.5, v26.2).

    A [t] records everything the pre-compile readiness check (T0–T5) needs to
    know about a user's LaTeX project: files, include graph, declared engine
    profile, and feature declarations.

    This module is deliberately thin: it serialises a project layout into a
    typed value. Heavy lifting (include resolution, graph acyclicity) is in
    [Build_graph] and [Compile_contract]. *)

type file_id
(** Opaque identifier for a .tex file in the project. Stable across [t]
    lifetime; NOT persisted between runs. *)

type file_entry = {
  id : file_id;
  path : string;
      (** Repo-relative or absolute path, whichever the caller used at [of_root]
          time. *)
  is_root : bool;
}

type engine_profile =
  | Pdflatex
  | Xelatex
  | Lualatex
  | Ptex_uptex
      (** Parallels [Build_profile.engine]; re-declared here to avoid a module
          dependency cycle. [Build_profile.t] consumers should use
          [engine_of_build_profile] below to convert. *)

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
      (** Escape hatch for feature detected at runtime but not in the enum.
          Ignored by T3 admissibility check. *)

type t = private {
  files : file_entry list;
  root : file_id;
  engine : engine_profile;
  declared_features : declared_feature list;
}

val of_root :
  ?engine:engine_profile ->
  ?declared_features:declared_feature list ->
  string ->
  (t, [ `File_not_found of string | `Not_latex of string ]) result
(** Build a [t] from a root `.tex` path. Scans the file for [\input] /
    [\include] directives to enumerate [files]. Does NOT parse beyond
    include-resolution — that's [Compile_contract]'s job.

    @param engine defaults to [Pdflatex] (v26.2 GA baseline).
    @param declared_features
      empty list means "no features declared"; v26.2 doesn't auto-detect.
      Callers parsing the source may supply features from their own analysis. *)

val root_file : t -> file_entry
val all_files : t -> file_entry list
val find : t -> file_id -> file_entry option

val engine_of_build_profile : Build_profile.t -> engine_profile
(** Convenience: extract the [engine_profile] from a [Build_profile.t]. *)

val engine_to_string : engine_profile -> string
val feature_to_string : declared_feature -> string
