(** Parse and query `.aux` files produced by pdflatex (memo §5.5, v26.2).

    v26.2 scope: pdflatex `.aux` only. xelatex / lualatex `.aux` files are
    mostly-compatible but edge cases (counter serialization) may fail
    gracefully. Related aux-family files (`.toc`, `.lof`, `.lot`, `.idx`,
    `.glg`) are OUT of scope for v26.2.

    Design note: this is distinct from [Build_artifact_state] which wraps the
    runtime profile and holds the parsed log context. This module parses the
    .aux FILE CONTENT on disk. See ADR-002. *)

type label_entry = {
  name : string;  (** Label name as written with \label{...}. *)
  ref_number : string;
      (** First arg of the reference struct — section number etc. *)
  page_number : string;  (** Second arg — page where \label was placed. *)
  raw : string;  (** Original \newlabel arg for debugging. *)
}

type bibcite_entry = {
  key : string;  (** Citation key from \cite{...}. *)
  number : string;  (** Rendered citation number or author-year string. *)
}

type t = {
  source_path : string;
  labels : label_entry list;
  bibcites : bibcite_entry list;
  bibstyle : string option;  (** \bibstyle{...} if present. *)
  bibdata : string list;  (** \bibdata{...} entries (split on comma). *)
  parse_warnings : string list;  (** Lines the parser couldn't classify. *)
}

val of_file :
  string -> (t, [ `File_not_found of string | `Read_error of string ]) result
(** Parse a `.aux` file from disk. Returns [Ok t] even if the file has
    unrecognised lines — those land in [parse_warnings]. *)

val of_string : source_path:string -> string -> t
(** Parse `.aux` content directly. [source_path] is stored for traceability. *)

val find_label : t -> string -> label_entry option
(** [find_label t name] returns the first [\newlabel] entry with the given name,
    or [None]. For duplicate-label detection use [labels_unique]. *)

val find_bibcite : t -> string -> bibcite_entry option
(** [find_bibcite t key] returns the [\bibcite] entry for [key], or [None]. *)

val labels_unique : t -> bool
(** True iff no two [\newlabel] entries share a name. pdflatex emits a warning
    on duplicate labels but still writes both; this predicate is the T4
    coherence check at the single-file level. *)
