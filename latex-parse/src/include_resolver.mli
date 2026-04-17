(** Include resolver: parse and resolve [\input], [\include], [\includeonly]
    from LaTeX source. *)

type include_entry = {
  command : string;  (** ["input"] or ["include"]. *)
  raw_path : string;  (** Argument as written in source. *)
  position : int;  (** Byte offset. *)
}

type resolved_include = {
  entry : include_entry;
  resolved_path : string option;  (** [None] = unresolved. *)
}

val extract_includes : string -> include_entry list
(** Extract all [\input\{...\}] and [\include\{...\}] from source. *)

val extract_includeonly : string -> string list
(** Parse [\includeonly\{a,b,c\}] into a list of basenames. *)

val resolve_include : base_dir:string -> include_entry -> resolved_include
(** Resolve an include entry to an absolute path. Tries bare path, then with
    [.tex] extension. *)

val resolve_all : base_dir:string -> include_entry list -> resolved_include list
