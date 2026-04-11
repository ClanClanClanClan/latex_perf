(* ══════════════════════════════════════════════════════════════════════
   File_analyzer — extract and analyze external files from LaTeX source

   Orchestrator that extracts \includegraphics paths, resolves them,
   dispatches to png_reader/jpeg_reader/pdf_reader/font_reader,
   and builds a File_context.file_analysis record.
   ══════════════════════════════════════════════════════════════════════ *)

val analyze_files : base_dir:string -> source:string -> File_context.file_analysis
(** [analyze_files ~base_dir ~source] extracts file references from [source],
    resolves them relative to [base_dir] (and any \graphicspath entries),
    reads metadata from found files, and returns the analysis. *)

val extract_includegraphics_paths : string -> string list
(** [extract_includegraphics_paths source] returns all file path arguments
    from \includegraphics commands in [source]. *)

val extract_graphicspath : string -> string list
(** [extract_graphicspath source] returns directory paths from
    \graphicspath commands. *)
