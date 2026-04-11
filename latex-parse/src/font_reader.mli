(* ══════════════════════════════════════════════════════════════════════
   Font_reader — TrueType/OpenType cmap table reader

   Reads the cmap table from a .ttf/.otf font file and checks coverage
   of CJK Unified Ideographs (U+4E00–U+9FFF) for CJK-007.
   ══════════════════════════════════════════════════════════════════════ *)

val has_cjk_coverage : string -> bool option
(** [has_cjk_coverage path] returns [Some true] if the font at [path]
    covers the CJK Unified Ideographs range, [Some false] if it does
    not, and [None] on I/O error or unrecognizable font format. *)
