(* ══════════════════════════════════════════════════════════════════════
   File_context — thread-local storage for external file analysis results

   Set by validators_cli / REST handlers before run_all; consumed by L3
   validators via get_file_context (). Follows the same pattern as
   Log_parser.{set,get,clear}_log_context.
   ══════════════════════════════════════════════════════════════════════ *)

type image_info = {
  path : string;
  format : [ `PNG | `JPEG ];
  width_px : int;
  height_px : int;
  dpi_x : float;  (** 0.0 = not specified *)
  dpi_y : float;
  has_transparency : bool;
  color_type : [ `Gray | `RGB | `RGBA | `Indexed | `GrayAlpha | `CMYK | `YCCK ];
  has_icc_profile : bool;
  icc_is_srgb : bool;
  palette_size : int;  (** 0 if no palette *)
  file_size : int;
}

type pdf_info = {
  path : string;
  file_size : int;
  has_struct_tree_root : bool;
  has_mark_info : bool;
  figures_without_alt : int;
  links_without_contents : int;
  lang_entry : string option;
  fonts : (string * bool * bool) list;  (** (name, embedded, subsetted) *)
  has_spot_colour : bool;
  has_spot_colour_vector : bool;
  streams_all_compressed : bool;
  page_label_count : int;
  page_count : int;
}

type font_info = { path : string; has_cjk_coverage : bool }

type file_analysis = {
  images : image_info list;
  pdfs : pdf_info list;
  fonts : font_info list;
  doc_class : string;
}

val set_file_context : file_analysis -> unit
val get_file_context : unit -> file_analysis option
val clear_file_context : unit -> unit
