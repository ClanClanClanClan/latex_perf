(* ══════════════════════════════════════════════════════════════════════
   File_context — thread-local storage for external file analysis results

   Follows Log_parser.{set,get,clear}_log_context (log_parser.ml:180-194).
   ══════════════════════════════════════════════════════════════════════ *)

type image_info = {
  path : string;
  format : [ `PNG | `JPEG ];
  width_px : int;
  height_px : int;
  dpi_x : float;
  dpi_y : float;
  has_transparency : bool;
  color_type : [ `Gray | `RGB | `RGBA | `Indexed | `GrayAlpha | `CMYK | `YCCK ];
  has_icc_profile : bool;
  icc_is_srgb : bool;
  palette_size : int;
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
  fonts : (string * bool * bool) list;
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

(* ── Thread-local context ──────────────────────────────────────────── *)

let _file_ctx_tbl : (int, file_analysis) Hashtbl.t = Hashtbl.create 4

let set_file_context (ctx : file_analysis) : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.replace _file_ctx_tbl tid ctx

let get_file_context () : file_analysis option =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.find_opt _file_ctx_tbl tid

let clear_file_context () : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.remove _file_ctx_tbl tid
