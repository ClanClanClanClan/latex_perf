(* ══════════════════════════════════════════════════════════════════════
   File_analyzer — extract and analyze external files from LaTeX source
   ══════════════════════════════════════════════════════════════════════ *)

(* ── Path extraction ───────────────────────────────────────────────── *)

let re_includegraphics =
  Re_compat.regexp {|\\includegraphics\(\[[^]]*\]\)?{\([^}]*\)}|}

let extract_includegraphics_paths (source : string) : string list =
  let paths = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re_includegraphics source !i in
       let path = Re_compat.matched_group _mr 2 source in
       paths := path :: !paths;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  List.rev !paths

let re_graphicspath_outer = Re_compat.regexp {|\\graphicspath{\([^}]*}\)|}
let re_graphicspath_dir = Re_compat.regexp {|{\([^}]*\)}|}

let extract_graphicspath (source : string) : string list =
  (* \graphicspath{{dir1/}{dir2/}{dir3/}} — extract each {dir/} individually *)
  let dirs = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re_graphicspath_outer source !i in
       let inner = Re_compat.matched_group _mr 1 source in
       let outer_end = Re_compat.match_end _mr in
       (* Extract each {dir/} from the inner content *)
       let j = ref 0 in
       (try
          while true do
            let _mr, _ =
              Re_compat.search_forward re_graphicspath_dir inner !j
            in
            let dir = Re_compat.matched_group _mr 1 inner in
            if dir <> "" then dirs := dir :: !dirs;
            j := Re_compat.match_end _mr
          done
        with Not_found -> ());
       i := outer_end
     done
   with Not_found -> ());
  List.rev !dirs

let re_docclass = Re_compat.regexp {|\\documentclass\(\[[^]]*\]\)?{\([^}]+\)}|}

let extract_docclass (source : string) : string =
  try
    let _mr, _ = Re_compat.search_forward re_docclass source 0 in
    Re_compat.matched_group _mr 2 source
  with Not_found -> ""

let re_cjk_font =
  Re_compat.regexp {|\\setCJK\(main\|sans\|mono\)font\(\[[^]]*\]\)?{\([^}]+\)}|}

let extract_cjk_fonts (source : string) : string list =
  let fonts = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re_cjk_font source !i in
       let name = Re_compat.matched_group _mr 3 source in
       fonts := name :: !fonts;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  List.rev !fonts

(* ── File resolution ───────────────────────────────────────────────── *)

let image_extensions = [ ""; ".png"; ".jpg"; ".jpeg"; ".PNG"; ".JPG"; ".JPEG" ]
let pdf_extensions = [ ""; ".pdf"; ".PDF" ]

let resolve_path ~(base_dir : string) ~(graphics_paths : string list)
    ~(extensions : string list) (raw_path : string) : string option =
  let try_dir dir =
    let base = Filename.concat dir raw_path in
    let rec try_ext = function
      | [] -> None
      | ext :: rest ->
          let full = base ^ ext in
          if Sys.file_exists full then Some full else try_ext rest
    in
    try_ext extensions
  in
  (* Try graphics paths first, then base_dir *)
  let search_dirs = graphics_paths @ [ base_dir ] in
  let rec try_dirs = function
    | [] -> None
    | dir :: rest -> (
        let full_dir =
          if Filename.is_relative dir then Filename.concat base_dir dir else dir
        in
        match try_dir full_dir with
        | Some _ as found -> found
        | None -> try_dirs rest)
  in
  try_dirs search_dirs

(* ── Image analysis ────────────────────────────────────────────────── *)

let analyze_image (path : string) : File_context.image_info option =
  let ext = String.lowercase_ascii (Filename.extension path) in
  let file_size =
    try (Unix.stat path).Unix.st_size with Unix.Unix_error _ -> 0
  in
  match ext with
  | ".png" -> (
      match Png_reader.read_png_info path with
      | None -> None
      | Some png ->
          let dpi_x, dpi_y =
            if png.phys_unit = 1 && png.phys_x > 0 then
              (float png.phys_x *. 0.0254, float png.phys_y *. 0.0254)
            else (0.0, 0.0)
          in
          let has_transparency =
            png.has_trns
            || png.color_type = 4 (* gray + alpha *)
            || png.color_type = 6 (* RGBA *)
          in
          let color_type =
            match png.color_type with
            | 0 -> `Gray
            | 2 -> `RGB
            | 3 -> `Indexed
            | 4 -> `GrayAlpha
            | 6 -> `RGBA
            | _ -> `RGB
          in
          Some
            {
              File_context.path;
              format = `PNG;
              width_px = png.width;
              height_px = png.height;
              dpi_x;
              dpi_y;
              has_transparency;
              color_type;
              has_icc_profile = png.has_iccp;
              icc_is_srgb =
                png.has_srgb
                || png.has_iccp
                   && String.lowercase_ascii png.iccp_name = "srgb";
              palette_size = png.plte_entries;
              file_size;
            })
  | ".jpg" | ".jpeg" -> (
      match Jpeg_reader.read_jpeg_info path with
      | None -> None
      | Some jpg ->
          let color_type =
            if jpg.components = 1 then `Gray
            else if jpg.components = 4 then
              if jpg.adobe_color_transform = 2 then `YCCK else `CMYK
            else `RGB (* 3 components = YCbCr → RGB *)
          in
          let icc_is_srgb = jpg.has_icc_profile && jpg.icc_color_space = `RGB in
          Some
            {
              File_context.path;
              format = `JPEG;
              width_px = jpg.width;
              height_px = jpg.height;
              dpi_x = jpg.dpi_x;
              dpi_y = jpg.dpi_y;
              has_transparency = false;
              (* JPEG has no alpha *)
              color_type;
              has_icc_profile = jpg.has_icc_profile;
              icc_is_srgb;
              palette_size = 0;
              file_size;
            })
  | _ -> None

(* ── PDF analysis ──────────────────────────────────────────────────── *)

let analyze_pdf (path : string) : File_context.pdf_info option =
  let file_size =
    try (Unix.stat path).Unix.st_size with Unix.Unix_error _ -> 0
  in
  match Pdf_reader.read_pdf_info path with
  | None -> None
  | Some info ->
      Some
        {
          File_context.path;
          file_size;
          has_struct_tree_root = info.has_struct_tree_root;
          has_mark_info = info.has_mark_info;
          figures_without_alt = info.figures_without_alt;
          links_without_contents = info.links_without_contents;
          lang_entry = info.lang;
          fonts = info.fonts;
          has_spot_colour = info.has_spot_colour;
          has_spot_colour_vector = info.has_spot_colour_vector;
          streams_all_compressed = info.streams_all_compressed;
          page_label_count = info.page_label_count;
          page_count = info.page_count;
        }

(* ── Font analysis ─────────────────────────────────────────────────── *)

let find_font_file ~(base_dir : string) (name : string) : string option =
  (* Try common font file locations *)
  let candidates =
    [
      Filename.concat base_dir (name ^ ".ttf");
      Filename.concat base_dir (name ^ ".otf");
      Filename.concat base_dir (name ^ ".TTF");
      Filename.concat base_dir (name ^ ".OTF");
    ]
  in
  List.find_opt Sys.file_exists candidates

let analyze_font ~(base_dir : string) (name : string) :
    File_context.font_info option =
  match find_font_file ~base_dir name with
  | None -> None
  | Some path -> (
      match Font_reader.has_cjk_coverage path with
      | None -> None
      | Some has_cjk -> Some { File_context.path; has_cjk_coverage = has_cjk })

(* ── Main orchestrator ─────────────────────────────────────────────── *)

let analyze_files ~(base_dir : string) ?tex_path ~(source : string) () :
    File_context.file_analysis =
  let graphics_paths = extract_graphicspath source in
  let doc_class = extract_docclass source in

  (* Analyze images *)
  let image_paths = extract_includegraphics_paths source in
  let images =
    List.filter_map
      (fun raw_path ->
        match
          resolve_path ~base_dir ~graphics_paths ~extensions:image_extensions
            raw_path
        with
        | Some full_path -> analyze_image full_path
        | None -> (
            (* Try as PDF *)
            match
              resolve_path ~base_dir ~graphics_paths ~extensions:pdf_extensions
                raw_path
            with
            | Some _ -> None (* PDFs handled separately *)
            | None -> None))
      image_paths
  in

  (* Analyze PDFs referenced by \includegraphics *)
  let pdfs =
    List.filter_map
      (fun raw_path ->
        match
          resolve_path ~base_dir ~graphics_paths ~extensions:pdf_extensions
            raw_path
        with
        | Some full_path ->
            let ext = String.lowercase_ascii (Filename.extension full_path) in
            if ext = ".pdf" then analyze_pdf full_path else None
        | None -> None)
      image_paths
  in

  (* Also look for the main output PDF (same name as .tex, with .pdf) *)
  let main_pdfs =
    match tex_path with
    | Some tp ->
        let stem =
          try Filename.chop_extension (Filename.basename tp)
          with Invalid_argument _ -> Filename.basename tp
        in
        let main_pdf_path = Filename.concat base_dir (stem ^ ".pdf") in
        if Sys.file_exists main_pdf_path then
          match analyze_pdf main_pdf_path with
          | Some info -> [ info ]
          | None -> []
        else []
    | None -> []
  in

  (* Analyze CJK fonts *)
  let cjk_font_names = extract_cjk_fonts source in
  let fonts =
    List.filter_map (fun name -> analyze_font ~base_dir name) cjk_font_names
  in

  { File_context.images; pdfs = pdfs @ main_pdfs; fonts; doc_class }
