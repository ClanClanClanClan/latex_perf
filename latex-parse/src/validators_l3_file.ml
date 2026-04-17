(* ══════════════════════════════════════════════════════════════════════
   Validators_l3_file — 19 L3 semantic rules requiring external files

   All rules follow the Log_parser pattern: if File_context is not set, the rule
   returns None (graceful degradation).

   Rules: FIG-004, FIG-006, FIG-016, FIG-021 COL-001, COL-002, COL-003, COL-005,
   COL-004, COL-007 PDF-006, PDF-007, PDF-008, PDF-009, PDF-011, PDF-012
   TIKZ-002, TIKZ-008 CJK-007
   ══════════════════════════════════════════════════════════════════════ *)

open Validators_common

(* ══════════════════════════════════════════════════════════════════════ Image
   metadata rules (8)
   ══════════════════════════════════════════════════════════════════════ *)

(* FIG-004: Raster image exceeds 300 dpi *)
let r_fig_004 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (img : File_context.image_info) ->
              if img.dpi_x > 300.0 || img.dpi_y > 300.0 then acc + 1 else acc)
            0 ctx.images
        in
        if cnt > 0 then
          Some
            {
              id = "FIG-004";
              severity = Info;
              message = "Raster image exceeds 300 dpi";
              count = cnt;
            }
        else None
  in
  mk_rule "FIG-004" run

(* FIG-006: Bitmap image with transparency channel *)
let r_fig_006 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (img : File_context.image_info) ->
              if img.has_transparency then acc + 1 else acc)
            0 ctx.images
        in
        if cnt > 0 then
          Some
            {
              id = "FIG-006";
              severity = Info;
              message = "Bitmap image with transparency channel";
              count = cnt;
            }
        else None
  in
  mk_rule "FIG-006" run

(* FIG-016: Raster image colour profile not sRGB *)
let r_fig_016 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (img : File_context.image_info) ->
              if img.has_icc_profile && not img.icc_is_srgb then acc + 1
              else acc)
            0 ctx.images
        in
        if cnt > 0 then
          Some
            {
              id = "FIG-016";
              severity = Info;
              message = "Raster image colour profile not sRGB";
              count = cnt;
            }
        else None
  in
  mk_rule "FIG-016" run

(* FIG-021: Embedded bitmap > 20 MiB – PDF bloat *)
let r_fig_021 : rule =
  let max_size = 20 * 1024 * 1024 in
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (img : File_context.image_info) ->
              if img.file_size > max_size then acc + 1 else acc)
            0 ctx.images
        in
        if cnt > 0 then
          Some
            {
              id = "FIG-021";
              severity = Warning;
              message = "Embedded bitmap > 20 MiB — PDF bloat risk";
              count = cnt;
            }
        else None
  in
  mk_rule "FIG-021" run

(* COL-001: CMYK image in RGB workflow *)
let r_col_001 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (img : File_context.image_info) ->
              match img.color_type with `CMYK | `YCCK -> acc + 1 | _ -> acc)
            0 ctx.images
        in
        if cnt > 0 then
          Some
            {
              id = "COL-001";
              severity = Info;
              message = "CMYK image in RGB workflow";
              count = cnt;
            }
        else None
  in
  mk_rule "COL-001" run

(* COL-002: ICC profile missing in embedded image *)
let r_col_002 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (img : File_context.image_info) ->
              if not img.has_icc_profile then acc + 1 else acc)
            0 ctx.images
        in
        if cnt > 0 then
          Some
            {
              id = "COL-002";
              severity = Info;
              message = "ICC profile missing in embedded image";
              count = cnt;
            }
        else None
  in
  mk_rule "COL-002" run

(* COL-003: Transparent PNG in print-optimised class *)
let r_col_003 : rule =
  let print_classes = [ "book"; "memoir"; "scrbook"; "scrreprt" ] in
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        if not (List.mem ctx.doc_class print_classes) then None
        else
          let cnt =
            List.fold_left
              (fun acc (img : File_context.image_info) ->
                if img.format = `PNG && img.has_transparency then acc + 1
                else acc)
              0 ctx.images
          in
          if cnt > 0 then
            Some
              {
                id = "COL-003";
                severity = Warning;
                message = "Transparent PNG in print-optimised document class";
                count = cnt;
              }
          else None
  in
  mk_rule "COL-003" run

(* COL-005: Excess distinct colours (> 256) in indexed image *)
let r_col_005 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (img : File_context.image_info) ->
              if img.palette_size > 256 then acc + 1 else acc)
            0 ctx.images
        in
        if cnt > 0 then
          Some
            {
              id = "COL-005";
              severity = Info;
              message = "Excess distinct colours (> 256) in indexed image";
              count = cnt;
            }
        else None
  in
  mk_rule "COL-005" run

(* ══════════════════════════════════════════════════════════════════════ PDF
   structure rules (8)
   ══════════════════════════════════════════════════════════════════════ *)

(* PDF-006: Tagged PDF lacks /StructTreeRoot *)
let r_pdf_006 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              if pdf.has_mark_info && not pdf.has_struct_tree_root then acc + 1
              else acc)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "PDF-006";
              severity = Warning;
              message = "Tagged PDF lacks /StructTreeRoot";
              count = cnt;
            }
        else None
  in
  mk_rule "PDF-006" run

(* PDF-007: Figure objects without /Alt text in tagged PDF *)
let r_pdf_007 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              acc + pdf.figures_without_alt)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "PDF-007";
              severity = Warning;
              message = "Figure objects without /Alt text in tagged PDF";
              count = cnt;
            }
        else None
  in
  mk_rule "PDF-007" run

(* PDF-008: Link annotations missing /Contents *)
let r_pdf_008 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              acc + pdf.links_without_contents)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "PDF-008";
              severity = Warning;
              message =
                "Link annotations missing /Contents — screen-reader issue";
              count = cnt;
            }
        else None
  in
  mk_rule "PDF-008" run

(* PDF-009: /Lang entry missing or mismatched in PDF catalog *)
let r_pdf_009 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              match pdf.lang_entry with None -> acc + 1 | Some _ -> acc)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "PDF-009";
              severity = Warning;
              message = "/Lang entry missing in PDF catalog";
              count = cnt;
            }
        else None
  in
  mk_rule "PDF-009" run

(* PDF-011: Fonts in PDF not fully embedded or subsetted *)
let r_pdf_011 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              List.fold_left
                (fun a (_name, embedded, _subsetted) ->
                  if not embedded then a + 1 else a)
                acc pdf.fonts)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "PDF-011";
              severity = Error;
              message = "Fonts in PDF not fully embedded or subsetted";
              count = cnt;
            }
        else None
  in
  mk_rule "PDF-011" run

(* PDF-012: Logical page labels (/PageLabels) inconsistent with numbering *)
let r_pdf_012 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              (* Fire if page labels exist but count doesn't match page count.
                 page_label_count=0 means no labels (acceptable). Mismatch =
                 labels are present but don't cover all pages. *)
              if
                pdf.page_label_count > 0
                && pdf.page_label_count <> pdf.page_count
              then acc + 1
              else acc)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "PDF-012";
              severity = Info;
              message = "Logical page labels inconsistent with numbering";
              count = cnt;
            }
        else None
  in
  mk_rule "PDF-012" run

(* COL-004: PDF contains spot-colour separation *)
let r_col_004 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              if pdf.has_spot_colour then acc + 1 else acc)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "COL-004";
              severity = Info;
              message = "PDF contains spot-colour separation";
              count = cnt;
            }
        else None
  in
  mk_rule "COL-004" run

(* COL-007: Spot colour detected in vector element *)
let r_col_007 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              if pdf.has_spot_colour_vector then acc + 1 else acc)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "COL-007";
              severity = Info;
              message = "Spot colour detected in vector element";
              count = cnt;
            }
        else None
  in
  mk_rule "COL-007" run

(* ══════════════════════════════════════════════════════════════════════ Build
   integration rules (2)
   ══════════════════════════════════════════════════════════════════════ *)

(* TIKZ-002: TikZ compile time > 5 s *)
let r_tikz_002 : rule =
  let run _s =
    match Log_parser.get_log_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc t -> if t > 5.0 then acc + 1 else acc)
            0 ctx.tikz_compile_times
        in
        if cnt > 0 then
          Some
            {
              id = "TIKZ-002";
              severity = Warning;
              message = "TikZ compile time exceeds 5 seconds";
              count = cnt;
            }
        else None
  in
  mk_rule "TIKZ-002" run

(* TIKZ-008: Uncompressed PDFs generated by TikZ *)
let r_tikz_008 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (pdf : File_context.pdf_info) ->
              if not pdf.streams_all_compressed then acc + 1 else acc)
            0 ctx.pdfs
        in
        if cnt > 0 then
          Some
            {
              id = "TIKZ-008";
              severity = Info;
              message = "Uncompressed streams in PDF (possible TikZ output)";
              count = cnt;
            }
        else None
  in
  mk_rule "TIKZ-008" run

(* ══════════════════════════════════════════════════════════════════════ Font
   introspection (1)
   ══════════════════════════════════════════════════════════════════════ *)

(* CJK-007: Kanji glyph missing in selected CJK font *)
let r_cjk_007 : rule =
  let run _s =
    match File_context.get_file_context () with
    | None -> None
    | Some ctx ->
        let cnt =
          List.fold_left
            (fun acc (f : File_context.font_info) ->
              if not f.has_cjk_coverage then acc + 1 else acc)
            0 ctx.fonts
        in
        if cnt > 0 then
          Some
            {
              id = "CJK-007";
              severity = Warning;
              message = "Kanji glyph missing in selected CJK font";
              count = cnt;
            }
        else None
  in
  mk_rule "CJK-007" run

(* ── Rule list ─────────────────────────────────────────────────────── *)

let rules_l3_file : rule list =
  [
    r_fig_004;
    r_fig_006;
    r_fig_016;
    r_fig_021;
    r_col_001;
    r_col_002;
    r_col_003;
    r_col_005;
    r_pdf_006;
    r_pdf_007;
    r_pdf_008;
    r_pdf_009;
    r_pdf_011;
    r_pdf_012;
    r_col_004;
    r_col_007;
    r_tikz_008;
    r_cjk_007;
  ]
