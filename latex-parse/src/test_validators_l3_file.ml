(** Test_validators_l3_file — 19 L3 rules × 5-8 cases each. ~140 cases. *)

open Latex_parse_lib
open Test_helpers

let () = Unix.putenv "L0_VALIDATORS" "pilot"

(* ── Cache-busting: each test needs a unique source string ─────────── *)
let test_counter = ref 0

let unique_src () =
  incr test_counter;
  Printf.sprintf "%% l3-test-%d\n" !test_counter

(* ── Helpers ───────────────────────────────────────────────────────── *)

let empty_ctx ?(doc_class = "article") () : File_context.file_analysis =
  { images = []; pdfs = []; fonts = []; doc_class }

let mk_image ?(dpi_x = 72.0) ?(dpi_y = 72.0) ?(has_transparency = false)
    ?(color_type = `RGB) ?(has_icc = false) ?(icc_is_srgb = false)
    ?(palette_size = 0) ?(file_size = 1024) ?(format = `PNG) () :
    File_context.image_info =
  {
    path = "/tmp/test.png";
    format;
    width_px = 100;
    height_px = 100;
    dpi_x;
    dpi_y;
    has_transparency;
    color_type;
    has_icc_profile = has_icc;
    icc_is_srgb;
    palette_size;
    file_size;
  }

let mk_pdf ?(has_struct_tree = false) ?(has_mark_info = false)
    ?(figures_without_alt = 0) ?(links_without_contents = 0)
    ?(lang = None) ?(fonts = []) ?(has_spot = false) ?(has_spot_vec = false)
    ?(compressed = true) () : File_context.pdf_info =
  {
    path = "/tmp/test.pdf";
    file_size = 50000;
    has_struct_tree_root = has_struct_tree;
    has_mark_info;
    figures_without_alt;
    links_without_contents;
    lang_entry = lang;
    fonts;
    has_spot_colour = has_spot;
    has_spot_colour_vector = has_spot_vec;
    streams_all_compressed = compressed;
    page_label_count = 0;
    page_count = 1;
  }

let with_file_ctx ctx f =
  File_context.set_file_context ctx;
  Fun.protect ~finally:File_context.clear_file_context f

let () =
  (* ══════════════════════════════════════════════════════════════════
     FIG-004: Raster image exceeds 300 dpi
     ══════════════════════════════════════════════════════════════════ *)

  run "FIG-004 fires: 301 dpi" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~dpi_x:301.0 ~dpi_y:301.0 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "FIG-004" (unique_src ())) (tag ^ ": fires")));

  run "FIG-004 clean: 300 dpi exactly" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~dpi_x:300.0 ~dpi_y:300.0 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "FIG-004" (unique_src ())) (tag ^ ": clean")));

  run "FIG-004 clean: 72 dpi" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~dpi_x:72.0 ~dpi_y:72.0 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "FIG-004" (unique_src ())) (tag ^ ": clean")));

  run "FIG-004 no context: returns None" (fun tag ->
      File_context.clear_file_context ();
      expect (does_not_fire "FIG-004" (unique_src ())) (tag ^ ": no ctx"));

  run "FIG-004 count: 2 high-dpi images" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images =
            [ mk_image ~dpi_x:600.0 (); mk_image ~dpi_y:400.0 () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires_with_count "FIG-004" (unique_src ()) 2) (tag ^ ": count=2")));

  (* ══════════════════════════════════════════════════════════════════
     FIG-006: Bitmap image with transparency channel
     ══════════════════════════════════════════════════════════════════ *)

  run "FIG-006 fires: RGBA PNG" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images = [ mk_image ~has_transparency:true ~color_type:`RGBA () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "FIG-006" (unique_src ())) (tag ^ ": fires")));

  run "FIG-006 clean: RGB PNG" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~color_type:`RGB () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "FIG-006" (unique_src ())) (tag ^ ": clean")));

  run "FIG-006 fires: indexed with tRNS" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images =
            [
              mk_image ~has_transparency:true ~color_type:`Indexed
                ~palette_size:128 ();
            ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "FIG-006" (unique_src ())) (tag ^ ": fires")));

  run "FIG-006 no context" (fun tag ->
      File_context.clear_file_context ();
      expect (does_not_fire "FIG-006" (unique_src ())) (tag ^ ": no ctx"));

  (* ══════════════════════════════════════════════════════════════════
     FIG-016: Raster image colour profile not sRGB
     ══════════════════════════════════════════════════════════════════ *)

  run "FIG-016 fires: ICC present but not sRGB" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images = [ mk_image ~has_icc:true ~icc_is_srgb:false () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "FIG-016" (unique_src ())) (tag ^ ": fires")));

  run "FIG-016 clean: ICC sRGB" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images = [ mk_image ~has_icc:true ~icc_is_srgb:true () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "FIG-016" (unique_src ())) (tag ^ ": clean")));

  run "FIG-016 clean: no ICC" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~has_icc:false () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "FIG-016" (unique_src ())) (tag ^ ": clean")));

  run "FIG-016 no context" (fun tag ->
      File_context.clear_file_context ();
      expect (does_not_fire "FIG-016" (unique_src ())) (tag ^ ": no ctx"));

  (* ══════════════════════════════════════════════════════════════════
     FIG-021: Embedded bitmap > 20 MiB
     ══════════════════════════════════════════════════════════════════ *)

  run "FIG-021 fires: 25 MiB" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images = [ mk_image ~file_size:(25 * 1024 * 1024) () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "FIG-021" (unique_src ())) (tag ^ ": fires")));

  run "FIG-021 clean: 19 MiB" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images = [ mk_image ~file_size:(19 * 1024 * 1024) () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "FIG-021" (unique_src ())) (tag ^ ": clean")));

  run "FIG-021 clean: exactly 20 MiB" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images = [ mk_image ~file_size:(20 * 1024 * 1024) () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "FIG-021" (unique_src ())) (tag ^ ": boundary")));

  run "FIG-021 severity: Warning" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images = [ mk_image ~file_size:(21 * 1024 * 1024) () ];
        }
      in
      with_file_ctx ctx (fun () ->
          let results = Validators.run_all (unique_src ()) in
          match List.find_opt (fun r -> (r : Validators.result).id = "FIG-021") results with
          | Some r ->
              expect (r.severity = Warning) (tag ^ ": Warning severity")
          | None -> expect false (tag ^ ": should fire")));

  (* ══════════════════════════════════════════════════════════════════
     COL-001: CMYK image in RGB workflow
     ══════════════════════════════════════════════════════════════════ *)

  run "COL-001 fires: CMYK" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~color_type:`CMYK () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-001" (unique_src ())) (tag ^ ": fires")));

  run "COL-001 fires: YCCK" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~color_type:`YCCK () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-001" (unique_src ())) (tag ^ ": fires")));

  run "COL-001 clean: RGB" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~color_type:`RGB () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-001" (unique_src ())) (tag ^ ": clean")));

  run "COL-001 clean: Gray" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~color_type:`Gray () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-001" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     COL-002: ICC profile missing
     ══════════════════════════════════════════════════════════════════ *)

  run "COL-002 fires: no ICC" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~has_icc:false () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-002" (unique_src ())) (tag ^ ": fires")));

  run "COL-002 clean: has ICC" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~has_icc:true () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-002" (unique_src ())) (tag ^ ": clean")));

  run "COL-002 count: 3 missing" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          images =
            [ mk_image (); mk_image (); mk_image ~has_icc:true () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires_with_count "COL-002" (unique_src ()) 2) (tag ^ ": count=2")));

  (* ══════════════════════════════════════════════════════════════════
     COL-003: Transparent PNG in print-optimised class
     ══════════════════════════════════════════════════════════════════ *)

  run "COL-003 fires: transparent + book" (fun tag ->
      let ctx =
        {
          (empty_ctx ~doc_class:"book" ()) with
          images = [ mk_image ~has_transparency:true ~format:`PNG () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-003" (unique_src ())) (tag ^ ": fires")));

  run "COL-003 fires: transparent + memoir" (fun tag ->
      let ctx =
        {
          (empty_ctx ~doc_class:"memoir" ()) with
          images = [ mk_image ~has_transparency:true ~format:`PNG () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-003" (unique_src ())) (tag ^ ": fires")));

  run "COL-003 clean: transparent + article" (fun tag ->
      let ctx =
        {
          (empty_ctx ~doc_class:"article" ()) with
          images = [ mk_image ~has_transparency:true ~format:`PNG () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-003" (unique_src ())) (tag ^ ": clean")));

  run "COL-003 clean: opaque + book" (fun tag ->
      let ctx =
        {
          (empty_ctx ~doc_class:"book" ()) with
          images = [ mk_image ~has_transparency:false ~format:`PNG () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-003" (unique_src ())) (tag ^ ": clean")));

  run "COL-003 clean: transparent JPEG + book" (fun tag ->
      let ctx =
        {
          (empty_ctx ~doc_class:"book" ()) with
          images = [ mk_image ~has_transparency:true ~format:`JPEG () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-003" (unique_src ())) (tag ^ ": JPEG not PNG")));

  (* ══════════════════════════════════════════════════════════════════
     COL-005: Excess distinct colours (> 256)
     ══════════════════════════════════════════════════════════════════ *)

  run "COL-005 fires: palette > 256" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~palette_size:300 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-005" (unique_src ())) (tag ^ ": fires")));

  run "COL-005 clean: palette = 256" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~palette_size:256 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-005" (unique_src ())) (tag ^ ": clean")));

  run "COL-005 clean: no palette" (fun tag ->
      let ctx =
        { (empty_ctx ()) with images = [ mk_image ~palette_size:0 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-005" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     PDF-006: Tagged PDF lacks /StructTreeRoot
     ══════════════════════════════════════════════════════════════════ *)

  run "PDF-006 fires: marked but no struct tree" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs = [ mk_pdf ~has_mark_info:true ~has_struct_tree:false () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "PDF-006" (unique_src ())) (tag ^ ": fires")));

  run "PDF-006 clean: marked with struct tree" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs = [ mk_pdf ~has_mark_info:true ~has_struct_tree:true () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-006" (unique_src ())) (tag ^ ": clean")));

  run "PDF-006 clean: not marked" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~has_mark_info:false () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-006" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     PDF-007: Figure objects without /Alt text
     ══════════════════════════════════════════════════════════════════ *)

  run "PDF-007 fires: 3 figures no alt" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs = [ mk_pdf ~figures_without_alt:3 () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires_with_count "PDF-007" (unique_src ()) 3) (tag ^ ": count=3")));

  run "PDF-007 clean: 0 figures" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~figures_without_alt:0 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-007" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     PDF-008: Link annotations missing /Contents
     ══════════════════════════════════════════════════════════════════ *)

  run "PDF-008 fires: 2 links no contents" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs = [ mk_pdf ~links_without_contents:2 () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires_with_count "PDF-008" (unique_src ()) 2) (tag ^ ": count=2")));

  run "PDF-008 clean: 0 links" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~links_without_contents:0 () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-008" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     PDF-009: /Lang entry missing
     ══════════════════════════════════════════════════════════════════ *)

  run "PDF-009 fires: no lang" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~lang:None () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "PDF-009" (unique_src ())) (tag ^ ": fires")));

  run "PDF-009 clean: has lang" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~lang:(Some "en-US") () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-009" (unique_src ())) (tag ^ ": clean")));

  run "PDF-009 no context" (fun tag ->
      File_context.clear_file_context ();
      expect (does_not_fire "PDF-009" (unique_src ())) (tag ^ ": no ctx"));

  (* ══════════════════════════════════════════════════════════════════
     PDF-011: Fonts not embedded (Error severity!)
     ══════════════════════════════════════════════════════════════════ *)

  run "PDF-011 fires: font not embedded" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs = [ mk_pdf ~fonts:[ ("Times", false, false) ] () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "PDF-011" (unique_src ())) (tag ^ ": fires")));

  run "PDF-011 clean: font embedded" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs = [ mk_pdf ~fonts:[ ("Times", true, false) ] () ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-011" (unique_src ())) (tag ^ ": clean")));

  run "PDF-011 count: 2 not embedded" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs =
            [
              mk_pdf
                ~fonts:
                  [
                    ("Times", false, false);
                    ("Helvetica", false, false);
                    ("Courier", true, true);
                  ]
                ();
            ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires_with_count "PDF-011" (unique_src ()) 2) (tag ^ ": count=2")));

  run "PDF-011 severity: Error" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs = [ mk_pdf ~fonts:[ ("Times", false, false) ] () ];
        }
      in
      with_file_ctx ctx (fun () ->
          let results = Validators.run_all (unique_src ()) in
          match
            List.find_opt (fun r -> (r : Validators.result).id = "PDF-011") results
          with
          | Some r ->
              expect (r.severity = Error) (tag ^ ": Error severity")
          | None -> expect false (tag ^ ": should fire")));

  (* ══════════════════════════════════════════════════════════════════
     PDF-012: Page labels inconsistent with numbering
     ══════════════════════════════════════════════════════════════════ *)

  run "PDF-012 fires: label count != page count" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs =
            [
              {
                (mk_pdf ()) with
                page_label_count = 3;
                page_count = 5;
              };
            ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "PDF-012" (unique_src ())) (tag ^ ": fires")));

  run "PDF-012 clean: label count = page count" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs =
            [
              {
                (mk_pdf ()) with
                page_label_count = 5;
                page_count = 5;
              };
            ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-012" (unique_src ())) (tag ^ ": clean")));

  run "PDF-012 clean: no page labels" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          pdfs =
            [
              {
                (mk_pdf ()) with
                page_label_count = 0;
                page_count = 10;
              };
            ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "PDF-012" (unique_src ())) (tag ^ ": no labels")));

  run "PDF-012 no context" (fun tag ->
      File_context.clear_file_context ();
      expect (does_not_fire "PDF-012" (unique_src ())) (tag ^ ": no ctx"));

  (* ══════════════════════════════════════════════════════════════════
     COL-004: PDF contains spot-colour separation
     ══════════════════════════════════════════════════════════════════ *)

  run "COL-004 fires: spot colour" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~has_spot:true () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-004" (unique_src ())) (tag ^ ": fires")));

  run "COL-004 clean: no spot" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~has_spot:false () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-004" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     COL-007: Spot colour in vector element
     ══════════════════════════════════════════════════════════════════ *)

  run "COL-007 fires: spot vector" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~has_spot_vec:true () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "COL-007" (unique_src ())) (tag ^ ": fires")));

  run "COL-007 clean: no spot vector" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~has_spot_vec:false () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "COL-007" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     TIKZ-002: TikZ compile time > 5 s
     ══════════════════════════════════════════════════════════════════ *)

  run "TIKZ-002 fires: 6.2s compile time" (fun tag ->
      let log_ctx =
        { Log_parser.empty_context with tikz_compile_times = [ 6.2 ] }
      in
      Log_parser.set_log_context log_ctx;
      Fun.protect
        ~finally:Log_parser.clear_log_context
        (fun () -> expect (fires "TIKZ-002" (unique_src ())) (tag ^ ": fires")));

  run "TIKZ-002 clean: 4.9s" (fun tag ->
      let log_ctx =
        { Log_parser.empty_context with tikz_compile_times = [ 4.9 ] }
      in
      Log_parser.set_log_context log_ctx;
      Fun.protect
        ~finally:Log_parser.clear_log_context
        (fun () ->
          expect (does_not_fire "TIKZ-002" (unique_src ())) (tag ^ ": clean")));

  run "TIKZ-002 clean: no log context" (fun tag ->
      Log_parser.clear_log_context ();
      expect (does_not_fire "TIKZ-002" (unique_src ())) (tag ^ ": no ctx"));

  run "TIKZ-002 count: 2 slow pictures" (fun tag ->
      let log_ctx =
        {
          Log_parser.empty_context with
          tikz_compile_times = [ 7.0; 3.0; 12.5 ];
        }
      in
      Log_parser.set_log_context log_ctx;
      Fun.protect
        ~finally:Log_parser.clear_log_context
        (fun () ->
          expect (fires_with_count "TIKZ-002" (unique_src ()) 2) (tag ^ ": count=2")));

  (* ══════════════════════════════════════════════════════════════════
     TIKZ-008: Uncompressed PDFs
     ══════════════════════════════════════════════════════════════════ *)

  run "TIKZ-008 fires: uncompressed streams" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~compressed:false () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "TIKZ-008" (unique_src ())) (tag ^ ": fires")));

  run "TIKZ-008 clean: compressed streams" (fun tag ->
      let ctx =
        { (empty_ctx ()) with pdfs = [ mk_pdf ~compressed:true () ] }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "TIKZ-008" (unique_src ())) (tag ^ ": clean")));

  (* ══════════════════════════════════════════════════════════════════
     CJK-007: Kanji glyph missing
     ══════════════════════════════════════════════════════════════════ *)

  run "CJK-007 fires: font without CJK" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          fonts = [ { path = "/tmp/f.ttf"; has_cjk_coverage = false } ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (fires "CJK-007" (unique_src ())) (tag ^ ": fires")));

  run "CJK-007 clean: font with CJK" (fun tag ->
      let ctx =
        {
          (empty_ctx ()) with
          fonts = [ { path = "/tmp/f.ttf"; has_cjk_coverage = true } ];
        }
      in
      with_file_ctx ctx (fun () ->
          expect (does_not_fire "CJK-007" (unique_src ())) (tag ^ ": clean")));

  run "CJK-007 no context" (fun tag ->
      File_context.clear_file_context ();
      expect (does_not_fire "CJK-007" (unique_src ())) (tag ^ ": no ctx"));

  (* ══════════════════════════════════════════════════════════════════
     Integration: all rules with no context return None
     ══════════════════════════════════════════════════════════════════ *)

  run "All L3 rules silent without file context" (fun tag ->
      File_context.clear_file_context ();
      Log_parser.clear_log_context ();
      let results = Validators.run_all (unique_src ()) in
      let l3_ids =
        [
          "FIG-004"; "FIG-006"; "FIG-016"; "FIG-021";
          "COL-001"; "COL-002"; "COL-003"; "COL-005";
          "PDF-006"; "PDF-007"; "PDF-008"; "PDF-009";
          "PDF-011"; "PDF-012"; "COL-004"; "COL-007";
          "TIKZ-002"; "TIKZ-008"; "CJK-007";
        ]
      in
      let l3_results =
        List.filter (fun r -> List.mem (r : Validators.result).id l3_ids) results
      in
      expect (l3_results = []) (tag ^ ": none fired"));

  (* ══════════════════════════════════════════════════════════════════
     Layer mapping: all 19 rules map to L3
     ══════════════════════════════════════════════════════════════════ *)

  run "All 19 rules mapped to L3" (fun tag ->
      let l3_ids =
        [
          "FIG-004"; "FIG-006"; "FIG-016"; "FIG-021";
          "COL-001"; "COL-002"; "COL-003"; "COL-005";
          "PDF-006"; "PDF-007"; "PDF-008"; "PDF-009";
          "PDF-011"; "PDF-012"; "COL-004"; "COL-007";
          "TIKZ-002"; "TIKZ-008"; "CJK-007";
        ]
      in
      List.iter
        (fun id ->
          let ly = Validators.precondition_of_rule_id id in
          expect (ly = L3)
            (Printf.sprintf "%s: %s -> L3" tag id))
        l3_ids)

let () = finalise "validators-l3-file"
