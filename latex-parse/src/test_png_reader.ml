(** Comprehensive tests for the Png_reader module.

    Generates synthetic PNG files using Test_binary_gen, writes them to temp
    files, reads them back with Png_reader.read_png_info, and validates the
    parsed metadata. 35+ test cases covering IHDR fields, pHYs DPI, tRNS, iCCP,
    sRGB, PLTE, edge cases, and combined chunks. *)

open Latex_parse_lib
open Test_helpers

(** Write [data] to a temp file, run [f path], then remove the file. Cleanup
    runs even when [f] raises. *)
let with_temp_png data f =
  let path = Test_binary_gen.write_to_temp_file data ".png" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () -> f path)

(** Helper: unwrap [Some] or fail the test. *)
let require_some tag = function
  | Some info -> info
  | None ->
      expect false (tag ^ ": expected Some, got None");
      (* Return a dummy so subsequent checks still run and report. *)
      {
        Png_reader.width = -1;
        height = -1;
        bit_depth = -1;
        color_type = -1;
        has_trns = false;
        phys_x = -1;
        phys_y = -1;
        phys_unit = -1;
        has_iccp = false;
        iccp_name = "";
        has_srgb = false;
        plte_entries = -1;
      }

let () =
  (* ════════════════════════════════════════════════════════════════════ 1.
     Basic IHDR parsing — width / height
     ════════════════════════════════════════════════════════════════════ *)
  run "IHDR: default width/height (100x100)" (fun tag ->
      let png = Test_binary_gen.make_png Test_binary_gen.default_png_opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.width = 100) (tag ^ ": width");
          expect (info.height = 100) (tag ^ ": height")));

  run "IHDR: small 1x1" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with width = 1; height = 1 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.width = 1) (tag ^ ": width");
          expect (info.height = 1) (tag ^ ": height")));

  run "IHDR: large 4096x2160" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with width = 4096; height = 2160 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.width = 4096) (tag ^ ": width");
          expect (info.height = 2160) (tag ^ ": height")));

  run "IHDR: non-square 640x480" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with width = 640; height = 480 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.width = 640) (tag ^ ": width");
          expect (info.height = 480) (tag ^ ": height")));

  (* ════════════════════════════════════════════════════════════════════ 2.
     Color types (0, 2, 3, 4, 6)
     ════════════════════════════════════════════════════════════════════ *)
  run "IHDR: color_type 0 (grayscale)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 0; bit_depth = 8 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.color_type = 0) (tag ^ ": color_type")));

  run "IHDR: color_type 2 (truecolor)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 2; bit_depth = 8 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.color_type = 2) (tag ^ ": color_type")));

  run "IHDR: color_type 3 (indexed)" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 3;
          bit_depth = 8;
          plte_size = 16;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.color_type = 3) (tag ^ ": color_type")));

  run "IHDR: color_type 4 (grayscale+alpha)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 4; bit_depth = 8 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.color_type = 4) (tag ^ ": color_type")));

  run "IHDR: color_type 6 (truecolor+alpha)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 6; bit_depth = 8 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.color_type = 6) (tag ^ ": color_type")));

  (* ════════════════════════════════════════════════════════════════════ 3. Bit
     depths
     ════════════════════════════════════════════════════════════════════ *)
  run "IHDR: bit_depth 1 (grayscale)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 0; bit_depth = 1 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.bit_depth = 1) (tag ^ ": bit_depth")));

  run "IHDR: bit_depth 4 (grayscale)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 0; bit_depth = 4 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.bit_depth = 4) (tag ^ ": bit_depth")));

  run "IHDR: bit_depth 8 (truecolor)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 2; bit_depth = 8 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.bit_depth = 8) (tag ^ ": bit_depth")));

  run "IHDR: bit_depth 16 (truecolor)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 2; bit_depth = 16 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.bit_depth = 16) (tag ^ ": bit_depth")));

  (* ════════════════════════════════════════════════════════════════════ 4.
     pHYs — DPI / resolution metadata
     ════════════════════════════════════════════════════════════════════ *)
  run "pHYs: 72 DPI" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with dpi = 72 } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          let expected_ppm = int_of_float (72.0 /. 0.0254) in
          expect (info.phys_x = expected_ppm) (tag ^ ": phys_x");
          expect (info.phys_y = expected_ppm) (tag ^ ": phys_y");
          expect (info.phys_unit = 1) (tag ^ ": phys_unit = meter")));

  run "pHYs: 300 DPI" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with dpi = 300 } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          let expected_ppm = int_of_float (300.0 /. 0.0254) in
          expect (info.phys_x = expected_ppm) (tag ^ ": phys_x");
          expect (info.phys_y = expected_ppm) (tag ^ ": phys_y");
          expect (info.phys_unit = 1) (tag ^ ": phys_unit = meter")));

  run "pHYs: 96 DPI (screen)" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with dpi = 96 } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          let expected_ppm = int_of_float (96.0 /. 0.0254) in
          expect (info.phys_x = expected_ppm) (tag ^ ": phys_x");
          expect (info.phys_y = expected_ppm) (tag ^ ": phys_y")));

  run "pHYs: absent (dpi = 0)" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with dpi = 0 } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.phys_x = 0) (tag ^ ": phys_x = 0");
          expect (info.phys_y = 0) (tag ^ ": phys_y = 0");
          expect (info.phys_unit = 0) (tag ^ ": phys_unit = 0")));

  (* ════════════════════════════════════════════════════════════════════ 5.
     tRNS — transparency chunk
     ════════════════════════════════════════════════════════════════════ *)
  run "tRNS: present" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with has_trns = true } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_trns (tag ^ ": has_trns = true")));

  run "tRNS: absent" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with has_trns = false } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (not info.has_trns) (tag ^ ": has_trns = false")));

  run "tRNS: present on grayscale" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 0;
          has_trns = true;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_trns (tag ^ ": has_trns = true")));

  run "tRNS: present on indexed color" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 3;
          plte_size = 4;
          has_trns = true;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_trns (tag ^ ": has_trns = true")));

  (* ════════════════════════════════════════════════════════════════════ 6.
     iCCP — embedded ICC profile
     ════════════════════════════════════════════════════════════════════ *)
  run "iCCP: present with name" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          has_iccp = true;
          iccp_name = "sRGB IEC61966-2.1";
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_iccp (tag ^ ": has_iccp = true");
          expect
            (info.iccp_name = "sRGB IEC61966-2.1")
            (tag ^ ": iccp_name = " ^ info.iccp_name)));

  run "iCCP: short name" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          has_iccp = true;
          iccp_name = "P3";
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_iccp (tag ^ ": has_iccp = true");
          expect (info.iccp_name = "P3") (tag ^ ": iccp_name")));

  run "iCCP: absent" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with has_iccp = false } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (not info.has_iccp) (tag ^ ": has_iccp = false");
          expect (info.iccp_name = "") (tag ^ ": iccp_name empty")));

  (* ════════════════════════════════════════════════════════════════════ 7.
     sRGB — standard RGB rendering intent
     ════════════════════════════════════════════════════════════════════ *)
  run "sRGB: present" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with has_srgb = true } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_srgb (tag ^ ": has_srgb = true")));

  run "sRGB: absent" (fun tag ->
      let opts = { Test_binary_gen.default_png_opts with has_srgb = false } in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (not info.has_srgb) (tag ^ ": has_srgb = false")));

  (* ════════════════════════════════════════════════════════════════════ 8.
     PLTE — palette entries
     ════════════════════════════════════════════════════════════════════ *)
  run "PLTE: 1 entry" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 3;
          bit_depth = 8;
          plte_size = 1;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.plte_entries = 1) (tag ^ ": plte_entries")));

  run "PLTE: 128 entries" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 3;
          bit_depth = 8;
          plte_size = 128;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.plte_entries = 128) (tag ^ ": plte_entries")));

  run "PLTE: 256 entries (max)" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 3;
          bit_depth = 8;
          plte_size = 256;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.plte_entries = 256) (tag ^ ": plte_entries")));

  run "PLTE: absent (truecolor, no palette)" (fun tag ->
      let opts =
        { Test_binary_gen.default_png_opts with color_type = 2; plte_size = 0 }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.plte_entries = 0) (tag ^ ": plte_entries = 0")));

  (* ════════════════════════════════════════════════════════════════════ 9.
     Edge cases — malformed or non-PNG input
     ════════════════════════════════════════════════════════════════════ *)
  run "edge: non-PNG file returns None" (fun tag ->
      let data = Bytes.of_string "This is not a PNG file at all." in
      with_temp_png data (fun path ->
          let result = Png_reader.read_png_info path in
          expect (result = None) (tag ^ ": expected None")));

  run "edge: empty file returns None" (fun tag ->
      let data = Bytes.empty in
      with_temp_png data (fun path ->
          let result = Png_reader.read_png_info path in
          expect (result = None) (tag ^ ": expected None")));

  run "edge: truncated after magic returns None" (fun tag ->
      let data = Bytes.of_string "\137PNG\r\n\026\n" in
      with_temp_png data (fun path ->
          let result = Png_reader.read_png_info path in
          expect (result = None) (tag ^ ": expected None")));

  run "edge: truncated mid-IHDR returns None" (fun tag ->
      (* PNG magic (8 bytes) + partial IHDR chunk header (8 bytes) but no
         data *)
      let data = Bytes.create 20 in
      Bytes.blit_string "\137PNG\r\n\026\n" 0 data 0 8;
      (* chunk length = 13 *)
      Bytes.set data 8 '\000';
      Bytes.set data 9 '\000';
      Bytes.set data 10 '\000';
      Bytes.set data 11 '\013';
      (* chunk type = IHDR *)
      Bytes.blit_string "IHDR" 0 data 12 4;
      (* Only 4 bytes of IHDR data instead of 13 *)
      Bytes.set data 16 '\000';
      Bytes.set data 17 '\000';
      Bytes.set data 18 '\000';
      Bytes.set data 19 '\001';
      with_temp_png data (fun path ->
          let result = Png_reader.read_png_info path in
          expect (result = None) (tag ^ ": expected None")));

  run "edge: JPEG file returns None" (fun tag ->
      let data = Bytes.of_string "\xFF\xD8\xFF\xE0\x00\x10JFIF\x00" in
      with_temp_png data (fun path ->
          let result = Png_reader.read_png_info path in
          expect (result = None) (tag ^ ": expected None")));

  run "edge: nonexistent path returns None" (fun tag ->
      let result =
        Png_reader.read_png_info "/tmp/nonexistent_test_png_42.png"
      in
      expect (result = None) (tag ^ ": expected None"));

  (* ════════════════════════════════════════════════════════════════════ 10.
     Combined — multiple optional chunks simultaneously
     ════════════════════════════════════════════════════════════════════ *)
  run "combined: sRGB + tRNS + pHYs 150dpi" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          has_srgb = true;
          has_trns = true;
          dpi = 150;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_srgb (tag ^ ": has_srgb");
          expect info.has_trns (tag ^ ": has_trns");
          let expected_ppm = int_of_float (150.0 /. 0.0254) in
          expect (info.phys_x = expected_ppm) (tag ^ ": phys_x");
          expect (info.phys_unit = 1) (tag ^ ": phys_unit")));

  run "combined: iCCP + PLTE + tRNS (indexed)" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 3;
          bit_depth = 8;
          plte_size = 64;
          has_iccp = true;
          iccp_name = "AdobeRGB";
          has_trns = true;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect info.has_iccp (tag ^ ": has_iccp");
          expect (info.iccp_name = "AdobeRGB") (tag ^ ": iccp_name");
          expect (info.plte_entries = 64) (tag ^ ": plte_entries");
          expect info.has_trns (tag ^ ": has_trns");
          expect (info.color_type = 3) (tag ^ ": color_type")));

  run "combined: all optional chunks enabled" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          width = 800;
          height = 600;
          color_type = 3;
          plte_size = 32;
          dpi = 300;
          has_trns = true;
          has_iccp = true;
          iccp_name = "DisplayP3";
          has_srgb = true;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.width = 800) (tag ^ ": width");
          expect (info.height = 600) (tag ^ ": height");
          expect (info.color_type = 3) (tag ^ ": color_type");
          expect (info.bit_depth = 8) (tag ^ ": bit_depth");
          expect (info.plte_entries = 32) (tag ^ ": plte_entries");
          let expected_ppm = int_of_float (300.0 /. 0.0254) in
          expect (info.phys_x = expected_ppm) (tag ^ ": phys_x");
          expect (info.phys_y = expected_ppm) (tag ^ ": phys_y");
          expect (info.phys_unit = 1) (tag ^ ": phys_unit");
          expect info.has_trns (tag ^ ": has_trns");
          expect info.has_iccp (tag ^ ": has_iccp");
          expect (info.iccp_name = "DisplayP3") (tag ^ ": iccp_name");
          expect info.has_srgb (tag ^ ": has_srgb")));

  run "combined: grayscale+alpha 16-bit, 600 DPI, no optional" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          width = 2048;
          height = 1024;
          color_type = 4;
          bit_depth = 16;
          dpi = 600;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.width = 2048) (tag ^ ": width");
          expect (info.height = 1024) (tag ^ ": height");
          expect (info.color_type = 4) (tag ^ ": color_type");
          expect (info.bit_depth = 16) (tag ^ ": bit_depth");
          let expected_ppm = int_of_float (600.0 /. 0.0254) in
          expect (info.phys_x = expected_ppm) (tag ^ ": phys_x");
          expect (not info.has_trns) (tag ^ ": no trns");
          expect (not info.has_iccp) (tag ^ ": no iccp");
          expect (not info.has_srgb) (tag ^ ": no srgb");
          expect (info.plte_entries = 0) (tag ^ ": no plte")));

  run "combined: truecolor+alpha sRGB only" (fun tag ->
      let opts =
        {
          Test_binary_gen.default_png_opts with
          color_type = 6;
          bit_depth = 8;
          has_srgb = true;
        }
      in
      let png = Test_binary_gen.make_png opts in
      with_temp_png png (fun path ->
          let info = require_some tag (Png_reader.read_png_info path) in
          expect (info.color_type = 6) (tag ^ ": color_type");
          expect info.has_srgb (tag ^ ": has_srgb");
          expect (not info.has_iccp) (tag ^ ": no iccp");
          expect (not info.has_trns) (tag ^ ": no trns");
          expect (info.plte_entries = 0) (tag ^ ": no plte")));

  ()

let () = finalise "png-reader"
