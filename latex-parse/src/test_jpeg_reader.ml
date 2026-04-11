(* ══════════════════════════════════════════════════════════════════════
   test_jpeg_reader — comprehensive tests for Jpeg_reader.read_jpeg_info

   30+ test cases covering SOF0 dimensions, component counts, APP0 JFIF
   DPI (units 1 & 2), APP2 ICC profile detection and color space, APP14
   Adobe transform values, missing markers, edge cases (non-JPEG,
   truncated, SOI+EOI only), and combined markers.
   ══════════════════════════════════════════════════════════════════════ *)

open Latex_parse_lib
open Test_helpers

(** Write bytes to a temp .jpg, run [f path], clean up. *)
let with_jpeg_file (data : bytes) (f : string -> unit) : unit =
  let path = Test_binary_gen.write_to_temp_file data ".jpg" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () -> f path)

(** Convenience: generate JPEG from opts, write to temp file, run [f path]. *)
let with_jpeg (opts : Test_binary_gen.jpeg_opts) (f : string -> unit) : unit =
  with_jpeg_file (Test_binary_gen.make_jpeg opts) f

let () =
  (* ════════════════════════════════════════════════════════════════════
     1. SOF0 dimensions — various sizes
     ════════════════════════════════════════════════════════════════════ *)

  run "SOF0: default 100x100" (fun tag ->
    with_jpeg Test_binary_gen.default_jpeg_opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some, got None")
      | Some info ->
        expect (info.width = 100) (tag ^ ": width");
        expect (info.height = 100) (tag ^ ": height")));

  run "SOF0: 1x1 minimum" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_width = 1; j_height = 1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 1) (tag ^ ": width=1");
        expect (info.height = 1) (tag ^ ": height=1")));

  run "SOF0: wide 4000x100" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_width = 4000; j_height = 100 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 4000) (tag ^ ": width=4000");
        expect (info.height = 100) (tag ^ ": height=100")));

  run "SOF0: tall 100x3000" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_width = 100; j_height = 3000 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 100) (tag ^ ": width=100");
        expect (info.height = 3000) (tag ^ ": height=3000")));

  run "SOF0: large 8192x8192" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_width = 8192; j_height = 8192 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 8192) (tag ^ ": width=8192");
        expect (info.height = 8192) (tag ^ ": height=8192")));

  run "SOF0: max u16 width 65535" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_width = 65535; j_height = 1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 65535) (tag ^ ": width=65535")));

  (* ════════════════════════════════════════════════════════════════════
     2. Component counts: 1 (gray), 3 (YCbCr), 4 (CMYK)
     ════════════════════════════════════════════════════════════════════ *)

  run "components: 1 (grayscale)" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_components = 1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.components = 1) (tag ^ ": components=1")));

  run "components: 3 (YCbCr)" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_components = 3 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.components = 3) (tag ^ ": components=3")));

  run "components: 4 (CMYK)" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_components = 4 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.components = 4) (tag ^ ": components=4")));

  (* ════════════════════════════════════════════════════════════════════
     3. APP0 JFIF DPI — units=1 (dots per inch)
     ════════════════════════════════════════════════════════════════════ *)

  run "JFIF DPI: 72" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_dpi = 72 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.dpi_x = 72.0) (tag ^ ": dpi_x=72");
        expect (info.dpi_y = 72.0) (tag ^ ": dpi_y=72")));

  run "JFIF DPI: 300" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_dpi = 300 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.dpi_x = 300.0) (tag ^ ": dpi_x=300");
        expect (info.dpi_y = 300.0) (tag ^ ": dpi_y=300")));

  run "JFIF DPI: 600" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_dpi = 600 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.dpi_x = 600.0) (tag ^ ": dpi_x=600");
        expect (info.dpi_y = 600.0) (tag ^ ": dpi_y=600")));

  (* ── APP0 JFIF DPI — units=2 (dots per cm) ─────────────────────────
     The generator only supports units=1, so we craft raw bytes for
     units=2 to test the reader's cm-to-inch conversion. *)

  run "JFIF DPI: units=2 (dots/cm) 118 -> ~300 DPI" (fun tag ->
    (* Build a minimal JPEG: SOI + APP0(units=2, 118dpcm) + SOF0 + EOI *)
    let put_u16_be buf off v =
      Bytes.set buf off (Char.chr ((v lsr 8) land 0xFF));
      Bytes.set buf (off + 1) (Char.chr (v land 0xFF))
    in
    (* SOI *)
    let soi = Bytes.of_string "\xFF\xD8" in
    (* APP0 with units=2 *)
    let app0 = Bytes.create 18 in
    Bytes.set app0 0 '\xFF';
    Bytes.set app0 1 '\xE0';
    put_u16_be app0 2 16;
    Bytes.blit_string "JFIF\000" 0 app0 4 5;
    Bytes.set app0 9 '\001';
    Bytes.set app0 10 '\001';
    Bytes.set app0 11 '\002';  (* units = dots per cm *)
    put_u16_be app0 12 118;   (* X density *)
    put_u16_be app0 14 118;   (* Y density *)
    Bytes.set app0 16 '\000';
    Bytes.set app0 17 '\000';
    (* SOF0: 1x1, 3 components *)
    let sof = Bytes.create 19 in
    Bytes.set sof 0 '\xFF';
    Bytes.set sof 1 '\xC0';
    put_u16_be sof 2 17;      (* segment length *)
    Bytes.set sof 4 '\x08';   (* precision *)
    put_u16_be sof 5 1;       (* height *)
    put_u16_be sof 7 1;       (* width *)
    Bytes.set sof 9 (Char.chr 3);
    for i = 0 to 2 do
      let off = 10 + i * 3 in
      Bytes.set sof off (Char.chr (i + 1));
      Bytes.set sof (off + 1) '\x11';
      Bytes.set sof (off + 2) '\x00'
    done;
    let eoi = Bytes.of_string "\xFF\xD9" in
    let total = 2 + 18 + 19 + 2 in
    let data = Bytes.create total in
    Bytes.blit soi 0 data 0 2;
    Bytes.blit app0 0 data 2 18;
    Bytes.blit sof 0 data 20 19;
    Bytes.blit eoi 0 data 39 2;
    with_jpeg_file data (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        (* 118 dots/cm * 2.54 = 299.72 *)
        let expected = 118.0 *. 2.54 in
        expect (abs_float (info.dpi_x -. expected) < 0.01)
          (Printf.sprintf "%s: dpi_x=%.2f expected ~%.2f" tag info.dpi_x expected);
        expect (abs_float (info.dpi_y -. expected) < 0.01)
          (Printf.sprintf "%s: dpi_y=%.2f expected ~%.2f" tag info.dpi_y expected)));

  (* ════════════════════════════════════════════════════════════════════
     4. APP2 ICC profile detection and color space
     ════════════════════════════════════════════════════════════════════ *)

  run "ICC: RGB color space detected" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with
                 j_has_icc = true; j_icc_color_space = "RGB " } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect info.has_icc_profile (tag ^ ": has_icc=true");
        expect (info.icc_color_space = `RGB) (tag ^ ": icc=RGB")));

  run "ICC: CMYK color space detected" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with
                 j_has_icc = true; j_icc_color_space = "CMYK" } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect info.has_icc_profile (tag ^ ": has_icc=true");
        expect (info.icc_color_space = `CMYK) (tag ^ ": icc=CMYK")));

  run "ICC: GRAY color space detected" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with
                 j_has_icc = true; j_icc_color_space = "GRAY" } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect info.has_icc_profile (tag ^ ": has_icc=true");
        expect (info.icc_color_space = `Gray) (tag ^ ": icc=Gray")));

  run "ICC: unknown color space" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with
                 j_has_icc = true; j_icc_color_space = "XYZ " } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect info.has_icc_profile (tag ^ ": has_icc=true");
        expect (info.icc_color_space = `Unknown) (tag ^ ": icc=Unknown")));

  (* ════════════════════════════════════════════════════════════════════
     5. APP14 Adobe marker with transform values 0, 1, 2
     ════════════════════════════════════════════════════════════════════ *)

  run "Adobe: transform=0 (CMYK)" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_adobe_transform = 0 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.adobe_color_transform = 0) (tag ^ ": adobe=0")));

  run "Adobe: transform=1 (YCbCr)" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_adobe_transform = 1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.adobe_color_transform = 1) (tag ^ ": adobe=1")));

  run "Adobe: transform=2 (YCCK)" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_adobe_transform = 2 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.adobe_color_transform = 2) (tag ^ ": adobe=2")));

  (* ════════════════════════════════════════════════════════════════════
     6. Missing markers — defaults when absent
     ════════════════════════════════════════════════════════════════════ *)

  run "no JFIF: DPI defaults to 0.0" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_dpi = 0 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.dpi_x = 0.0) (tag ^ ": dpi_x=0");
        expect (info.dpi_y = 0.0) (tag ^ ": dpi_y=0")));

  run "no ICC: has_icc_profile = false" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_has_icc = false } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (not info.has_icc_profile) (tag ^ ": has_icc=false");
        expect (info.icc_color_space = `Unknown) (tag ^ ": icc=Unknown")));

  run "no Adobe: adobe_color_transform = -1" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with j_adobe_transform = -1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.adobe_color_transform = -1) (tag ^ ": adobe=-1")));

  run "bare minimum: no JFIF, no ICC, no Adobe" (fun tag ->
    let opts = { Test_binary_gen.default_jpeg_opts with
                 j_dpi = 0; j_has_icc = false; j_adobe_transform = -1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.dpi_x = 0.0) (tag ^ ": dpi_x=0");
        expect (not info.has_icc_profile) (tag ^ ": no icc");
        expect (info.adobe_color_transform = -1) (tag ^ ": no adobe")));

  (* ════════════════════════════════════════════════════════════════════
     7. Edge cases
     ════════════════════════════════════════════════════════════════════ *)

  run "non-JPEG file: returns None" (fun tag ->
    let data = Bytes.of_string "This is not a JPEG file at all." in
    with_jpeg_file data (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": not-JPEG -> None")));

  run "PNG file: returns None" (fun tag ->
    let png = Test_binary_gen.make_png Test_binary_gen.default_png_opts in
    with_jpeg_file png (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": PNG -> None")));

  run "empty file: returns None" (fun tag ->
    with_jpeg_file Bytes.empty (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": empty -> None")));

  run "truncated: only SOI marker" (fun tag ->
    let data = Bytes.of_string "\xFF\xD8" in
    with_jpeg_file data (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": SOI-only -> None")));

  run "SOI + EOI only: no SOF -> None" (fun tag ->
    let data = Bytes.of_string "\xFF\xD8\xFF\xD9" in
    with_jpeg_file data (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": SOI+EOI -> None")));

  run "truncated SOF0: segment too short" (fun tag ->
    (* SOI + start of SOF0 marker but truncated payload *)
    let data = Bytes.of_string "\xFF\xD8\xFF\xC0\x00\x05\x08" in
    with_jpeg_file data (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": truncated SOF0 -> None")));

  run "nonexistent file: returns None" (fun tag ->
    let result = Jpeg_reader.read_jpeg_info "/nonexistent/path/to/file.jpg" in
    expect (result = None) (tag ^ ": nonexistent -> None"));

  run "single byte file: returns None" (fun tag ->
    with_jpeg_file (Bytes.of_string "\xFF") (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": 1-byte -> None")));

  run "three bytes (SOI + partial): returns None" (fun tag ->
    with_jpeg_file (Bytes.of_string "\xFF\xD8\xFF") (fun path ->
      let result = Jpeg_reader.read_jpeg_info path in
      expect (result = None) (tag ^ ": 3-byte -> None")));

  (* ════════════════════════════════════════════════════════════════════
     8. Combined: JPEG with all markers present
     ════════════════════════════════════════════════════════════════════ *)

  run "combined: all markers (JFIF + ICC + Adobe + SOF0)" (fun tag ->
    let opts = { Test_binary_gen.j_width = 640; j_height = 480;
                 j_components = 3; j_dpi = 300;
                 j_has_icc = true; j_icc_color_space = "RGB ";
                 j_adobe_transform = 1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 640) (tag ^ ": width=640");
        expect (info.height = 480) (tag ^ ": height=480");
        expect (info.components = 3) (tag ^ ": components=3");
        expect (info.dpi_x = 300.0) (tag ^ ": dpi_x=300");
        expect (info.dpi_y = 300.0) (tag ^ ": dpi_y=300");
        expect info.has_icc_profile (tag ^ ": has_icc=true");
        expect (info.icc_color_space = `RGB) (tag ^ ": icc=RGB");
        expect (info.adobe_color_transform = 1) (tag ^ ": adobe=1")));

  run "combined: CMYK with ICC and Adobe transform=2" (fun tag ->
    let opts = { Test_binary_gen.j_width = 1200; j_height = 800;
                 j_components = 4; j_dpi = 150;
                 j_has_icc = true; j_icc_color_space = "CMYK";
                 j_adobe_transform = 2 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 1200) (tag ^ ": width=1200");
        expect (info.height = 800) (tag ^ ": height=800");
        expect (info.components = 4) (tag ^ ": components=4");
        expect (info.dpi_x = 150.0) (tag ^ ": dpi_x=150");
        expect info.has_icc_profile (tag ^ ": has_icc=true");
        expect (info.icc_color_space = `CMYK) (tag ^ ": icc=CMYK");
        expect (info.adobe_color_transform = 2) (tag ^ ": adobe=2")));

  run "combined: grayscale with Gray ICC, no Adobe" (fun tag ->
    let opts = { Test_binary_gen.j_width = 256; j_height = 256;
                 j_components = 1; j_dpi = 96;
                 j_has_icc = true; j_icc_color_space = "GRAY";
                 j_adobe_transform = -1 } in
    with_jpeg opts (fun path ->
      match Jpeg_reader.read_jpeg_info path with
      | None -> expect false (tag ^ ": expected Some")
      | Some info ->
        expect (info.width = 256) (tag ^ ": width=256");
        expect (info.height = 256) (tag ^ ": height=256");
        expect (info.components = 1) (tag ^ ": components=1");
        expect (info.dpi_x = 96.0) (tag ^ ": dpi_x=96");
        expect info.has_icc_profile (tag ^ ": has_icc=true");
        expect (info.icc_color_space = `Gray) (tag ^ ": icc=Gray");
        expect (info.adobe_color_transform = -1) (tag ^ ": adobe=-1")));

  (* ════════════════════════════════════════════════════════════════════ *)
  finalise "jpeg_reader"
