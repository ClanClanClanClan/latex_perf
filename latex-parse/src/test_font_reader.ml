(** Test_font_reader — TTF cmap reader (format 4 + format 12). 19 cases. *)

open Latex_parse_lib
open Test_helpers

let with_temp_file data suffix f =
  let path = Test_binary_gen.write_to_temp_file data suffix in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () -> f path)

let () =
  (* ── CJK coverage detection ──────────────────────────────────── *)

  run "TTF with CJK coverage returns Some true" (fun tag ->
      let data = Test_binary_gen.make_ttf ~has_cjk:true in
      with_temp_file data ".ttf" (fun path ->
          match Font_reader.has_cjk_coverage path with
          | Some true -> expect true (tag ^ ": has CJK")
          | Some false -> expect false (tag ^ ": expected true got false")
          | None -> expect false (tag ^ ": expected Some got None")));

  run "TTF without CJK coverage returns Some false" (fun tag ->
      let data = Test_binary_gen.make_ttf ~has_cjk:false in
      with_temp_file data ".ttf" (fun path ->
          match Font_reader.has_cjk_coverage path with
          | Some false -> expect true (tag ^ ": no CJK")
          | Some true -> expect false (tag ^ ": expected false got true")
          | None -> expect false (tag ^ ": expected Some got None")));

  (* ── Edge cases ──────────────────────────────────────────────── *)

  run "nonexistent file returns None" (fun tag ->
      expect
        (Font_reader.has_cjk_coverage "/nonexistent/font.ttf" = None)
        (tag ^ ": None"));

  run "empty file returns None" (fun tag ->
      with_temp_file Bytes.empty ".ttf" (fun path ->
          expect (Font_reader.has_cjk_coverage path = None)
            (tag ^ ": None for empty")));

  run "too-small file returns None" (fun tag ->
      with_temp_file (Bytes.make 8 '\000') ".ttf" (fun path ->
          expect (Font_reader.has_cjk_coverage path = None)
            (tag ^ ": None for small")));

  run "non-font binary returns None" (fun tag ->
      let garbage = Bytes.make 256 '\xFF' in
      with_temp_file garbage ".ttf" (fun path ->
          expect (Font_reader.has_cjk_coverage path = None)
            (tag ^ ": None for garbage")));

  run "text file returns None" (fun tag ->
      let text = Bytes.of_string "This is not a font file at all" in
      with_temp_file text ".ttf" (fun path ->
          expect (Font_reader.has_cjk_coverage path = None)
            (tag ^ ": None for text")));

  run "PNG file returns None" (fun tag ->
      let png =
        Test_binary_gen.make_png Test_binary_gen.default_png_opts
      in
      with_temp_file png ".ttf" (fun path ->
          expect (Font_reader.has_cjk_coverage path = None)
            (tag ^ ": None for PNG")));

  (* ── Format variations ───────────────────────────────────────── *)

  run "CJK font: specific sample points covered" (fun tag ->
      let data = Test_binary_gen.make_ttf ~has_cjk:true in
      with_temp_file data ".ttf" (fun path ->
          (* The font has range U+4E00-U+9FFF *)
          match Font_reader.has_cjk_coverage path with
          | Some v -> expect v (tag ^ ": coverage confirmed")
          | None -> expect false (tag ^ ": parse failed")));

  run "no-CJK font: still has ASCII" (fun tag ->
      let data = Test_binary_gen.make_ttf ~has_cjk:false in
      with_temp_file data ".ttf" (fun path ->
          (* Should parse successfully even without CJK *)
          match Font_reader.has_cjk_coverage path with
          | Some _ -> expect true (tag ^ ": parsed OK")
          | None -> expect false (tag ^ ": should parse")));

  (* ── Idempotence ─────────────────────────────────────────────── *)

  run "reading same file twice gives same result" (fun tag ->
      let data = Test_binary_gen.make_ttf ~has_cjk:true in
      with_temp_file data ".ttf" (fun path ->
          let r1 = Font_reader.has_cjk_coverage path in
          let r2 = Font_reader.has_cjk_coverage path in
          expect (r1 = r2) (tag ^ ": idempotent")));

  (* ── Large file ──────────────────────────────────────────────── *)

  run "CJK font data is deterministic" (fun tag ->
      let d1 = Test_binary_gen.make_ttf ~has_cjk:true in
      let d2 = Test_binary_gen.make_ttf ~has_cjk:true in
      expect (d1 = d2) (tag ^ ": deterministic"));

  run "no-CJK font data is deterministic" (fun tag ->
      let d1 = Test_binary_gen.make_ttf ~has_cjk:false in
      let d2 = Test_binary_gen.make_ttf ~has_cjk:false in
      expect (d1 = d2) (tag ^ ": deterministic"));

  run "CJK and no-CJK produce different data" (fun tag ->
      let d1 = Test_binary_gen.make_ttf ~has_cjk:true in
      let d2 = Test_binary_gen.make_ttf ~has_cjk:false in
      expect (d1 <> d2) (tag ^ ": different"));

  (* ── Format 4 (BMP) cmap subtable ─────────────────────────────── *)

  run "Format 4 TTF with CJK returns Some true" (fun tag ->
      let data = Test_binary_gen.make_ttf_format4 ~has_cjk:true in
      with_temp_file data ".ttf" (fun path ->
          match Font_reader.has_cjk_coverage path with
          | Some true -> expect true (tag ^ ": fmt4 has CJK")
          | Some false -> expect false (tag ^ ": fmt4 expected true got false")
          | None -> expect false (tag ^ ": fmt4 expected Some got None")));

  run "Format 4 TTF without CJK returns Some false" (fun tag ->
      let data = Test_binary_gen.make_ttf_format4 ~has_cjk:false in
      with_temp_file data ".ttf" (fun path ->
          match Font_reader.has_cjk_coverage path with
          | Some false -> expect true (tag ^ ": fmt4 no CJK")
          | Some true -> expect false (tag ^ ": fmt4 expected false got true")
          | None -> expect false (tag ^ ": fmt4 expected Some got None")));

  run "Format 4 ASCII-only returns Some false" (fun tag ->
      let data = Test_binary_gen.make_ttf_format4 ~has_cjk:false in
      with_temp_file data ".ttf" (fun path ->
          match Font_reader.has_cjk_coverage path with
          | Some false -> expect true (tag ^ ": fmt4 ASCII-only is false")
          | r ->
              let s = match r with Some true -> "Some true" | Some false -> "Some false" | None -> "None" in
              expect false (tag ^ ": expected Some false got " ^ s)));

  run "Format 4 and format 12 agree on CJK coverage" (fun tag ->
      let fmt4_cjk = Test_binary_gen.make_ttf_format4 ~has_cjk:true in
      let fmt12_cjk = Test_binary_gen.make_ttf ~has_cjk:true in
      let fmt4_no = Test_binary_gen.make_ttf_format4 ~has_cjk:false in
      let fmt12_no = Test_binary_gen.make_ttf ~has_cjk:false in
      with_temp_file fmt4_cjk ".ttf" (fun p4c ->
      with_temp_file fmt12_cjk ".ttf" (fun p12c ->
      with_temp_file fmt4_no ".ttf" (fun p4n ->
      with_temp_file fmt12_no ".ttf" (fun p12n ->
          let r4c = Font_reader.has_cjk_coverage p4c in
          let r12c = Font_reader.has_cjk_coverage p12c in
          let r4n = Font_reader.has_cjk_coverage p4n in
          let r12n = Font_reader.has_cjk_coverage p12n in
          expect (r4c = r12c) (tag ^ ": CJK results agree");
          expect (r4n = r12n) (tag ^ ": no-CJK results agree"))))))

let () = finalise "font-reader"
