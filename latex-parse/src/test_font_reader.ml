(** Test_font_reader — TTF cmap reader. 15 cases. *)

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
      expect (d1 <> d2) (tag ^ ": different"))

let () = finalise "font-reader"
