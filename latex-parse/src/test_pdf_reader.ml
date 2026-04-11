(** Comprehensive unit tests for Pdf_reader — 40+ cases covering
    parse_pdf / read_pdf_info with programmatically generated PDFs
    from Test_binary_gen.make_pdf.

    Uses Fun.protect for temp-file cleanup.  Finalises as "pdf-reader". *)

open Latex_parse_lib
open Test_helpers

(* ── Helpers ─────────────────────────────────────────────────────────── *)

(** Write [data] to a temp file, run [f path], clean up unconditionally. *)
let with_pdf data f =
  let path = Test_binary_gen.write_to_temp_file data ".pdf" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () -> f path)

(** Convenience: make_pdf with given opts, write, read_pdf_info, return option. *)
let info_of opts =
  let data = Test_binary_gen.make_pdf opts in
  let path = Test_binary_gen.write_to_temp_file data ".pdf" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    Pdf_reader.read_pdf_info path)

(** Convenience: make_pdf with given opts, write, parse_pdf, return option. *)
let doc_of opts =
  let data = Test_binary_gen.make_pdf opts in
  let path = Test_binary_gen.write_to_temp_file data ".pdf" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    Pdf_reader.parse_pdf path)

let default = Test_binary_gen.default_pdf_opts

let () =
  (* ══════════════════════════════════════════════════════════════════════
     §1  Basic parsing
     ══════════════════════════════════════════════════════════════════════ *)
  run "minimal PDF parses successfully" (fun tag ->
      expect (doc_of default <> None) tag);

  run "minimal PDF returns page_count = 1" (fun tag ->
      match info_of default with
      | Some i -> expect (i.page_count = 1)
                    (tag ^ Printf.sprintf ": got %d" i.page_count)
      | None -> expect false (tag ^ ": None"));

  run "parse_pdf returns Some with objects" (fun tag ->
      match doc_of default with
      | Some doc -> expect (Hashtbl.length doc.objects > 0)
                      (tag ^ ": no objects")
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §2  StructTreeRoot
     ══════════════════════════════════════════════════════════════════════ *)
  run "StructTreeRoot absent by default" (fun tag ->
      match info_of default with
      | Some i -> expect (not i.has_struct_tree_root) tag
      | None -> expect false (tag ^ ": None"));

  run "StructTreeRoot present when has_struct_tree=true" (fun tag ->
      let opts = { default with has_struct_tree = true } in
      match info_of opts with
      | Some i -> expect i.has_struct_tree_root tag
      | None -> expect false (tag ^ ": None"));

  run "StructTreeRoot absent when has_struct_tree=false" (fun tag ->
      let opts = { default with has_struct_tree = false } in
      match info_of opts with
      | Some i -> expect (not i.has_struct_tree_root) tag
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §3  MarkInfo
     ══════════════════════════════════════════════════════════════════════ *)
  run "MarkInfo absent by default" (fun tag ->
      match info_of default with
      | Some i -> expect (not i.has_mark_info) tag
      | None -> expect false (tag ^ ": None"));

  run "MarkInfo marked=true" (fun tag ->
      let opts = { default with has_mark_info = true } in
      match info_of opts with
      | Some i -> expect i.has_mark_info tag
      | None -> expect false (tag ^ ": None"));

  run "MarkInfo marked=false" (fun tag ->
      let opts = { default with has_mark_info = false } in
      match info_of opts with
      | Some i -> expect (not i.has_mark_info) tag
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §4  Lang
     ══════════════════════════════════════════════════════════════════════ *)
  run "Lang absent by default" (fun tag ->
      match info_of default with
      | Some i -> expect (i.lang = None)
                    (tag ^ Printf.sprintf ": got %s"
                       (match i.lang with Some s -> s | None -> "<None>"))
      | None -> expect false (tag ^ ": None"));

  run "Lang present: en-US" (fun tag ->
      let opts = { default with has_lang = Some "en-US" } in
      match info_of opts with
      | Some i -> expect (i.lang = Some "en-US")
                    (tag ^ Printf.sprintf ": got %s"
                       (match i.lang with Some s -> s | None -> "<None>"))
      | None -> expect false (tag ^ ": None"));

  run "Lang present: de-DE" (fun tag ->
      let opts = { default with has_lang = Some "de-DE" } in
      match info_of opts with
      | Some i -> expect (i.lang = Some "de-DE") tag
      | None -> expect false (tag ^ ": None"));

  run "Lang present: fr" (fun tag ->
      let opts = { default with has_lang = Some "fr" } in
      match info_of opts with
      | Some i -> expect (i.lang = Some "fr") tag
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §5  Figures without alt
     ══════════════════════════════════════════════════════════════════════ *)
  run "figures_without_alt = 0 when no struct tree" (fun tag ->
      match info_of default with
      | Some i -> expect (i.figures_without_alt = 0)
                    (tag ^ Printf.sprintf ": got %d" i.figures_without_alt)
      | None -> expect false (tag ^ ": None"));

  run "figures_without_alt = 0 when struct tree with no figures" (fun tag ->
      let opts = { default with has_struct_tree = true;
                                figures_without_alt = 0 } in
      match info_of opts with
      | Some i -> expect (i.figures_without_alt = 0)
                    (tag ^ Printf.sprintf ": got %d" i.figures_without_alt)
      | None -> expect false (tag ^ ": None"));

  run "figures_without_alt = 1" (fun tag ->
      let opts = { default with has_struct_tree = true;
                                figures_without_alt = 1 } in
      match info_of opts with
      | Some i -> expect (i.figures_without_alt = 1)
                    (tag ^ Printf.sprintf ": got %d" i.figures_without_alt)
      | None -> expect false (tag ^ ": None"));

  run "figures_without_alt = 3" (fun tag ->
      let opts = { default with has_struct_tree = true;
                                figures_without_alt = 3 } in
      match info_of opts with
      | Some i -> expect (i.figures_without_alt = 3)
                    (tag ^ Printf.sprintf ": got %d" i.figures_without_alt)
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §6  Links without contents
     ══════════════════════════════════════════════════════════════════════ *)
  run "links_without_contents = 0 by default" (fun tag ->
      match info_of default with
      | Some i -> expect (i.links_without_contents = 0)
                    (tag ^ Printf.sprintf ": got %d" i.links_without_contents)
      | None -> expect false (tag ^ ": None"));

  run "links_without_contents = 1" (fun tag ->
      let opts = { default with links_without_contents = 1 } in
      match info_of opts with
      | Some i -> expect (i.links_without_contents = 1)
                    (tag ^ Printf.sprintf ": got %d" i.links_without_contents)
      | None -> expect false (tag ^ ": None"));

  run "links_without_contents = 4" (fun tag ->
      let opts = { default with links_without_contents = 4 } in
      match info_of opts with
      | Some i -> expect (i.links_without_contents = 4)
                    (tag ^ Printf.sprintf ": got %d" i.links_without_contents)
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §7  Fonts — embedded vs not embedded, subset detection
     ══════════════════════════════════════════════════════════════════════ *)
  run "no fonts by default" (fun tag ->
      match info_of default with
      | Some i -> expect (i.fonts = [])
                    (tag ^ Printf.sprintf ": got %d fonts" (List.length i.fonts))
      | None -> expect false (tag ^ ": None"));

  run "one embedded non-subsetted font" (fun tag ->
      let opts = { default with
                   fonts = [("Helvetica", true, false)] } in
      match info_of opts with
      | Some i ->
          let n = List.length i.fonts in
          expect (n = 1)
            (tag ^ Printf.sprintf ": expected 1 font, got %d" n);
          begin match i.fonts with
          | [(name, emb, sub)] ->
              expect (name = "Helvetica") (tag ^ ": name = " ^ name);
              expect emb (tag ^ ": expected embedded");
              expect (not sub) (tag ^ ": expected not subsetted")
          | _ -> ()
          end
      | None -> expect false (tag ^ ": None"));

  run "one non-embedded font" (fun tag ->
      let opts = { default with
                   fonts = [("TimesRoman", false, false)] } in
      match info_of opts with
      | Some i ->
          begin match i.fonts with
          | [(_, emb, _)] ->
              expect (not emb) (tag ^ ": expected not embedded")
          | _ -> expect false (tag ^ ": wrong font count")
          end
      | None -> expect false (tag ^ ": None"));

  run "subsetted font has ABCDEF+ prefix" (fun tag ->
      let opts = { default with
                   fonts = [("CMR10", true, true)] } in
      match info_of opts with
      | Some i ->
          begin match i.fonts with
          | [(name, emb, sub)] ->
              expect (String.length name > 7 && name.[6] = '+')
                (tag ^ ": expected ABCDEF+ prefix, got " ^ name);
              expect emb (tag ^ ": expected embedded");
              expect sub (tag ^ ": expected subsetted")
          | _ -> expect false (tag ^ Printf.sprintf ": wrong font count %d"
                                 (List.length i.fonts))
          end
      | None -> expect false (tag ^ ": None"));

  run "multiple fonts" (fun tag ->
      let opts = { default with
                   fonts = [("Helvetica", true, false);
                            ("Courier", false, false);
                            ("Symbol", true, true)] } in
      match info_of opts with
      | Some i ->
          expect (List.length i.fonts = 3)
            (tag ^ Printf.sprintf ": expected 3 fonts, got %d"
               (List.length i.fonts))
      | None -> expect false (tag ^ ": None"));

  run "embedded font has FontFile2" (fun tag ->
      let opts = { default with
                   fonts = [("DejaVuSans", true, false)] } in
      match info_of opts with
      | Some i ->
          begin match i.fonts with
          | [(_, emb, _)] -> expect emb (tag ^ ": not embedded")
          | _ -> expect false (tag ^ ": wrong count")
          end
      | None -> expect false (tag ^ ": None"));

  run "non-subsetted font name has no plus sign" (fun tag ->
      let opts = { default with
                   fonts = [("Palatino", true, false)] } in
      match info_of opts with
      | Some i ->
          begin match i.fonts with
          | [(name, _, sub)] ->
              expect (not sub) (tag ^ ": expected not subsetted");
              expect (not (String.contains name '+'))
                (tag ^ ": name should have no +: " ^ name)
          | _ -> expect false (tag ^ ": wrong count")
          end
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §8  Spot colours
     ══════════════════════════════════════════════════════════════════════ *)
  run "no spot colours by default" (fun tag ->
      match info_of default with
      | Some i ->
          expect (not i.has_spot_colour) (tag ^ ": has_spot_colour");
          expect (not i.has_spot_colour_vector) (tag ^ ": has_spot_colour_vector")
      | None -> expect false (tag ^ ": None"));

  run "Separation spot colour present" (fun tag ->
      let opts = { default with has_spot_colour = true;
                                has_spot_colour_vector = false } in
      match info_of opts with
      | Some i ->
          expect i.has_spot_colour (tag ^ ": expected has_spot_colour");
          expect (not i.has_spot_colour_vector)
            (tag ^ ": should not have DeviceN")
      | None -> expect false (tag ^ ": None"));

  run "DeviceN spot colour vector present" (fun tag ->
      let opts = { default with has_spot_colour = true;
                                has_spot_colour_vector = true } in
      match info_of opts with
      | Some i ->
          expect i.has_spot_colour (tag ^ ": expected has_spot_colour");
          expect i.has_spot_colour_vector
            (tag ^ ": expected has_spot_colour_vector")
      | None -> expect false (tag ^ ": None"));

  run "DeviceN implies Separation" (fun tag ->
      let opts = { default with has_spot_colour = true;
                                has_spot_colour_vector = true } in
      match info_of opts with
      | Some i ->
          expect i.has_spot_colour
            (tag ^ ": DeviceN should imply has_spot_colour")
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §9  Stream compression
     ══════════════════════════════════════════════════════════════════════ *)
  run "streams_all_compressed = true by default" (fun tag ->
      match info_of default with
      | Some i -> expect i.streams_all_compressed
                    (tag ^ ": expected true")
      | None -> expect false (tag ^ ": None"));

  run "uncompressed stream detected" (fun tag ->
      let opts = { default with streams_compressed = false } in
      match info_of opts with
      | Some i -> expect (not i.streams_all_compressed)
                    (tag ^ ": expected false")
      | None -> expect false (tag ^ ": None"));

  run "compressed streams stay true" (fun tag ->
      let opts = { default with streams_compressed = true } in
      match info_of opts with
      | Some i -> expect i.streams_all_compressed
                    (tag ^ ": expected true")
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §10  Edge cases — non-PDF, truncated, empty, encrypted
     ══════════════════════════════════════════════════════════════════════ *)
  run "non-PDF file returns None" (fun tag ->
      let data = Bytes.of_string "This is not a PDF file at all." in
      with_pdf data (fun path ->
        expect (Pdf_reader.read_pdf_info path = None) tag));

  run "empty file returns None" (fun tag ->
      let data = Bytes.empty in
      with_pdf data (fun path ->
        expect (Pdf_reader.read_pdf_info path = None) tag));

  run "truncated PDF header returns None" (fun tag ->
      let data = Bytes.of_string "%PDF" in
      with_pdf data (fun path ->
        expect (Pdf_reader.read_pdf_info path = None) tag));

  run "just %PDF-1.7 with no xref returns None" (fun tag ->
      let data = Bytes.of_string "%PDF-1.7\n" in
      with_pdf data (fun path ->
        expect (Pdf_reader.read_pdf_info path = None) tag));

  run "nonexistent file returns None" (fun tag ->
      expect (Pdf_reader.read_pdf_info "/tmp/nonexistent_pdf_42.pdf" = None)
        tag);

  run "parse_pdf on non-PDF returns None" (fun tag ->
      let data = Bytes.of_string "Hello World" in
      with_pdf data (fun path ->
        expect (Pdf_reader.parse_pdf path = None) tag));

  run "parse_pdf on empty returns None" (fun tag ->
      let data = Bytes.empty in
      with_pdf data (fun path ->
        expect (Pdf_reader.parse_pdf path = None) tag));

  run "encrypted PDF returns None" (fun tag ->
      (* Build a PDF-like blob with /Encrypt in trailer *)
      let data = Bytes.of_string (String.concat ""
        [ "%PDF-1.7\n";
          "1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n";
          "2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n";
          "3 0 obj\n<< /Type /Page /Parent 2 0 R >>\nendobj\n";
          "xref\n0 4\n";
          "0000000000 65535 f \n";
          "0000000010 00000 n \n";
          "0000000063 00000 n \n";
          "0000000120 00000 n \n";
          "trailer\n<< /Size 4 /Root 1 0 R /Encrypt << /V 2 >> >>\n";
          "startxref\n170\n%%EOF\n" ]) in
      with_pdf data (fun path ->
        expect (Pdf_reader.parse_pdf path = None) tag));

  (* ══════════════════════════════════════════════════════════════════════
     §11  Combined configurations — tagged PDF with all features
     ══════════════════════════════════════════════════════════════════════ *)
  run "fully tagged PDF: struct tree + mark info + lang" (fun tag ->
      let opts = { default with has_struct_tree = true;
                                has_mark_info = true;
                                has_lang = Some "en-GB" } in
      match info_of opts with
      | Some i ->
          expect i.has_struct_tree_root (tag ^ ": struct tree");
          expect i.has_mark_info (tag ^ ": mark info");
          expect (i.lang = Some "en-GB") (tag ^ ": lang")
      | None -> expect false (tag ^ ": None"));

  run "tagged PDF with figures and links" (fun tag ->
      let opts = { default with has_struct_tree = true;
                                figures_without_alt = 2;
                                links_without_contents = 3 } in
      match info_of opts with
      | Some i ->
          expect (i.figures_without_alt = 2)
            (tag ^ Printf.sprintf ": figs = %d" i.figures_without_alt);
          expect (i.links_without_contents = 3)
            (tag ^ Printf.sprintf ": links = %d" i.links_without_contents)
      | None -> expect false (tag ^ ": None"));

  run "full kitchen sink: all features" (fun tag ->
      let opts = { Test_binary_gen.
                   has_struct_tree = true;
                   has_mark_info = true;
                   has_lang = Some "ja";
                   figures_without_alt = 2;
                   links_without_contents = 1;
                   fonts = [("Mincho", true, true); ("Gothic", false, false)];
                   has_spot_colour = true;
                   has_spot_colour_vector = true;
                   streams_compressed = false } in
      match info_of opts with
      | Some i ->
          expect i.has_struct_tree_root (tag ^ ": struct tree");
          expect i.has_mark_info (tag ^ ": mark info");
          expect (i.lang = Some "ja") (tag ^ ": lang");
          expect (i.figures_without_alt = 2)
            (tag ^ Printf.sprintf ": figs = %d" i.figures_without_alt);
          expect (i.links_without_contents = 1)
            (tag ^ Printf.sprintf ": links = %d" i.links_without_contents);
          expect (List.length i.fonts = 2)
            (tag ^ Printf.sprintf ": font count = %d" (List.length i.fonts));
          expect i.has_spot_colour (tag ^ ": spot colour");
          expect i.has_spot_colour_vector (tag ^ ": spot colour vector");
          expect (not i.streams_all_compressed) (tag ^ ": uncompressed")
      | None -> expect false (tag ^ ": None"));

  run "tagged PDF without spot colours but with fonts" (fun tag ->
      let opts = { default with has_struct_tree = true;
                                has_mark_info = true;
                                has_lang = Some "zh";
                                fonts = [("SimSun", true, true)] } in
      match info_of opts with
      | Some i ->
          expect i.has_struct_tree_root (tag ^ ": struct tree");
          expect (not i.has_spot_colour) (tag ^ ": no spot");
          expect (List.length i.fonts = 1) (tag ^ ": 1 font")
      | None -> expect false (tag ^ ": None"));

  run "read_pdf_info roundtrips parse_pdf" (fun tag ->
      let opts = { default with has_lang = Some "es";
                                has_mark_info = true } in
      let data = Test_binary_gen.make_pdf opts in
      let path = Test_binary_gen.write_to_temp_file data ".pdf" in
      Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
        let doc_ok = Pdf_reader.parse_pdf path <> None in
        let info_ok = Pdf_reader.read_pdf_info path <> None in
        expect doc_ok (tag ^ ": parse_pdf");
        expect info_ok (tag ^ ": read_pdf_info")));

  run "page_count is 1 for single-page PDF" (fun tag ->
      let opts = { default with has_struct_tree = true } in
      match info_of opts with
      | Some i -> expect (i.page_count = 1)
                    (tag ^ Printf.sprintf ": got %d" i.page_count)
      | None -> expect false (tag ^ ": None"));

  (* ══════════════════════════════════════════════════════════════════════
     §12  Misc edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "binary garbage after %PDF header returns None" (fun tag ->
      let data = Bytes.of_string "%PDF-1.7\n\x00\x01\x02\x03" in
      with_pdf data (fun path ->
        expect (Pdf_reader.read_pdf_info path = None) tag));

  run "figures_without_alt = 0 with struct tree but zero figures" (fun tag ->
      let opts = { default with has_struct_tree = true;
                                figures_without_alt = 0 } in
      match info_of opts with
      | Some i -> expect (i.figures_without_alt = 0) tag
      | None -> expect false (tag ^ ": None"));

  run "default opts: page_label_count = 0" (fun tag ->
      match info_of default with
      | Some i -> expect (i.page_label_count = 0)
                    (tag ^ Printf.sprintf ": got %d" i.page_label_count)
      | None -> expect false (tag ^ ": None"));

  (* ── Done ──────────────────────────────────────────────────────────── *)
  finalise "pdf-reader"
