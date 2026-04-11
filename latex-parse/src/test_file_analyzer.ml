(** Test_file_analyzer — path extraction and file resolution. 20+ cases. *)

open Latex_parse_lib
open Test_helpers

let () =
  (* ══════════════════════════════════════════════════════════════
     \includegraphics path extraction
     ══════════════════════════════════════════════════════════════ *)

  run "extract simple path" (fun tag ->
      let paths =
        File_analyzer.extract_includegraphics_paths
          {|\includegraphics{foo.png}|}
      in
      expect (paths = [ "foo.png" ]) (tag ^ ": foo.png"));

  run "extract path with options" (fun tag ->
      let paths =
        File_analyzer.extract_includegraphics_paths
          {|\includegraphics[width=0.5\textwidth]{bar.jpg}|}
      in
      expect (paths = [ "bar.jpg" ]) (tag ^ ": bar.jpg"));

  run "extract multiple paths" (fun tag ->
      let src =
        {|\includegraphics{a.png}
Some text
\includegraphics[scale=0.8]{b.pdf}
More text
\includegraphics{c.jpg}|}
      in
      let paths = File_analyzer.extract_includegraphics_paths src in
      expect (List.length paths = 3) (tag ^ ": 3 paths");
      expect (List.nth paths 0 = "a.png") (tag ^ ": first=a.png");
      expect (List.nth paths 1 = "b.pdf") (tag ^ ": second=b.pdf");
      expect (List.nth paths 2 = "c.jpg") (tag ^ ": third=c.jpg"));

  run "extract path without extension" (fun tag ->
      let paths =
        File_analyzer.extract_includegraphics_paths
          {|\includegraphics{diagram}|}
      in
      expect (paths = [ "diagram" ]) (tag ^ ": diagram"));

  run "extract nested in figure env" (fun tag ->
      let src =
        {|\begin{figure}
  \centering
  \includegraphics[width=\linewidth]{img/photo.png}
  \caption{A photo}
\end{figure}|}
      in
      let paths = File_analyzer.extract_includegraphics_paths src in
      expect (paths = [ "img/photo.png" ]) (tag ^ ": img/photo.png"));

  run "no includegraphics" (fun tag ->
      let paths =
        File_analyzer.extract_includegraphics_paths
          "Hello world, no graphics here."
      in
      expect (paths = []) (tag ^ ": empty"));

  run "path with subdirectory" (fun tag ->
      let paths =
        File_analyzer.extract_includegraphics_paths
          {|\includegraphics{figures/chart.pdf}|}
      in
      expect (paths = [ "figures/chart.pdf" ]) (tag ^ ": figures/chart.pdf"));

  (* ══════════════════════════════════════════════════════════════
     \graphicspath extraction
     ══════════════════════════════════════════════════════════════ *)

  run "extract graphicspath single dir" (fun tag ->
      let dirs =
        File_analyzer.extract_graphicspath
          {|\graphicspath{{figures/}}|}
      in
      expect (dirs = [ "figures/" ]) (tag ^ ": figures/"));

  run "extract graphicspath multiple dirs" (fun tag ->
      let src =
        {|\graphicspath{{figures/}}
\graphicspath{{img/}}|}
      in
      let dirs = File_analyzer.extract_graphicspath src in
      expect (List.length dirs = 2) (tag ^ ": 2 dirs");
      expect (List.nth dirs 0 = "figures/") (tag ^ ": first=figures/");
      expect (List.nth dirs 1 = "img/") (tag ^ ": second=img/"));

  run "no graphicspath" (fun tag ->
      let dirs =
        File_analyzer.extract_graphicspath "No graphics path here."
      in
      expect (dirs = []) (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════
     Full analyze_files
     ══════════════════════════════════════════════════════════════ *)

  run "empty source produces empty analysis" (fun tag ->
      let ctx = File_analyzer.analyze_files ~base_dir:"/tmp" ~source:"" () in
      expect (ctx.images = []) (tag ^ ": no images");
      expect (ctx.pdfs = []) (tag ^ ": no pdfs");
      expect (ctx.fonts = []) (tag ^ ": no fonts");
      expect (ctx.doc_class = "") (tag ^ ": no docclass"));

  run "docclass extraction: article" (fun tag ->
      let ctx =
        File_analyzer.analyze_files ~base_dir:"/tmp"
          ~source:{|\documentclass{article}|} ()
      in
      expect (ctx.doc_class = "article") (tag ^ ": article"));

  run "docclass extraction: book with options" (fun tag ->
      let ctx =
        File_analyzer.analyze_files ~base_dir:"/tmp"
          ~source:{|\documentclass[12pt,a4paper]{book}|} ()
      in
      expect (ctx.doc_class = "book") (tag ^ ": book"));

  run "docclass extraction: memoir" (fun tag ->
      let ctx =
        File_analyzer.analyze_files ~base_dir:"/tmp"
          ~source:{|\documentclass{memoir}|} ()
      in
      expect (ctx.doc_class = "memoir") (tag ^ ": memoir"));

  run "missing image files produce empty list" (fun tag ->
      let src = {|\includegraphics{nonexistent.png}|} in
      let ctx = File_analyzer.analyze_files ~base_dir:"/tmp" ~source:src () in
      expect (ctx.images = []) (tag ^ ": no images for missing file"));

  run "analyze real PNG file" (fun tag ->
      let png_data =
        Test_binary_gen.make_png
          { Test_binary_gen.default_png_opts with dpi = 300 }
      in
      let path = Test_binary_gen.write_to_temp_file png_data ".png" in
      Fun.protect
        ~finally:(fun () -> Sys.remove path)
        (fun () ->
          let dir = Filename.dirname path in
          let basename = Filename.basename path in
          let src =
            Printf.sprintf {|\includegraphics{%s}|} basename
          in
          let ctx = File_analyzer.analyze_files ~base_dir:dir ~source:src () in
          expect (List.length ctx.images = 1) (tag ^ ": 1 image");
          let img = List.hd ctx.images in
          expect (img.width_px = 100) (tag ^ ": width=100");
          expect (img.dpi_x > 290.0 && img.dpi_x < 310.0)
            (tag ^ ": dpi ~300")));

  run "analyze real JPEG file" (fun tag ->
      let jpg_data =
        Test_binary_gen.make_jpeg
          { Test_binary_gen.default_jpeg_opts with j_dpi = 150 }
      in
      let path = Test_binary_gen.write_to_temp_file jpg_data ".jpg" in
      Fun.protect
        ~finally:(fun () -> Sys.remove path)
        (fun () ->
          let dir = Filename.dirname path in
          let basename = Filename.basename path in
          let src =
            Printf.sprintf {|\includegraphics{%s}|} basename
          in
          let ctx = File_analyzer.analyze_files ~base_dir:dir ~source:src () in
          expect (List.length ctx.images = 1) (tag ^ ": 1 image");
          let img = List.hd ctx.images in
          expect (img.format = `JPEG) (tag ^ ": format=JPEG")));

  run "analyze real PDF file" (fun tag ->
      let pdf_data =
        Test_binary_gen.make_pdf
          {
            Test_binary_gen.default_pdf_opts with
            has_struct_tree = true;
            has_lang = Some "en";
          }
      in
      let path = Test_binary_gen.write_to_temp_file pdf_data ".pdf" in
      Fun.protect
        ~finally:(fun () -> Sys.remove path)
        (fun () ->
          let dir = Filename.dirname path in
          let basename = Filename.basename path in
          let src =
            Printf.sprintf {|\includegraphics{%s}|} basename
          in
          let ctx = File_analyzer.analyze_files ~base_dir:dir ~source:src () in
          expect (List.length ctx.pdfs >= 1) (tag ^ ": >=1 pdf")));

  run "CJK font extraction" (fun tag ->
      let src =
        {|\setCJKmainfont{NotoSansCJK}
\setCJKsansfont{SourceHanSans}|}
      in
      (* These fonts don't exist, so no font_info entries *)
      let ctx =
        File_analyzer.analyze_files ~base_dir:"/tmp" ~source:src ()
      in
      expect (ctx.fonts = []) (tag ^ ": missing fonts produce empty list"));

  run "multiple images in document" (fun tag ->
      let png1 =
        Test_binary_gen.make_png Test_binary_gen.default_png_opts
      in
      let png2 =
        Test_binary_gen.make_png
          { Test_binary_gen.default_png_opts with width = 200 }
      in
      let p1 = Test_binary_gen.write_to_temp_file png1 ".png" in
      let p2 = Test_binary_gen.write_to_temp_file png2 ".png" in
      Fun.protect
        ~finally:(fun () ->
          Sys.remove p1;
          Sys.remove p2)
        (fun () ->
          let dir = Filename.dirname p1 in
          let b1 = Filename.basename p1 in
          let b2 = Filename.basename p2 in
          let src =
            Printf.sprintf
              {|\includegraphics{%s}
\includegraphics{%s}|}
              b1 b2
          in
          let ctx =
            File_analyzer.analyze_files ~base_dir:dir ~source:src ()
          in
          expect (List.length ctx.images = 2) (tag ^ ": 2 images")))

let () = finalise "file-analyzer"
