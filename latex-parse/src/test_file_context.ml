(** Test_file_context — thread-local storage for file analysis. 12 cases. *)

open Latex_parse_lib

let cases = ref 0
let fails = ref 0

let expect cond msg =
  incr cases;
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  let tag = Printf.sprintf "case %d: %s" (!cases + 1) msg in
  f tag

let () =
  (* Clean slate *)
  File_context.clear_file_context ();

  run "get without set returns None" (fun tag ->
      expect (File_context.get_file_context () = None) (tag ^ ": should be None"));

  run "set then get returns Some" (fun tag ->
      let ctx =
        {
          File_context.images = [];
          pdfs = [];
          fonts = [];
          doc_class = "article";
        }
      in
      File_context.set_file_context ctx;
      expect
        (File_context.get_file_context () <> None)
        (tag ^ ": should be Some"));

  run "get returns correct doc_class" (fun tag ->
      match File_context.get_file_context () with
      | Some ctx ->
          expect (ctx.doc_class = "article") (tag ^ ": doc_class=article")
      | None -> expect false (tag ^ ": should be Some"));

  run "set overwrites previous" (fun tag ->
      let ctx2 =
        { File_context.images = []; pdfs = []; fonts = []; doc_class = "book" }
      in
      File_context.set_file_context ctx2;
      match File_context.get_file_context () with
      | Some ctx -> expect (ctx.doc_class = "book") (tag ^ ": doc_class=book")
      | None -> expect false (tag ^ ": should be Some"));

  run "clear then get returns None" (fun tag ->
      File_context.clear_file_context ();
      expect (File_context.get_file_context () = None) (tag ^ ": should be None"));

  run "set with images" (fun tag ->
      let img : File_context.image_info =
        {
          path = "/tmp/test.png";
          format = `PNG;
          width_px = 100;
          height_px = 200;
          dpi_x = 72.0;
          dpi_y = 72.0;
          has_transparency = false;
          color_type = `RGB;
          has_icc_profile = false;
          icc_is_srgb = false;
          palette_size = 0;
          file_size = 1024;
        }
      in
      let ctx =
        {
          File_context.images = [ img ];
          pdfs = [];
          fonts = [];
          doc_class = "article";
        }
      in
      File_context.set_file_context ctx;
      match File_context.get_file_context () with
      | Some c ->
          expect (List.length c.images = 1) (tag ^ ": 1 image");
          let i = List.hd c.images in
          expect (i.width_px = 100) (tag ^ ": width=100");
          expect (i.dpi_x = 72.0) (tag ^ ": dpi_x=72")
      | None -> expect false (tag ^ ": should be Some"));

  run "set with pdfs" (fun tag ->
      let pdf : File_context.pdf_info =
        {
          path = "/tmp/test.pdf";
          file_size = 50000;
          has_struct_tree_root = true;
          has_mark_info = true;
          figures_without_alt = 2;
          links_without_contents = 1;
          lang_entry = Some "en-US";
          fonts = [ ("Times", true, false) ];
          has_spot_colour = false;
          has_spot_colour_vector = false;
          streams_all_compressed = true;
          page_label_count = 0;
          page_count = 1;
        }
      in
      let ctx =
        {
          File_context.images = [];
          pdfs = [ pdf ];
          fonts = [];
          doc_class = "report";
        }
      in
      File_context.set_file_context ctx;
      match File_context.get_file_context () with
      | Some c ->
          expect (List.length c.pdfs = 1) (tag ^ ": 1 pdf");
          let p = List.hd c.pdfs in
          expect p.has_struct_tree_root (tag ^ ": struct tree");
          expect (p.figures_without_alt = 2) (tag ^ ": 2 figs no alt")
      | None -> expect false (tag ^ ": should be Some"));

  run "set with fonts" (fun tag ->
      let font : File_context.font_info =
        { path = "/tmp/font.ttf"; has_cjk_coverage = true }
      in
      let ctx =
        {
          File_context.images = [];
          pdfs = [];
          fonts = [ font ];
          doc_class = "article";
        }
      in
      File_context.set_file_context ctx;
      match File_context.get_file_context () with
      | Some c ->
          expect (List.length c.fonts = 1) (tag ^ ": 1 font");
          expect (List.hd c.fonts).has_cjk_coverage (tag ^ ": has CJK")
      | None -> expect false (tag ^ ": should be Some"));

  (* Thread isolation *)
  run "thread isolation: child thread sees None" (fun tag ->
      File_context.clear_file_context ();
      let ctx =
        {
          File_context.images = [];
          pdfs = [];
          fonts = [];
          doc_class = "main-thread";
        }
      in
      File_context.set_file_context ctx;
      let child_saw_none = ref false in
      let t =
        Thread.create
          (fun () -> child_saw_none := File_context.get_file_context () = None)
          ()
      in
      Thread.join t;
      expect !child_saw_none (tag ^ ": child thread isolated"));

  run "thread isolation: parent unaffected by child set" (fun tag ->
      let child_set = ref false in
      let t =
        Thread.create
          (fun () ->
            let ctx =
              {
                File_context.images = [];
                pdfs = [];
                fonts = [];
                doc_class = "child-thread";
              }
            in
            File_context.set_file_context ctx;
            child_set := true)
          ()
      in
      Thread.join t;
      expect !child_set (tag ^ ": child did set");
      match File_context.get_file_context () with
      | Some c ->
          expect (c.doc_class = "main-thread") (tag ^ ": parent unaffected")
      | None -> expect false (tag ^ ": parent should still have context"));

  File_context.clear_file_context ()

let () =
  Printf.printf "[file-context] %d passed, %d failed\n%!" !cases !fails;
  if !fails > 0 then exit 1
