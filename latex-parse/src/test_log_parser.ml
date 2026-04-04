(** Unit tests for Log_parser — LaTeX .log file parsing. *)

open Test_helpers

let () =
  (* Test 1: Overfull \hbox parsing *)
  run "overfull hbox detected" (fun tag ->
      let log =
        "Overfull \\hbox (3.45pt too wide) in paragraph at lines 42--45\n"
      in
      let ctx = Latex_parse_lib.Log_parser.parse_log log in
      expect
        (List.length ctx.overfull_lines = 1)
        (tag ^ ": one overfull line range");
      expect (fst (List.hd ctx.overfull_lines) = 42) (tag ^ ": line_start = 42");
      expect (snd (List.hd ctx.overfull_lines) = 45) (tag ^ ": line_end = 45");
      expect (ctx.max_overfull_pt > 3.0) (tag ^ ": amount > 3pt"));

  (* Test 2: Underfull \hbox parsing *)
  run "underfull hbox detected" (fun tag ->
      let log =
        "Underfull \\hbox (badness 10000) in paragraph at lines 100\n"
      in
      let ctx = Latex_parse_lib.Log_parser.parse_log log in
      expect (List.length ctx.underfull_lines = 1) (tag ^ ": one underfull");
      expect (List.hd ctx.underfull_lines = 100) (tag ^ ": line = 100"));

  (* Test 3: Page numbers *)
  run "page numbers extracted" (fun tag ->
      let log = "[1] [2] [3] [4]\n[5]\n" in
      let ctx = Latex_parse_lib.Log_parser.parse_log log in
      expect (List.length ctx.pages = 5) (tag ^ ": 5 pages"));

  (* Test 4: Widow/orphan detection *)
  run "widow penalty detected" (fun tag ->
      let log = "Widow penalty 150 (page 3)\n" in
      let ctx = Latex_parse_lib.Log_parser.parse_log log in
      expect ctx.has_widows (tag ^ ": has widows"));

  run "club penalty detected" (fun tag ->
      let log = "Club penalty 150 (page 5)\n" in
      let ctx = Latex_parse_lib.Log_parser.parse_log log in
      expect ctx.has_orphans (tag ^ ": has orphans"));

  (* Test 5: Empty log *)
  run "empty log produces empty context" (fun tag ->
      let ctx = Latex_parse_lib.Log_parser.parse_log "" in
      expect (ctx.events = []) (tag ^ ": no events");
      expect (ctx.pages = []) (tag ^ ": no pages");
      expect (not ctx.has_widows) (tag ^ ": no widows"));

  (* Test 6: Mixed log *)
  run "mixed log events" (fun tag ->
      let log =
        "This is pdfTeX, Version 3.14\n\
         [1]\n\
         Overfull \\hbox (5.2pt too wide) in paragraph at lines 10--12\n\
         [2]\n\
         Underfull \\hbox (badness 5000) in paragraph at lines 30\n\
         [3] [4]\n\
         Widow penalty 150 (page 4)\n"
      in
      let ctx = Latex_parse_lib.Log_parser.parse_log log in
      expect (List.length ctx.pages = 4) (tag ^ ": 4 pages");
      expect (List.length ctx.overfull_lines = 1) (tag ^ ": 1 overfull");
      expect (List.length ctx.underfull_lines = 1) (tag ^ ": 1 underfull");
      expect ctx.has_widows (tag ^ ": has widows");
      expect (ctx.max_overfull_pt > 5.0) (tag ^ ": max > 5pt"));

  finalise "log_parser"
