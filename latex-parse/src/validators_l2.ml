open Validators_common

(* ══════════════════════════════════════════════════════════════════════
   L2-approximable rules: figure, table, package, CJK structure checks These are
   specced at L2_Ast but implemented via structural text scanning
   ══════════════════════════════════════════════════════════════════════ *)

(* ── FIG-001: Figure without caption ─────────────────────────────────── *)
let r_fig_001 : rule =
  let run s =
    let blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body -> if not (has_caption body) then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-001";
          severity = Warning;
          message = "Figure without caption";
          count = cnt;
        }
    else None
  in
  { id = "FIG-001"; run; languages = [] }

(* ── FIG-002: Figure without label ───────────────────────────────────── *)
let r_fig_002 : rule =
  let re_label = Str.regexp {|\\label{|} in
  let run s =
    let blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let found =
            try
              ignore (Str.search_forward re_label body 0);
              true
            with Not_found -> false
          in
          if not found then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-002";
          severity = Warning;
          message = "Figure without label";
          count = cnt;
        }
    else None
  in
  { id = "FIG-002"; run; languages = [] }

(* ── FIG-003: Label before caption in figure ─────────────────────────── *)
let r_fig_003 : rule =
  let re_label = Str.regexp {|\\label{|} in
  let re_caption = Str.regexp {|\\caption\(\[\|{\)|} in
  let run s =
    let blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let label_pos =
            try Some (Str.search_forward re_label body 0)
            with Not_found -> None
          in
          let caption_pos =
            try Some (Str.search_forward re_caption body 0)
            with Not_found -> None
          in
          match (label_pos, caption_pos) with
          | Some lp, Some cp when lp < cp -> acc + 1
          | _ -> acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-003";
          severity = Info;
          message = "Label before caption in figure";
          count = cnt;
        }
    else None
  in
  { id = "FIG-003"; run; languages = [] }

(* ── FIG-007: Figure lacks alt text for accessibility ────────────────── *)
let r_fig_007 : rule =
  let re_includegraphics = Str.regexp_string "\\includegraphics" in
  let run s =
    let blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          (* count \includegraphics without alt= in their options *)
          let c = ref 0 in
          let i = ref 0 in
          (try
             while true do
               let pos = Str.search_forward re_includegraphics body !i in
               let after = pos + 16 in
               (* \includegraphics = 16 chars *)
               (* check if followed by [...] containing alt= *)
               let has_alt =
                 if after < String.length body && body.[after] = '[' then (
                   let j = ref (after + 1) in
                   while !j < String.length body && body.[!j] <> ']' do
                     incr j
                   done;
                   if !j < String.length body then
                     let opts = String.sub body (after + 1) (!j - after - 1) in
                     count_substring opts "alt=" > 0
                   else false)
                 else false
               in
               if not has_alt then incr c;
               i := after
             done
           with Not_found -> ());
          acc + !c)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-007";
          severity = Info;
          message = {|Figure lacks alt text for accessibility|};
          count = cnt;
        }
    else None
  in
  { id = "FIG-007"; run; languages = [] }

(* ── FIG-009: Float position specifier ! used excessively ────────────── *)
let r_fig_009 : rule =
  let run s =
    (* count \begin{figure}[...!...] or \begin{table}[...!...] *)
    let cnt = ref 0 in
    let envs = [ "figure"; "table"; "figure*"; "table*" ] in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks_with_opts env s in
        List.iter
          (fun (opts, _body) -> if String.contains opts '!' then incr cnt)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "FIG-009";
          severity = Info;
          message = "Float position specifier ! used excessively";
          count = !cnt;
        }
    else None
  in
  { id = "FIG-009"; run; languages = [] }

(* ── TAB-001: Table lacks caption ────────────────────────────────────── *)
let r_tab_001 : rule =
  let run s =
    let blocks = extract_env_blocks_starred "table" s in
    let cnt =
      List.fold_left
        (fun acc body -> if not (has_caption body) then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-001";
          severity = Warning;
          message = "Table lacks caption";
          count = cnt;
        }
    else None
  in
  { id = "TAB-001"; run; languages = [] }

(* ── TAB-002: Caption below table (journal requires above) ──────────── *)
let r_tab_002 : rule =
  (* Match both \end{tabular} and \end{tabular*} *)
  let re_tabular_end = Str.regexp {|\\end{tabular\*?}|} in
  let re_caption = Str.regexp {|\\caption\(\[\|{\)|} in
  let run s =
    let blocks = extract_env_blocks_starred "table" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          (* Check if \caption appears after \end{tabular} or \end{tabular*} *)
          let tabular_end_pos =
            try Some (Str.search_forward re_tabular_end body 0)
            with Not_found -> None
          in
          let caption_pos =
            try Some (Str.search_forward re_caption body 0)
            with Not_found -> None
          in
          match (tabular_end_pos, caption_pos) with
          | Some tp, Some cp when cp > tp -> acc + 1
          | _ -> acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-002";
          severity = Info;
          message = "Caption below table (journal requires above)";
          count = cnt;
        }
    else None
  in
  { id = "TAB-002"; run; languages = [] }

(* ── TAB-005: Vertical rules present in tabular ─────────────────────── *)
let r_tab_005 : rule =
  let re_plain = Str.regexp_string "\\begin{tabular}{" in
  let re_star = Str.regexp_string "\\begin{tabular*}{" in
  (* Skip one brace group: returns position after matching } *)
  let skip_brace_group s start =
    let depth = ref 1 in
    let j = ref start in
    while !j < String.length s && !depth > 0 do
      (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
      incr j
    done;
    !j
  in
  (* Extract column spec string from brace group starting at pos *)
  let extract_col_spec s start =
    let depth = ref 1 in
    let j = ref start in
    while !j < String.length s && !depth > 0 do
      (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
      if !depth > 0 then incr j
    done;
    if !j > start then Some (String.sub s start (!j - start)) else None
  in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (* Check plain \begin{tabular}{colspec} *)
    (try
       while true do
         let _ = Str.search_forward re_plain s !i in
         let after = Str.match_end () in
         (match extract_col_spec s after with
         | Some col_spec -> if String.contains col_spec '|' then incr cnt
         | None -> ());
         i := after + 1
       done
     with Not_found -> ());
    (* Check \begin{tabular*}{width}{colspec} — skip width, check colspec *)
    i := 0;
    (try
       while true do
         let _ = Str.search_forward re_star s !i in
         let after = Str.match_end () in
         (* skip the width brace group *)
         let after_width = skip_brace_group s after in
         (* now expect the column spec brace group *)
         (if after_width < String.length s && s.[after_width] = '{' then
            match extract_col_spec s (after_width + 1) with
            | Some col_spec -> if String.contains col_spec '|' then incr cnt
            | None -> ());
         i := after_width + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TAB-005";
          severity = Info;
          message = "Vertical rules present in tabular";
          count = !cnt;
        }
    else None
  in
  { id = "TAB-005"; run; languages = [] }

(* ── PKG-001: Package duplicate inclusion detected ───────────────────── *)
let r_pkg_001 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages preamble in
    let seen = Hashtbl.create 16 in
    let cnt = ref 0 in
    List.iter
      (fun (_pos, pkg) ->
        if Hashtbl.mem seen pkg then incr cnt else Hashtbl.add seen pkg true)
      pkgs;
    if !cnt > 0 then
      Some
        {
          id = "PKG-001";
          severity = Warning;
          message = "Package duplicate inclusion detected";
          count = !cnt;
        }
    else None
  in
  { id = "PKG-001"; run; languages = [] }

(* ── PKG-002: geometry loaded after hyperref — must precede ──────────── *)
let r_pkg_002 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages preamble in
    let geom_pos = ref (-1) in
    let hyper_pos = ref (-1) in
    List.iter
      (fun (pos, pkg) ->
        if pkg = "geometry" && !geom_pos < 0 then geom_pos := pos;
        if pkg = "hyperref" && !hyper_pos < 0 then hyper_pos := pos)
      pkgs;
    if !geom_pos >= 0 && !hyper_pos >= 0 && !geom_pos > !hyper_pos then
      Some
        {
          id = "PKG-002";
          severity = Error;
          message = {|geometry loaded after hyperref – must precede|};
          count = 1;
        }
    else None
  in
  { id = "PKG-002"; run; languages = [] }

(* ── PKG-004: Package loaded after \begin{document} ──────────────────── *)
let r_pkg_004 : rule =
  let re_usepackage = Str.regexp_string "\\usepackage" in
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body ->
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let _ = Str.search_forward re_usepackage body !i in
             incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "PKG-004";
              severity = Error;
              message = {esc|Package loaded after \begin{document}|esc};
              count = !cnt;
            }
        else None
  in
  { id = "PKG-004"; run; languages = [] }

(* ── PKG-005: Unknown option for geometry ────────────────────────────── *)
let r_pkg_005 : rule =
  (* Known geometry options — comprehensive list *)
  let known_opts =
    [
      "a0paper";
      "a1paper";
      "a2paper";
      "a3paper";
      "a4paper";
      "a5paper";
      "a6paper";
      "b0paper";
      "b1paper";
      "b2paper";
      "b3paper";
      "b4paper";
      "b5paper";
      "b6paper";
      "letterpaper";
      "legalpaper";
      "executivepaper";
      "landscape";
      "portrait";
      "top";
      "bottom";
      "left";
      "right";
      "inner";
      "outer";
      "hmargin";
      "vmargin";
      "margin";
      "textheight";
      "textwidth";
      "paperheight";
      "paperwidth";
      "headheight";
      "headsep";
      "footskip";
      "marginparsep";
      "marginparwidth";
      "columnsep";
      "hoffset";
      "voffset";
      "bindingoffset";
      "twoside";
      "asymmetric";
      "includeheadfoot";
      "includehead";
      "includefoot";
      "includemp";
      "centering";
      "scale";
      "hscale";
      "vscale";
      "heightrounded";
      "hratio";
      "vratio";
      "lines";
      "pass";
      "reset";
      "mag";
      "truedimen";
      "showframe";
      "verbose";
      "nohead";
      "nofoot";
      "noheadfoot";
      "nomarginpar";
      "driver";
      "pdftex";
      "xetex";
      "luatex";
      "dvips";
      "dvipdfm";
      "dvipdfmx";
      "total";
      "body";
      "paper";
      "lmargin";
      "rmargin";
      "tmargin";
      "bmargin";
      "ignoreall";
      "ignorehead";
      "ignorefoot";
      "ignoremp";
    ]
  in
  let known_set = Hashtbl.create 128 in
  let () = List.iter (fun o -> Hashtbl.add known_set o true) known_opts in
  let re_geom_opts = Str.regexp {|\\usepackage\[\([^]]*\)\]{geometry}|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re_geom_opts s !i in
         let opts_str = Str.matched_group 1 s in
         let opts = String.split_on_char ',' opts_str in
         List.iter
           (fun o ->
             let o = String.trim o in
             (* strip key=value to get just key *)
             let key =
               match String.index_opt o '=' with
               | Some idx -> String.trim (String.sub o 0 idx)
               | None -> o
             in
             if key <> "" && not (Hashtbl.mem known_set key) then incr cnt)
           opts;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "PKG-005";
          severity = Warning;
          message = "Unknown option for geometry";
          count = !cnt;
        }
    else None
  in
  { id = "PKG-005"; run; languages = [] }

(* ── CJK-004: xeCJK package missing when CJK glyphs present ─────────── *)
let r_cjk_004 : rule =
  let run s =
    (* Check if CJK characters present (U+4E00..U+9FFF, U+3400..U+4DBF) *)
    let has_cjk = ref false in
    let len = String.length s in
    let i = ref 0 in
    while !i < len - 2 && not !has_cjk do
      let b0 = Char.code (String.unsafe_get s !i) in
      if b0 >= 0xe4 && b0 <= 0xe9 then (
        (* potential CJK Unified Ideograph: U+4E00..U+9FFF = E4 B8 80..E9 BF BF *)
        (* also U+3400..U+4DBF = E3 90 80..E4 B6 BF *)
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        if b1 >= 0x80 && b1 <= 0xbf && b2 >= 0x80 && b2 <= 0xbf then
          has_cjk := true;
        i := !i + 3)
      else if b0 = 0xe3 then (
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        if b1 >= 0x90 && b2 >= 0x80 then has_cjk := true;
        i := !i + 3)
      else if b0 >= 0x80 then
        (* skip other multi-byte *)
        if b0 >= 0xf0 then i := !i + 4
        else if b0 >= 0xe0 then i := !i + 3
        else i := !i + 2
      else i := !i + 1
    done;
    if !has_cjk then
      (* check if xeCJK or CJKutf8 or ctex is loaded (handles options) *)
      if
        not
          (has_package s "xeCJK"
          || has_package s "CJKutf8"
          || has_package s "ctex")
      then
        Some
          {
            id = "CJK-004";
            severity = Warning;
            message = "xeCJK package missing when CJK glyphs present";
            count = 1;
          }
      else None
    else None
  in
  { id = "CJK-004"; run; languages = [ "zh"; "ja"; "ko" ] }

(* ── CJK-006: Ruby annotation requires ruby package ─────────────────── *)
let r_cjk_006 : rule =
  let re_ruby = Str.regexp_string "\\ruby{" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re_ruby s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      let has_ruby_pkg =
        has_package s "ruby"
        || has_package s "pxrubrica"
        || has_package s "luatexja-ruby"
      in
      if not has_ruby_pkg then
        Some
          {
            id = "CJK-006";
            severity = Warning;
            message = "Ruby annotation requires ruby package";
            count = !cnt;
          }
      else None
    else None
  in
  { id = "CJK-006"; run; languages = [ "zh"; "ja"; "ko" ] }

(* ── FONT-006: Missing \microtypesetup{expansion=true} ─────────────── *)
(* Fire if \usepackage{microtype} is present but \microtypesetup{expansion=true}
   is absent *)
let r_font_006 : rule =
  let re_setup =
    Str.regexp {|\\microtypesetup{[^}]*expansion[ ]*=[ ]*true[^}]*}|}
  in
  let run s =
    if has_package s "microtype" then
      let found =
        try
          ignore (Str.search_forward re_setup s 0);
          true
        with Not_found -> false
      in
      if not found then
        Some
          {
            id = "FONT-006";
            severity = Info;
            message = {|Missing \microtypesetup{expansion=true}|};
            count = 1;
          }
      else None
    else None
  in
  { id = "FONT-006"; run; languages = [] }

(* ── FONT-007: Obsolete \usepackage[T1]{fontenc} under XeLaTeX ──────── *)
(* Fire if \usepackage[T1]{fontenc} is present AND there is evidence of XeLaTeX
   usage (fontspec, xeCJK, or ifxetex) *)
let r_font_007 : rule =
  let re_fontenc = Str.regexp {|\\usepackage\[T1\]{fontenc}|} in
  let run s =
    let has_fontenc =
      try
        ignore (Str.search_forward re_fontenc s 0);
        true
      with Not_found -> false
    in
    if has_fontenc then
      let xelatex =
        has_package s "fontspec"
        || has_package s "xeCJK"
        || has_package s "ifxetex"
      in
      if xelatex then
        Some
          {
            id = "FONT-007";
            severity = Warning;
            message = {|Obsolete \usepackage[T1]{fontenc} under XeLaTeX|};
            count = 1;
          }
      else None
    else None
  in
  { id = "FONT-007"; run; languages = [] }

(* ── FONT-008: Multiple \setmainfont declarations ────────────────────── *)
let r_font_008 : rule =
  let re = Str.regexp {|\\setmainfont\(\[\|{\)|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 1 then
      Some
        {
          id = "FONT-008";
          severity = Warning;
          message = "Multiple \\setmainfont declarations";
          count = !cnt;
        }
    else None
  in
  { id = "FONT-008"; run; languages = [] }

(* ── MATH-032: Incorrect small matrix brackets ───────────────────────── *)
(* In LaTeX, \begin{smallmatrix} should be wrapped in appropriate delimiters:
   \bigl( ... \bigr) or \left( ... \right) etc. If wrapped in [ ] brackets, the
   correct environment is bsmallmatrix. Fire if \begin{smallmatrix} is found
   inside [ ] delimiters. *)
let r_math_032 : rule =
  let re = Str.regexp_string "\\begin{smallmatrix}" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re s !i in
         (* Look backwards for opening delimiter *)
         let j = ref (pos - 1) in
         while !j >= 0 && (s.[!j] = ' ' || s.[!j] = '\n' || s.[!j] = '\r') do
           decr j
         done;
         if !j >= 0 && s.[!j] = '[' then incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "MATH-032";
          severity = Warning;
          message = "Incorrect small matrix brackets";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-032"; run; languages = [] }

(* ── MATH-054: Equation labelled 'eq:' without environment ──────────── *)
(* Fire if \label{eq:...} appears outside known equation environments *)
let r_math_054 : rule =
  let re_label = Str.regexp {|\\label{eq:[^}]*}|} in
  let eq_envs =
    [
      "equation";
      "equation*";
      "align";
      "align*";
      "gather";
      "gather*";
      "multline";
      "multline*";
      "flalign";
      "flalign*";
      "alignat";
      "alignat*";
      "eqnarray";
      "eqnarray*";
    ]
  in
  let run s =
    (* Collect all ranges covered by equation environments *)
    let eq_ranges = ref [] in
    List.iter
      (fun env ->
        let open_tag = "\\begin{" ^ env ^ "}" in
        let close_tag = "\\end{" ^ env ^ "}" in
        let open_len = String.length open_tag in
        let close_len = String.length close_tag in
        let n = String.length s in
        let i = ref 0 in
        while !i <= n - open_len do
          if String.sub s !i open_len = open_tag then (
            let start = !i in
            i := !i + open_len;
            let found = ref false in
            while !i <= n - close_len && not !found do
              if String.sub s !i close_len = close_tag then (
                eq_ranges := (start, !i + close_len) :: !eq_ranges;
                i := !i + close_len;
                found := true)
              else incr i
            done;
            if not !found then i := n)
          else incr i
        done)
      eq_envs;
    let ranges = !eq_ranges in
    (* Find \label{eq:...} outside any equation range *)
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re_label s !i in
         let inside =
           List.exists (fun (lo, hi) -> pos >= lo && pos < hi) ranges
         in
         if not inside then incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "MATH-054";
          severity = Warning;
          message = {|Equation labelled 'eq:' without environment|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-054"; run; languages = [] }

(* ── MATH-062: Multiline equation lacks alignment character & ────────── *)
(* Fire if an align, align*, flalign, flalign*, alignat, alignat* environment
   contains no & character *)
let r_math_062 : rule =
  let align_envs =
    [ "align"; "align*"; "flalign"; "flalign*"; "alignat"; "alignat*" ]
  in
  let run s =
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun body -> if not (String.contains body '&') then incr cnt)
          blocks)
      align_envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-062";
          severity = Warning;
          message = "Multiline equation lacks alignment character &";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-062"; run; languages = [] }

(* ── MATH-063: Equation array with > 1 alignment point ──────────────── *)
(* In eqnarray, each line should have at most 2 & (for 3 columns). Fire if any
   line has more than 2 & characters. Also check split environments which should
   have exactly 1 &. *)
let r_math_063 : rule =
  let linebreak_re = Str.regexp_string "\\\\" in
  let run s =
    let cnt = ref 0 in
    let eqn_envs = [ "eqnarray"; "eqnarray*" ] in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun body ->
            let lines = Str.split linebreak_re body in
            List.iter
              (fun line ->
                let amps =
                  String.fold_left
                    (fun acc c -> if c = '&' then acc + 1 else acc)
                    0 line
                in
                if amps > 2 then incr cnt)
              lines)
          blocks)
      eqn_envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-063";
          severity = Warning;
          message = "Equation array with > 1 alignment point";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-063"; run; languages = [] }

(* ── MATH-100: Punctuation after equation missing (comma/period) ─────── *)
(* Fire if a display equation environment ends without a comma, period, or
   semicolon before \end{...} *)
let r_math_100 : rule =
  let display_envs =
    [
      "equation";
      "equation*";
      "align";
      "align*";
      "gather";
      "gather*";
      "multline";
      "multline*";
      "flalign";
      "flalign*";
    ]
  in
  let run s =
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun body ->
            (* Strip trailing whitespace *)
            let b = String.trim body in
            let n = String.length b in
            if n > 0 then
              let last = b.[n - 1] in
              if last <> ',' && last <> '.' && last <> ';' then incr cnt)
          blocks)
      display_envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-100";
          severity = Info;
          message = "Punctuation after equation missing (comma/period)";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-100"; run; languages = [] }

(* ── MATH-023: Equation label missing although referenced ────────────── *)
let r_math_023 : rule =
  let run s =
    let labels = extract_labels_with_prefix "eq:" s in
    let refs = extract_refs_with_prefix "eq:" s in
    let label_keys =
      List.fold_left
        (fun acc (_pos, key) -> if List.mem key acc then acc else key :: acc)
        [] labels
    in
    let cnt = ref 0 in
    List.iter
      (fun (_pos, key) ->
        if not (List.mem key label_keys) then
          (* Only count each missing label once *)
          if not (List.exists (fun (_p2, k2) -> k2 = key && _p2 < _pos) refs)
          then incr cnt)
      refs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-023";
          severity = Warning;
          message = "Equation label missing although referenced";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-023"; run; languages = [] }

(* ── MATH-024: Equation labelled but never referenced ────────────────── *)
let r_math_024 : rule =
  let run s =
    let labels = extract_labels_with_prefix "eq:" s in
    let refs = extract_refs_with_prefix "eq:" s in
    let ref_keys =
      List.fold_left
        (fun acc (_pos, key) -> if List.mem key acc then acc else key :: acc)
        [] refs
    in
    let cnt = ref 0 in
    List.iter
      (fun (_pos, key) -> if not (List.mem key ref_keys) then incr cnt)
      labels;
    if !cnt > 0 then
      Some
        {
          id = "MATH-024";
          severity = Info;
          message = "Equation labelled but never referenced";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-024"; run; languages = [] }

(* ── REF-010: Figure referenced before first mention in text ─────────── *)
(* Fire if \ref{fig:X} appears at a position before the \label{fig:X} *)
let r_ref_010 : rule =
  let run s =
    let labels = extract_labels_with_prefix "fig:" s in
    let refs = extract_refs_with_prefix "fig:" s in
    let cnt = ref 0 in
    (* For each unique ref key, check if first ref precedes label *)
    let checked = ref [] in
    List.iter
      (fun (ref_pos, key) ->
        if not (List.mem key !checked) then (
          checked := key :: !checked;
          (* Find label position for this key *)
          let label_pos =
            try
              let lpos, _ = List.find (fun (_p, k) -> k = key) labels in
              Some lpos
            with Not_found -> None
          in
          match label_pos with
          | Some lpos -> if ref_pos < lpos then incr cnt
          | None -> ()))
      refs;
    if !cnt > 0 then
      Some
        {
          id = "REF-010";
          severity = Info;
          message = "Figure referenced before first mention in text";
          count = !cnt;
        }
    else None
  in
  { id = "REF-010"; run; languages = [] }

(* ── CMD-014: \AtBeginDocument placed after \begin{document} ──────────── *)
let r_cmd_014 : rule =
  let re = Str.regexp_string "\\AtBeginDocument" in
  let _re_begin_doc = Str.regexp_string "\\begin{document}" in
  let run s =
    let doc_pos =
      try Some (Str.search_forward _re_begin_doc s 0) with Not_found -> None
    in
    match doc_pos with
    | None -> None
    | Some dp ->
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let pos = Str.search_forward re s !i in
             if pos > dp then incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "CMD-014";
              severity = Warning;
              message = "\\AtBeginDocument placed after \\begin{document}";
              count = !cnt;
            }
        else None
  in
  { id = "CMD-014"; run; languages = [] }

(* ── DOC-001: Title missing \maketitle ───────────────────────────────── *)
(* Only fires for article-like document classes that conventionally use
   \maketitle. Skips beamer, letter, standalone, etc. *)
let r_doc_001 : rule =
  let run s =
    if not (is_article_like s) then None
    else
      let has_maketitle = contains_substring s "\\maketitle" in
      if not has_maketitle then
        Some
          {
            id = "DOC-001";
            severity = Error;
            message = "Title missing \\maketitle";
            count = 1;
          }
      else None
  in
  { id = "DOC-001"; run; languages = [] }

(* ── DOC-002: Abstract environment missing ───────────────────────────── *)
(* Only fires for article-like document classes. *)
let r_doc_002 : rule =
  let run s =
    if not (is_article_like s) then None
    else
      let has_abstract = contains_substring s "\\begin{abstract}" in
      if not has_abstract then
        Some
          {
            id = "DOC-002";
            severity = Warning;
            message = "Abstract environment missing";
            count = 1;
          }
      else None
  in
  { id = "DOC-002"; run; languages = [] }

(* ── DOC-003: Keywords missing ───────────────────────────────────────── *)
(* Only fires for article-like document classes. *)
let r_doc_003 : rule =
  let run s =
    if not (is_article_like s) then None
    else
      let has_keywords = contains_substring s "\\keywords{" in
      if not has_keywords then
        Some
          {
            id = "DOC-003";
            severity = Info;
            message = "Keywords missing";
            count = 1;
          }
      else None
  in
  { id = "DOC-003"; run; languages = [] }

(* ── TAB-006: Consecutive \hline duplicated ──────────────────────────── *)
let r_tab_006 : rule =
  let re = Str.regexp "\\\\hline[ \t\n]*\\\\hline" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !i);
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TAB-006";
          severity = Info;
          message = "Consecutive \\hline duplicated";
          count = !cnt;
        }
    else None
  in
  { id = "TAB-006"; run; languages = [] }

(* ── TAB-009: Floating table missing \label ──────────────────────────── *)
let r_tab_009 : rule =
  let _re_label = Str.regexp {|\\label{|} in
  let run s =
    let blocks = extract_env_blocks_starred "table" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let has_label =
            try
              ignore (Str.search_forward _re_label body 0);
              true
            with Not_found -> false
          in
          if not has_label then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-009";
          severity = Warning;
          message = "Floating table missing \\label";
          count = cnt;
        }
    else None
  in
  { id = "TAB-009"; run; languages = [] }

(* ── TAB-010: Footnote placed inside table environment ───────────────── *)
let r_tab_010 : rule =
  let re_fn = Str.regexp {|\\footnote{|} in
  let run s =
    let blocks = extract_env_blocks_starred "table" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let n = ref 0 in
          let i = ref 0 in
          (try
             while true do
               ignore (Str.search_forward re_fn body !i);
               incr n;
               i := Str.match_end ()
             done
           with Not_found -> ());
          acc + !n)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-010";
          severity = Warning;
          message = "Footnote placed inside table environment";
          count = cnt;
        }
    else None
  in
  { id = "TAB-010"; run; languages = [] }

(* ── TAB-011: Top/bottom \hline instead of \toprule/\bottomrule ──────── *)
let r_tab_011 : rule =
  let _re_toprule = Str.regexp_string "\\toprule" in
  let run s =
    let blocks =
      extract_env_blocks "tabular" s @ extract_env_blocks "tabular*" s
    in
    let cnt =
      List.fold_left
        (fun acc body ->
          let has_hline = contains_substring body "\\hline" in
          let has_booktabs =
            try
              ignore (Str.search_forward _re_toprule body 0);
              true
            with Not_found -> contains_substring body "\\bottomrule"
          in
          if has_hline && not has_booktabs then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-011";
          severity = Info;
          message = "Top/bottom \\hline instead of \\toprule/\\bottomrule";
          count = cnt;
        }
    else None
  in
  { id = "TAB-011"; run; languages = [] }

(* ── TAB-014: Empty multicolumn alignment spec {} encountered ────────── *)
let r_tab_014 : rule =
  let re = Str.regexp {|\\multicolumn{[^}]*}{}|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !i);
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TAB-014";
          severity = Info;
          message = "Empty multicolumn alignment spec {} encountered";
          count = !cnt;
        }
    else None
  in
  { id = "TAB-014"; run; languages = [] }

(* ── PKG-007: hyperref loaded before geometry ────────────────────────── *)
(* Uses first-occurrence position for each package (consistent with PKG-002). *)
let r_pkg_007 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages preamble in
    let hyp_pos =
      List.fold_left
        (fun acc (pos, name) ->
          match acc with
          | Some _ -> acc
          | None -> if name = "hyperref" then Some pos else None)
        None pkgs
    in
    let geo_pos =
      List.fold_left
        (fun acc (pos, name) ->
          match acc with
          | Some _ -> acc
          | None -> if name = "geometry" then Some pos else None)
        None pkgs
    in
    match (hyp_pos, geo_pos) with
    | Some hp, Some gp ->
        if hp < gp then
          Some
            {
              id = "PKG-007";
              severity = Error;
              message = "hyperref loaded before geometry";
              count = 1;
            }
        else None
    | _ -> None
  in
  { id = "PKG-007"; run; languages = [] }

(* ── PKG-009: TikZ libraries loaded inside document body ─────────────── *)
let r_pkg_009 : rule =
  let re = Str.regexp_string "\\usetikzlibrary" in
  let _re_begin_doc_p9 = Str.regexp_string "\\begin{document}" in
  let run s =
    let doc_pos =
      try Some (Str.search_forward _re_begin_doc_p9 s 0)
      with Not_found -> None
    in
    match doc_pos with
    | None -> None
    | Some dp ->
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let pos = Str.search_forward re s !i in
             if pos > dp then incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "PKG-009";
              severity = Info;
              message = "TikZ libraries loaded inside document body";
              count = !cnt;
            }
        else None
  in
  { id = "PKG-009"; run; languages = [] }

(* ── PKG-011: booktabs required but not loaded for \toprule ──────────── *)
let r_pkg_011 : rule =
  let re_toprule = Str.regexp_string "\\toprule" in
  let re_midrule = Str.regexp_string "\\midrule" in
  let re_bottomrule = Str.regexp_string "\\bottomrule" in
  let run s =
    let uses_booktabs_cmds =
      (try
         ignore (Str.search_forward re_toprule s 0);
         true
       with Not_found -> false)
      ||
      try
        ignore (Str.search_forward re_midrule s 0);
        true
      with Not_found -> (
        try
          ignore (Str.search_forward re_bottomrule s 0);
          true
        with Not_found -> false)
    in
    if uses_booktabs_cmds && not (has_package s "booktabs") then
      Some
        {
          id = "PKG-011";
          severity = Warning;
          message = "booktabs required but not loaded for \\toprule";
          count = 1;
        }
    else None
  in
  { id = "PKG-011"; run; languages = [] }

(* ── PKG-012: csquotes not loaded when \enquote used ─────────────────── *)
let r_pkg_012 : rule =
  let re = Str.regexp_string "\\enquote{" in
  let run s =
    let has_enquote =
      try
        ignore (Str.search_forward re s 0);
        true
      with Not_found -> false
    in
    if has_enquote && not (has_package s "csquotes") then
      Some
        {
          id = "PKG-012";
          severity = Error;
          message = "csquotes not loaded when \\enquote used";
          count = 1;
        }
    else None
  in
  { id = "PKG-012"; run; languages = [] }

(* ── PKG-015: inputenc loaded under XeLaTeX/LuaLaTeX ────────────────── *)
let r_pkg_015 : rule =
  let run s =
    if has_package s "inputenc" then
      let xeluatex =
        has_package s "fontspec"
        || has_package s "xeCJK"
        || has_package s "ifxetex"
        || has_package s "ifluatex"
        || has_package s "luatexja"
      in
      if xeluatex then
        Some
          {
            id = "PKG-015";
            severity = Warning;
            message = "inputenc loaded under XeLaTeX/LuaLaTeX";
            count = 1;
          }
      else None
    else None
  in
  { id = "PKG-015"; run; languages = [] }

(* ── PKG-020: tikz external library not loaded when externalising ────── *)
let r_pkg_020 : rule =
  let re_ext = Str.regexp_string "\\tikzexternalize" in
  let re_lib = Str.regexp_string "\\usetikzlibrary{external}" in
  let run s =
    let has_externalize =
      try
        ignore (Str.search_forward re_ext s 0);
        true
      with Not_found -> false
    in
    if has_externalize then
      let has_lib =
        try
          ignore (Str.search_forward re_lib s 0);
          true
        with Not_found -> false
      in
      if not has_lib then
        Some
          {
            id = "PKG-020";
            severity = Info;
            message = "tikz external library not loaded when externalising";
            count = 1;
          }
      else None
    else None
  in
  { id = "PKG-020"; run; languages = [] }

(* ── PKG-022: Obsolete package (epsfig, subfigure, natbib) detected ──── *)
let r_pkg_022 : rule =
  let obsolete_pkgs =
    [ "epsfig"; "subfigure"; "natbib"; "t1enc"; "palatcm"; "euler"; "pslatex" ]
  in
  let run s =
    let cnt =
      List.fold_left
        (fun acc pkg -> if has_package s pkg then acc + 1 else acc)
        0 obsolete_pkgs
    in
    if cnt > 0 then
      Some
        {
          id = "PKG-022";
          severity = Warning;
          message = "Obsolete package (epsfig, subfigure, natbib) detected";
          count = cnt;
        }
    else None
  in
  { id = "PKG-022"; run; languages = [] }

(* ── PKG-023: unicode‑math must load before microtype ────────────────── *)
(* Note: spec description has a non-breaking hyphen U+2011 between "unicode" and
   "math" (bytes E2 80 91) *)
let r_pkg_023 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages preamble in
    let umath_pos =
      List.fold_left
        (fun acc (pos, name) ->
          match acc with
          | Some _ -> acc
          | None -> if name = "unicode-math" then Some pos else None)
        None pkgs
    in
    let micro_pos =
      List.fold_left
        (fun acc (pos, name) ->
          match acc with
          | Some _ -> acc
          | None -> if name = "microtype" then Some pos else None)
        None pkgs
    in
    match (umath_pos, micro_pos) with
    | Some up, Some mp ->
        if up > mp then
          Some
            {
              id = "PKG-023";
              severity = Error;
              message = {|unicode‑math must load before microtype|};
              count = 1;
            }
        else None
    | _ -> None
  in
  { id = "PKG-023"; run; languages = [] }

(* ── LANG-002: babel language option missing ─────────────────────────── *)
let r_lang_002 : rule =
  let re_bare = Str.regexp {|\\usepackage{babel}|} in
  let re_empty = Str.regexp {|\\usepackage\[\]{babel}|} in
  let run s =
    let has_bare =
      try
        ignore (Str.search_forward re_bare s 0);
        true
      with Not_found -> false
    in
    let has_empty =
      try
        ignore (Str.search_forward re_empty s 0);
        true
      with Not_found -> false
    in
    if has_bare || has_empty then
      Some
        {
          id = "LANG-002";
          severity = Warning;
          message = "babel language option missing";
          count = 1;
        }
    else None
  in
  { id = "LANG-002"; run; languages = [] }

(* ── LANG-004: Polyglossia loaded alongside babel – mutual exclusion ── *)
(* Note: spec has en-dash E2 80 93 between "babel" and "mutual" *)
let r_lang_004 : rule =
  let run s =
    if has_package s "polyglossia" && has_package s "babel" then
      Some
        {
          id = "LANG-004";
          severity = Error;
          message = {|Polyglossia loaded alongside babel – mutual exclusion|};
          count = 1;
        }
    else None
  in
  { id = "LANG-004"; run; languages = [] }

(* ── TIKZ-007: TikZ loaded after hyperref – reorder required ─────────── *)
(* Note: spec has en-dash E2 80 93 between "hyperref" and "reorder" *)
let r_tikz_007 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages preamble in
    let tikz_pos =
      List.fold_left
        (fun acc (pos, name) ->
          match acc with
          | Some _ -> acc
          | None -> if name = "tikz" then Some pos else None)
        None pkgs
    in
    let hyp_pos =
      List.fold_left
        (fun acc (pos, name) ->
          match acc with
          | Some _ -> acc
          | None -> if name = "hyperref" then Some pos else None)
        None pkgs
    in
    match (tikz_pos, hyp_pos) with
    | Some tp, Some hp ->
        if tp > hp then
          Some
            {
              id = "TIKZ-007";
              severity = Warning;
              message = {|TikZ loaded after hyperref – reorder required|};
              count = 1;
            }
        else None
    | _ -> None
  in
  { id = "TIKZ-007"; run; languages = [] }

(* ── FIG-010: Subfigure environment without \subcaption ──────────────── *)
(* Check both subfigure and subfigure* environments. *)
let r_fig_010 : rule =
  let _re_subcaption = Str.regexp_string "\\subcaption" in
  let run s =
    let blocks = extract_env_blocks_starred "subfigure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let has_subcap =
            try
              ignore (Str.search_forward _re_subcaption body 0);
              true
            with Not_found -> contains_substring body "\\caption"
          in
          if not has_subcap then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-010";
          severity = Warning;
          message = "Subfigure environment without \\subcaption";
          count = cnt;
        }
    else None
  in
  { id = "FIG-010"; run; languages = [] }

(* ── FIG-013: Graphicx option scale used instead of width ────────────── *)
let r_fig_013 : rule =
  let re = Str.regexp {|\\includegraphics\[[^]]*scale[ ]*=[^]]*\]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !i);
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "FIG-013";
          severity = Info;
          message = "Graphicx option scale used instead of width";
          count = !cnt;
        }
    else None
  in
  { id = "FIG-013"; run; languages = [] }

(* ── PKG-008: xcolor loaded without dvipsnames option ────────────────── *)
let r_pkg_008 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    let has_xcolor_no_dvips =
      List.exists
        (fun (_pos, opts, name) ->
          name = "xcolor" && not (contains_substring opts "dvipsnames"))
        pkgs
    in
    if has_xcolor_no_dvips then
      Some
        {
          id = "PKG-008";
          severity = Info;
          message = "xcolor loaded without dvipsnames option";
          count = 1;
        }
    else None
  in
  { id = "PKG-008"; run; languages = [] }

(* ── PKG-010: biblatex loaded with deprecated backend=biber ──────────── *)
let r_pkg_010 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    let has_deprecated =
      List.exists
        (fun (_pos, opts, name) ->
          name = "biblatex" && contains_substring opts "backend=biber")
        pkgs
    in
    if has_deprecated then
      Some
        {
          id = "PKG-010";
          severity = Warning;
          message = "biblatex loaded with deprecated backend=biber";
          count = 1;
        }
    else None
  in
  { id = "PKG-010"; run; languages = [] }

(* ── PKG-013: microtype not loaded on XeLaTeX path ───────────────────── *)
(* If fontspec is present (implies XeLaTeX/LuaLaTeX) but microtype is not *)
let r_pkg_013 : rule =
  let run s =
    if has_package s "fontspec" && not (has_package s "microtype") then
      Some
        {
          id = "PKG-013";
          severity = Warning;
          message = "microtype not loaded on XeLaTeX path";
          count = 1;
        }
    else None
  in
  { id = "PKG-013"; run; languages = [] }

(* ── PKG-014: siunitx v2 API detected (outdated) ────────────────────── *)
(* Detect \SI{, \si{, \num{ which are v2 commands. v3 uses \qty, \unit instead.
   Only fire if siunitx is loaded. *)
let r_pkg_014 : rule =
  let re = Str.regexp {|\\\(SI\|si\|SIrange\){|} in
  let run s =
    if not (has_package s "siunitx") then None
    else
      let cnt = ref 0 in
      let i = ref 0 in
      (try
         while true do
           let _ = Str.search_forward re s !i in
           incr cnt;
           i := Str.match_end ()
         done
       with Not_found -> ());
      if !cnt > 0 then
        Some
          {
            id = "PKG-014";
            severity = Warning;
            message = "siunitx v2 API detected (outdated)";
            count = !cnt;
          }
      else None
  in
  { id = "PKG-014"; run; languages = [] }

(* ── PKG-016: graphicx option pdftex incompatible with engine ────────── *)
let r_pkg_016 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    let has_pdftex_opt =
      List.exists
        (fun (_pos, opts, name) ->
          name = "graphicx" && contains_substring opts "pdftex")
        pkgs
    in
    if has_pdftex_opt then
      Some
        {
          id = "PKG-016";
          severity = Warning;
          message = "graphicx option pdftex incompatible with engine";
          count = 1;
        }
    else None
  in
  { id = "PKG-016"; run; languages = [] }

(* ── PKG-017: fontspec loaded in pdfLaTeX ────────────────────────────── *)
(* Conservative: fire if fontspec is loaded AND pdfLaTeX markers present
   ([T1]{fontenc} or [utf8]{inputenc}). *)
let r_pkg_017 : rule =
  let run s =
    if not (has_package s "fontspec") then None
    else
      let preamble = extract_preamble s in
      let pkgs = extract_usepackages_with_opts preamble in
      let has_pdftex_marker =
        List.exists
          (fun (_pos, opts, name) ->
            name = "fontenc"
            && String.length opts > 0
            && contains_substring opts "T1"
            || name = "inputenc"
               && String.length opts > 0
               && contains_substring opts "utf8")
          pkgs
      in
      if has_pdftex_marker then
        Some
          {
            id = "PKG-017";
            severity = Error;
            message = "fontspec loaded in pdfLaTeX";
            count = 1;
          }
      else None
  in
  { id = "PKG-017"; run; languages = [] }

(* ── PKG-021: Package loaded twice with conflicting options ──────────── *)
let r_pkg_021 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    (* Group by package name, collect distinct option strings *)
    let tbl = Hashtbl.create 16 in
    List.iter
      (fun (_pos, opts, name) ->
        let existing = try Hashtbl.find tbl name with Not_found -> [] in
        if not (List.mem opts existing) then
          Hashtbl.replace tbl name (opts :: existing))
      pkgs;
    let cnt = ref 0 in
    Hashtbl.iter
      (fun _name opts_list -> if List.length opts_list > 1 then incr cnt)
      tbl;
    if !cnt > 0 then
      Some
        {
          id = "PKG-021";
          severity = Error;
          message = "Package loaded twice with conflicting options";
          count = !cnt;
        }
    else None
  in
  { id = "PKG-021"; run; languages = [] }

(* ── PKG-024: polyglossia language duplicated ────────────────────────── *)
let r_pkg_024 : rule =
  let re =
    Str.regexp {|\\\(setdefaultlanguage\|setotherlanguage\){\([^}]+\)}|}
  in
  let run s =
    let langs = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         let lang = Str.matched_group 2 s in
         langs := lang :: !langs;
         i := Str.match_end ()
       done
     with Not_found -> ());
    (* Check for duplicates *)
    let seen = Hashtbl.create 8 in
    let dups = ref 0 in
    List.iter
      (fun l ->
        if Hashtbl.mem seen l then incr dups else Hashtbl.add seen l true)
      (List.rev !langs);
    if !dups > 0 then
      Some
        {
          id = "PKG-024";
          severity = Warning;
          message = {|polyglossia language duplicated via \setdefaultlanguage|};
          count = !dups;
        }
    else None
  in
  { id = "PKG-024"; run; languages = [] }

(* ── PKG-025: Engine option mismatch ─────────────────────────────────── *)
(* Detect contradictory engine indicators, e.g. fontspec (XeLaTeX/LuaLaTeX)
   together with [T1]{fontenc} + [utf8]{inputenc} (pdfLaTeX). *)
let r_pkg_025 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    let has_xeluatex =
      List.exists (fun (_, _, name) -> name = "fontspec") pkgs
    in
    let has_pdftex_enc =
      List.exists
        (fun (_, opts, name) ->
          name = "fontenc" && contains_substring opts "T1")
        pkgs
    in
    let has_inputenc =
      List.exists (fun (_, _, name) -> name = "inputenc") pkgs
    in
    if has_xeluatex && has_pdftex_enc && has_inputenc then
      Some
        {
          id = "PKG-025";
          severity = Warning;
          message = "Engine option mismatch (xelatex=true on LuaLaTeX run)";
          count = 1;
        }
    else None
  in
  { id = "PKG-025"; run; languages = [] }

(* ── TAB-003: Decimal column not aligned on dot ─────────────────────── *)
(* Fire if tabular uses l/c/r columns with numeric data containing '.' but no S
   column or @{.} separator. *)
let r_tab_003 : rule =
  let colspec_re = Str.regexp {|\\begin{tabular\*?}{\([^}]+\)}|} in
  let _re_decimal = Str.regexp {|[0-9]+\.[0-9]|} in
  let run s =
    let blocks =
      extract_env_blocks "tabular" s @ extract_env_blocks "tabular*" s
    in
    let cnt =
      List.fold_left
        (fun acc body ->
          (* check if body contains decimal numbers *)
          let has_decimal =
            try
              ignore (Str.search_forward _re_decimal body 0);
              true
            with Not_found -> false
          in
          if not has_decimal then acc
          else
            (* check if colspec has S column *)
            let has_s_col =
              try
                let _ = Str.search_forward colspec_re s 0 in
                let spec = Str.matched_group 1 s in
                String.contains spec 'S' || contains_substring spec "@{.}"
              with Not_found -> false
            in
            if has_s_col then acc else acc + 1)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-003";
          severity = Info;
          message = "Decimal column not aligned on dot";
          count = cnt;
        }
    else None
  in
  { id = "TAB-003"; run; languages = [] }

(* ── TAB-007: Text in numeric column without \multicolumn ─────────── *)
(* Fire if S-column tabular contains text rows without \multicolumn *)
let r_tab_007 : rule =
  let _re_s_column = Str.regexp {|{[^}]*S[^}]*}|} in
  let _re_three_alpha = Str.regexp {|[a-zA-Z][a-zA-Z][a-zA-Z]|} in
  let run s =
    let blocks =
      extract_env_blocks "tabular" s @ extract_env_blocks "tabular*" s
    in
    let cnt =
      List.fold_left
        (fun acc body ->
          (* Check if tabular uses S columns *)
          let has_s =
            try
              ignore (Str.search_forward _re_s_column s 0);
              true
            with Not_found -> false
          in
          if not has_s then acc
          else
            (* Check for text in S columns without multicolumn *)
            let has_text_no_mc =
              try
                ignore (Str.search_forward _re_three_alpha body 0);
                let has_mc = contains_substring body "\\multicolumn" in
                not has_mc
              with Not_found -> false
            in
            if has_text_no_mc then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-007";
          severity = Info;
          message = {|Text in numeric column without \multicolumn|};
          count = cnt;
        }
    else None
  in
  { id = "TAB-007"; run; languages = [] }

(* ── TAB-008: Table > 30 rows ────────────────────────────────────────── *)
let r_tab_008 : rule =
  let linebreak_re = Str.regexp_string "\\\\" in
  let run s =
    let blocks =
      extract_env_blocks "tabular" s @ extract_env_blocks "tabular*" s
    in
    let cnt =
      List.fold_left
        (fun acc body ->
          let rows = List.length (Str.split linebreak_re body) in
          if rows > 30 then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-008";
          severity = Info;
          message = {|Table > 30 rows – suggest longtable/xtab|};
          count = cnt;
        }
    else None
  in
  { id = "TAB-008"; run; languages = [] }

(* ── TAB-012: Numeric column not aligned using siunitx S-column ──────── *)
let r_tab_012 : rule =
  let colspec_re = Str.regexp {|\\begin{tabular\*?}{\([^}]+\)}|} in
  let _re_end_tabular = Str.regexp_string "\\end{tabular" in
  let _re_numeric = Str.regexp {|[0-9]+\.?[0-9]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward colspec_re s !i in
         let spec = Str.matched_group 1 s in
         let after = Str.match_end () in
         (* Check if spec has r/c/l but no S *)
         let has_rcl = String.contains spec 'r' || String.contains spec 'l' in
         let has_s = String.contains spec 'S' in
         (if has_rcl && not has_s then
            (* Check if body has numbers *)
            let body_end =
              try Str.search_forward _re_end_tabular s after
              with Not_found -> String.length s
            in
            let body = String.sub s after (body_end - after) in
            let has_nums =
              try
                ignore (Str.search_forward _re_numeric body 0);
                true
              with Not_found -> false
            in
            if has_nums then incr cnt);
         i := after
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TAB-012";
          severity = Info;
          message = {|Numeric column not aligned using siunitx S‑column|};
          count = !cnt;
        }
    else None
  in
  { id = "TAB-012"; run; languages = [] }

(* ── TAB-013: Caption position for longtable must be at top ──────────── *)
let r_tab_013 : rule =
  let _re_caption_t13 = Str.regexp_string "\\caption" in
  let _re_linebreak_t13 = Str.regexp_string "\\\\" in
  let run s =
    let blocks = extract_env_blocks "longtable" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let has_caption = contains_substring body "\\caption" in
          if not has_caption then acc
          else
            let cap_pos =
              try Str.search_forward _re_caption_t13 body 0
              with Not_found -> 0
            in
            let first_row_pos =
              try Str.search_forward _re_linebreak_t13 body 0
              with Not_found -> String.length body
            in
            if cap_pos > first_row_pos then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-013";
          severity = Info;
          message = "Caption position for longtable must be at top per style";
          count = cnt;
        }
    else None
  in
  { id = "TAB-013"; run; languages = [] }

(* ── TAB-015: \multirow inside tabularx X without raggedright ────── *)
let r_tab_015 : rule =
  let run s =
    let blocks = extract_env_blocks "tabularx" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let has_multirow = contains_substring body "\\multirow" in
          let has_raggedright = contains_substring body "\\raggedright" in
          if has_multirow && not has_raggedright then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TAB-015";
          severity = Warning;
          message = {|\multirow inside tabularx column X without raggedright|};
          count = cnt;
        }
    else None
  in
  { id = "TAB-015"; run; languages = [] }

(* ── TAB-016: Centred 'c' column in longtable holds ragged text ──────── *)
let r_tab_016 : rule =
  let colspec_re = Str.regexp {|\\begin{longtable}{\([^}]+\)}|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward colspec_re s !i in
         let spec = Str.matched_group 1 s in
         if String.contains spec 'c' then incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TAB-016";
          severity = Info;
          message = "Centred 'c' column in longtable holds ragged text";
          count = !cnt;
        }
    else None
  in
  { id = "TAB-016"; run; languages = [] }

(* ── FIG-012: Figure listed in LoF but not referenced ────────────────── *)
let r_fig_012 : rule =
  let run s =
    let labels = extract_labels_with_prefix "fig:" s in
    let refs = extract_refs_with_prefix "fig:" s in
    let ref_keys = List.map snd refs in
    let cnt =
      List.fold_left
        (fun acc (_pos, key) ->
          if not (List.mem key ref_keys) then acc + 1 else acc)
        0 labels
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-012";
          severity = Info;
          message = "Figure listed in LoF but not referenced";
          count = cnt;
        }
    else None
  in
  { id = "FIG-012"; run; languages = [] }

(* ── FIG-014: Figure caption exceeds 300 characters ──────────────────── *)
let r_fig_014 : rule =
  let run s =
    let blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          match extract_caption_content body with
          | Some cap -> if String.length cap > 300 then acc + 1 else acc
          | None -> acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-014";
          severity = Info;
          message = {|Figure caption exceeds 300 characters|};
          count = cnt;
        }
    else None
  in
  { id = "FIG-014"; run; languages = [] }

(* ── FIG-017: Sidewaysfigure used with portrait page layout ──────────── *)
let r_fig_017 : rule =
  let re = Str.regexp_string "\\begin{sidewaysfigure" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    (* Only fire if no landscape geometry *)
    if !cnt > 0 then
      let has_landscape = contains_substring s "landscape" in
      if not has_landscape then
        Some
          {
            id = "FIG-017";
            severity = Warning;
            message = "Sidewaysfigure used with portrait page layout";
            count = !cnt;
          }
      else None
    else None
  in
  { id = "FIG-017"; run; languages = [] }

(* ── FIG-019: Subcaption label missing (a), (b)... ───────────────────── *)
(* Similar to FIG-010 but specifically checks that subcaption has label text *)
let r_fig_019 : rule =
  let run s =
    let blocks = extract_env_blocks_starred "subfigure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let has_subcap = contains_substring body "\\subcaption" in
          let has_caption = contains_substring body "\\caption" in
          if (not has_subcap) && not has_caption then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-019";
          severity = Info;
          message = {|Subcaption label missing (a), (b)…|};
          count = cnt;
        }
    else None
  in
  { id = "FIG-019"; run; languages = [] }

(* ── FIG-022: Figure caption identical to surrounding sentence ───────── *)
let r_fig_022 : rule =
  let _re_begin_figure = Str.regexp_string "\\begin{figure" in
  let run s =
    let blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          match extract_caption_content body with
          | None -> acc
          | Some cap ->
              let cap = String.trim cap in
              if String.length cap < 5 then acc
              else
                (* Search for caption text outside figure environments *)
                let outside =
                  try
                    let fig_start = Str.search_forward _re_begin_figure s 0 in
                    let before = String.sub s 0 fig_start in
                    contains_substring before cap
                  with Not_found -> false
                in
                if outside then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-022";
          severity = Info;
          message = "Figure caption identical to surrounding sentence";
          count = cnt;
        }
    else None
  in
  { id = "FIG-022"; run; languages = [] }

(* ── FIG-024: Alt-text exceeds 140 chars ─────────────────────────────── *)
let r_fig_024 : rule =
  let re = Str.regexp {|\\includegraphics\[[^]]*alt={\([^}]*\)}|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         let alt = Str.matched_group 1 s in
         if String.length alt > 140 then incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "FIG-024";
          severity = Info;
          message = {|Alt‑text exceeds 140 chars—trim for accessibility|};
          count = !cnt;
        }
    else None
  in
  { id = "FIG-024"; run; languages = [] }

(* ── FIG-025: Alt-text identical to caption ──────────────────────────── *)
let r_fig_025 : rule =
  let alt_re = Str.regexp {|\\includegraphics\[[^]]*alt={\([^}]*\)}|} in
  let run s =
    let blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let cap =
            match extract_caption_content body with
            | Some c -> String.trim c
            | None -> ""
          in
          if String.length cap < 3 then acc
          else
            let has_matching_alt =
              try
                let _ = Str.search_forward alt_re body 0 in
                let alt = String.trim (Str.matched_group 1 body) in
                alt = cap
              with Not_found -> false
            in
            if has_matching_alt then acc + 1 else acc)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "FIG-025";
          severity = Info;
          message = {|Alt‑text identical to caption—reduce redundancy|};
          count = cnt;
        }
    else None
  in
  { id = "FIG-025"; run; languages = [] }

(* ── MATH-075: Equation number suppressed with \nonumber but referenced *)
let r_math_075 : rule =
  let run s =
    (* Find labels in equation environments that also have \nonumber *)
    let eq_envs = [ "equation"; "align"; "gather"; "multline"; "flalign" ] in
    let cnt = ref 0 in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun body ->
            let has_nonumber = contains_substring body "\\nonumber" in
            if has_nonumber then
              let labels = extract_labels_with_prefix "eq:" body in
              let refs = extract_refs_with_prefix "eq:" s in
              let ref_keys = List.map snd refs in
              List.iter
                (fun (_pos, key) -> if List.mem key ref_keys then incr cnt)
                labels)
          blocks)
      eq_envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-075";
          severity = Warning;
          message = {|Equation number suppressed with \nonumber but referenced|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-075"; run; languages = [] }

(* ── MATH-080: Equation exceeds 3 alignment columns ─────────────────── *)
let r_math_080 : rule =
  let linebreak_re = Str.regexp_string "\\\\" in
  let run s =
    let cnt = ref 0 in
    let envs =
      [ "align"; "align*"; "flalign"; "flalign*"; "alignat"; "alignat*" ]
    in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun body ->
            let lines = Str.split linebreak_re body in
            List.iter
              (fun line ->
                let amps =
                  String.fold_left
                    (fun acc c -> if c = '&' then acc + 1 else acc)
                    0 line
                in
                if amps > 3 then incr cnt)
              lines)
          blocks)
      envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-080";
          severity = Info;
          message = "Equation exceeds 3 alignment columns";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-080"; run; languages = [] }

(* ── CMD-012: \renewcommand\thesection after hyperref ────────────── *)
let r_cmd_012 : rule =
  let re = Str.regexp_string "\\renewcommand{\\thesection}" in
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages preamble in
    let hyp_pos =
      List.fold_left
        (fun acc (pos, name) ->
          match acc with
          | Some _ -> acc
          | None -> if name = "hyperref" then Some pos else None)
        None pkgs
    in
    match hyp_pos with
    | None -> None
    | Some hp ->
        let found =
          try
            let p = Str.search_forward re preamble 0 in
            p > hp
          with Not_found -> false
        in
        if found then
          Some
            {
              id = "CMD-012";
              severity = Warning;
              message =
                {|\renewcommand\thesection redefined after hyperref — bookmark mismatch|};
              count = 1;
            }
        else None
  in
  { id = "CMD-012"; run; languages = [] }

(* ── DOC-004: Acknowledgment section before conclusion ───────────────── *)
let r_doc_004 : rule =
  let ack_re = Str.regexp {|\\section{[Aa]cknowledg|} in
  let conc_re = Str.regexp {|\\section{[Cc]onclusion|} in
  let run s =
    let ack_pos =
      try Some (Str.search_forward ack_re s 0) with Not_found -> None
    in
    let conc_pos =
      try Some (Str.search_forward conc_re s 0) with Not_found -> None
    in
    match (ack_pos, conc_pos) with
    | Some ap, Some cp ->
        if ap < cp then
          Some
            {
              id = "DOC-004";
              severity = Info;
              message = "Acknowledgment section before conclusion";
              count = 1;
            }
        else None
    | _ -> None
  in
  { id = "DOC-004"; run; languages = [] }

(* ══════════════════════════════════════════════════════════════════════
   L3-expl3 rules (L1_Expanded)
   ══════════════════════════════════════════════════════════════════════ *)

(* ── L3-001: LaTeX3 \tl_new:N in preamble mixed with 2e macros ──── *)
let r_l3_001 : rule =
  let expl3_re =
    Str.regexp
      {|\\\(tl\|cs\|int\|bool\|fp\|clist\|seq\|prop\)_\(new\|set\|gset\):|}
  in
  let latex2e_re =
    Str.regexp {|\\\(newcommand\|renewcommand\|def\)[^a-zA-Z]|}
  in
  let run s =
    let preamble = extract_preamble s in
    let has_expl3 =
      try
        ignore (Str.search_forward expl3_re preamble 0);
        true
      with Not_found -> false
    in
    let has_2e =
      try
        ignore (Str.search_forward latex2e_re preamble 0);
        true
      with Not_found -> false
    in
    if has_expl3 && has_2e then
      Some
        {
          id = "L3-001";
          severity = Info;
          message = {|LaTeX3 \tl_new:N in preamble mixed with 2e macros|};
          count = 1;
        }
    else None
  in
  { id = "L3-001"; run; languages = [] }

(* ── L3-002: Expl3 variable declared after \begin{document} ──────── *)
let r_l3_002 : rule =
  let expl3_decl_re =
    Str.regexp {|\\\(tl\|cs\|int\|bool\|fp\|clist\|seq\|prop\)_new:|}
  in
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body ->
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let _ = Str.search_forward expl3_decl_re body !i in
             incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "L3-002";
              severity = Warning;
              message = {|Expl3 variable declared after \begin{document}|};
              count = !cnt;
            }
        else None
  in
  { id = "L3-002"; run; languages = [] }

(* ── L3-003: Expl3 and etoolbox patch macros combined ────────────── *)
let r_l3_003 : rule =
  let expl3_re = Str.regexp {|\\\(tl\|cs\|int\|bool\)_\(new\|set\|gset\):|} in
  let etoolbox_re =
    Str.regexp {|\\\(patchcmd\|apptocmd\|pretocmd\|robustify\){|}
  in
  let run s =
    let has_expl3 =
      try
        ignore (Str.search_forward expl3_re s 0);
        true
      with Not_found -> false
    in
    let has_etoolbox =
      try
        ignore (Str.search_forward etoolbox_re s 0);
        true
      with Not_found -> false
    in
    if has_expl3 && has_etoolbox then
      Some
        {
          id = "L3-003";
          severity = Warning;
          message = "Expl3 and etoolbox patch macros combined";
          count = 1;
        }
    else None
  in
  { id = "L3-003"; run; languages = [] }

(* ── L3-004: Undocumented \__module_internal:N used ──────────────── *)
let r_l3_004 : rule =
  let re = Str.regexp {|\\__[a-zA-Z_]+:[a-zA-Z]*|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "L3-004";
          severity = Info;
          message = {|Undocumented \__module_internal:N used|};
          count = !cnt;
        }
    else None
  in
  { id = "L3-004"; run; languages = [] }

(* ── L3-005: Missing \ExplSyntaxOn guard around expl3 code ──────── *)
let r_l3_005 : rule =
  let expl3_re =
    Str.regexp {|\\\(tl\|cs\|int\|bool\|fp\|clist\|seq\|prop\)_|}
  in
  let run s =
    let has_expl3 =
      try
        ignore (Str.search_forward expl3_re s 0);
        true
      with Not_found -> false
    in
    let has_guard = contains_substring s "\\ExplSyntaxOn" in
    if has_expl3 && not has_guard then
      Some
        {
          id = "L3-005";
          severity = Error;
          message = {|Missing \ExplSyntaxOn guard around expl3 code|};
          count = 1;
        }
    else None
  in
  { id = "L3-005"; run; languages = [] }

(* ── L3-006: Expl3 variable clobbers package macro name ──────────── *)
let r_l3_006 : rule =
  let var_re =
    Str.regexp {|\\\(l\|g\)_\([a-zA-Z]+\)_\(tl\|int\|bool\|clist\|seq\|prop\)|}
  in
  let cmd_re = Str.regexp {|\\\(newcommand\|renewcommand\){\\\([a-zA-Z]+\)}|} in
  let run s =
    let var_names = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward var_re s !i in
         let name = Str.matched_group 2 s in
         var_names := name :: !var_names;
         i := Str.match_end ()
       done
     with Not_found -> ());
    let cmd_names = ref [] in
    let j = ref 0 in
    (try
       while true do
         let _ = Str.search_forward cmd_re s !j in
         let name = Str.matched_group 2 s in
         cmd_names := name :: !cmd_names;
         j := Str.match_end ()
       done
     with Not_found -> ());
    let cnt =
      List.fold_left
        (fun acc vn -> if List.mem vn !cmd_names then acc + 1 else acc)
        0 !var_names
    in
    if cnt > 0 then
      Some
        {
          id = "L3-006";
          severity = Warning;
          message = "Expl3 variable clobbers package macro name";
          count = cnt;
        }
    else None
  in
  { id = "L3-006"; run; languages = [] }

(* ── L3-007: Mix of camelCase and snake_case in expl3 names ──────── *)
let r_l3_007 : rule =
  let camel_re = Str.regexp {|\\[a-z]+[A-Z][a-zA-Z]*[{ ]|} in
  let snake_re = Str.regexp {|\\[a-z]+_[a-z]+:|} in
  let run s =
    let has_camel =
      try
        ignore (Str.search_forward camel_re s 0);
        true
      with Not_found -> false
    in
    let has_snake =
      try
        ignore (Str.search_forward snake_re s 0);
        true
      with Not_found -> false
    in
    if has_camel && has_snake then
      Some
        {
          id = "L3-007";
          severity = Info;
          message = "Mix of camelCase and snake_case in expl3 names";
          count = 1;
        }
    else None
  in
  { id = "L3-007"; run; languages = [] }

(* ── L3-009: LaTeX3 function deprecated _n: variant used ─────────── *)
let r_l3_009 : rule =
  let re =
    Str.regexp
      {|\\\(tl\|cs\|int\|bool\|fp\|clist\|seq\|prop\)_[a-z_]+:n[^a-zA-Z]|}
  in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "L3-009";
          severity = Info;
          message = "LaTeX3 function deprecated _n: variant used";
          count = !cnt;
        }
    else None
  in
  { id = "L3-009"; run; languages = [] }

(* ── L3-011: Engine-branch uses pdfTeX primitive in Lua/XeTeX path ─ *)
let r_l3_011 : rule =
  let pdftex_re =
    Str.regexp
      {|\\\(pdfoutput\|pdfliteral\|pdfcatalog\|pdfinfo\|pdfcompresslevel\)|}
  in
  let luaxe_re = Str.regexp {|\\sys_if_engine_\(luatex\|xetex\):|} in
  let run s =
    let has_pdftex =
      try
        ignore (Str.search_forward pdftex_re s 0);
        true
      with Not_found -> false
    in
    let has_luaxe =
      try
        ignore (Str.search_forward luaxe_re s 0);
        true
      with Not_found -> false
    in
    if has_pdftex && has_luaxe then
      Some
        {
          id = "L3-011";
          severity = Warning;
          message = "Engine‑branch uses pdfTeX primitive in Lua/XeTeX path";
          count = 1;
        }
    else None
  in
  { id = "L3-011"; run; languages = [] }

(* ====================================================================== TIKZ
   rules (L2_Ast)
   ====================================================================== *)

(* -- TIKZ-001: TikZ picture outside figure environment --------------- *)
let r_tikz_001 : rule =
  let tikz_re = Str.regexp_string "\\begin{tikzpicture}" in
  let run s =
    let fig_blocks = extract_env_blocks_starred "figure" s in
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward tikz_re s !i in
         let inside_fig =
           List.exists
             (fun body -> contains_substring body "\\begin{tikzpicture}")
             fig_blocks
         in
         if not inside_fig then incr cnt;
         i := pos + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TIKZ-001";
          severity = Info;
          message = "TikZ picture outside figure environment";
          count = !cnt;
        }
    else None
  in
  { id = "TIKZ-001"; run; languages = [] }

(* -- TIKZ-003: pgfplots axis labels not in math mode ----------------- *)
let r_tikz_003 : rule =
  let label_re = Str.regexp {|\(xlabel\|ylabel\|zlabel\)={\([^}]*\)}|} in
  let run s =
    let blocks = extract_env_blocks "axis" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let c = ref 0 in
          let i = ref 0 in
          (try
             while true do
               let _ = Str.search_forward label_re body !i in
               let label_text = Str.matched_group 2 body in
               let has_math = String.contains label_text '$' in
               if not has_math then incr c;
               i := Str.match_end ()
             done
           with Not_found -> ());
          acc + !c)
        0 blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TIKZ-003";
          severity = Info;
          message = "pgfplots axis labels not in math mode";
          count = cnt;
        }
    else None
  in
  { id = "TIKZ-003"; run; languages = [] }

(* -- TIKZ-004: Hard-coded RGB values instead of xcolor names --------- *)
let r_tikz_004 : rule =
  let re = Str.regexp {|\(color\|fill\|draw\)={\(rgb\|RGB\)|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TIKZ-004";
          severity = Info;
          message = "Hard‑coded RGB values instead of xcolor names";
          count = !cnt;
        }
    else None
  in
  { id = "TIKZ-004"; run; languages = [] }

(* -- TIKZ-006: Missing \caption for tikzpicture inside figure ------- *)
let r_tikz_006 : rule =
  let run s =
    let fig_blocks = extract_env_blocks_starred "figure" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let has_tikz = contains_substring body "\\begin{tikzpicture}" in
          let has_caption = contains_substring body "\\caption" in
          if has_tikz && not has_caption then acc + 1 else acc)
        0 fig_blocks
    in
    if cnt > 0 then
      Some
        {
          id = "TIKZ-006";
          severity = Warning;
          message = {|Missing \caption for tikzpicture inside figure|};
          count = cnt;
        }
    else None
  in
  { id = "TIKZ-006"; run; languages = [] }

(* -- TIKZ-009: TikZ library arrows.meta missing for arrow tips ------- *)
let r_tikz_009 : rule =
  let arrow_re = Str.regexp "->\\|stealth\\|-latex" in
  let run s =
    let has_arrows =
      try
        let blocks = extract_env_blocks "tikzpicture" s in
        List.exists
          (fun body ->
            try
              ignore (Str.search_forward arrow_re body 0);
              true
            with Not_found -> false)
          blocks
      with Not_found -> false
    in
    if not has_arrows then None
    else
      let has_lib = contains_substring s "arrows.meta" in
      if not has_lib then
        Some
          {
            id = "TIKZ-009";
            severity = Info;
            message = "TikZ library arrows.meta missing for arrow tips";
            count = 1;
          }
      else None
  in
  { id = "TIKZ-009"; run; languages = [] }

(* -- TIKZ-010: Deprecated \pgfplotsset key used -------------------- *)
let r_tikz_010 : rule =
  let re =
    Str.regexp {|\\pgfplotsset{[^}]*\(every axis\|compat=1\.[0-7]\)[^}]*}|}
  in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "TIKZ-010";
          severity = Info;
          message = {|Deprecated \pgfplotsset key used|};
          count = !cnt;
        }
    else None
  in
  { id = "TIKZ-010"; run; languages = [] }

(* ====================================================================== LANG +
   Other L2_Ast rules
   ====================================================================== *)

(* -- LANG-001: \usepackage[british]{babel} but US spelling ---------- *)
let r_lang_001 : rule =
  let us_words =
    [
      "color";
      "center";
      "defense";
      "offense";
      "analyze";
      "organize";
      "recognize";
      "favor";
      "honor";
      "neighbor";
      "labor";
    ]
  in
  let _re_british = Str.regexp {|british\|UKenglish|} in
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    let has_british =
      List.exists
        (fun (_pos, opts, name) ->
          name = "babel"
          &&
          try
            ignore (Str.search_forward _re_british opts 0);
            true
          with Not_found -> false)
        pkgs
    in
    if not has_british then None
    else
      match extract_document_body s with
      | None -> None
      | Some body ->
          let body_lc = String.lowercase_ascii body in
          let cnt =
            List.fold_left
              (fun acc w ->
                if contains_substring body_lc w then acc + 1 else acc)
              0 us_words
          in
          if cnt > 0 then
            Some
              {
                id = "LANG-001";
                severity = Info;
                message =
                  {|\usepackage[british]{babel} but US spelling detected|};
                count = cnt;
              }
          else None
  in
  { id = "LANG-001"; run; languages = [] }

(* -- LANG-006: Non-English abstract before \selectlanguage ---------- *)
let r_lang_006 : rule =
  let _re_begin_abstract = Str.regexp_string "\\begin{abstract}" in
  let _re_selectlang = Str.regexp_string "\\selectlanguage" in
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body -> (
        let abs_pos =
          try Some (Str.search_forward _re_begin_abstract body 0)
          with Not_found -> None
        in
        let lang_pos =
          try Some (Str.search_forward _re_selectlang body 0)
          with Not_found -> None
        in
        match (abs_pos, lang_pos) with
        | Some ap, Some lp ->
            if ap < lp then
              Some
                {
                  id = "LANG-006";
                  severity = Info;
                  message = "Non‑English abstract before \\selectlanguage";
                  count = 1;
                }
            else None
        | _ -> None)
  in
  { id = "LANG-006"; run; languages = [] }

(* -- LANG-007: babel shorthand mis-used instead of og/fg ----------- *)
let r_lang_007 : rule =
  let shorthand_re = Str.regexp {|""|} in
  let _re_french = Str.regexp {|french\|francais|} in
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    let has_french =
      List.exists
        (fun (_pos, opts, name) ->
          name = "babel"
          &&
          try
            ignore (Str.search_forward _re_french opts 0);
            true
          with Not_found -> false)
        pkgs
    in
    if not has_french then None
    else
      match extract_document_body s with
      | None -> None
      | Some body ->
          let cnt = ref 0 in
          let i = ref 0 in
          (try
             while true do
               let _ = Str.search_forward shorthand_re body !i in
               incr cnt;
               i := Str.match_end ()
             done
           with Not_found -> ());
          if !cnt > 0 then
            Some
              {
                id = "LANG-007";
                severity = Info;
                message = "babel shorthand \" mis‑used instead of \\og … \\fg";
                count = !cnt;
              }
          else None
  in
  { id = "LANG-007"; run; languages = [] }

(* -- LANG-013: Abstract language differs from \selectlanguage ------- *)
let r_lang_013 : rule =
  let lang_re = Str.regexp {|\\selectlanguage{\([^}]+\)}|} in
  let _re_begin_abstract_l13 = Str.regexp_string "\\begin{abstract}" in
  let _re_end_abstract = Str.regexp_string "\\end{abstract}" in
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body -> (
        let abs_pos =
          try Some (Str.search_forward _re_begin_abstract_l13 body 0)
          with Not_found -> None
        in
        match abs_pos with
        | None -> None
        | Some ap -> (
            let abs_end =
              try
                Str.search_forward _re_end_abstract body ap
                + String.length "\\end{abstract}"
              with Not_found -> ap
            in
            let before_abs = String.sub body 0 ap in
            let after_abs =
              String.sub body abs_end (String.length body - abs_end)
            in
            let lang_before =
              try
                let _ = Str.search_forward lang_re before_abs 0 in
                Some (Str.matched_group 1 before_abs)
              with Not_found -> None
            in
            let lang_after =
              try
                let _ = Str.search_forward lang_re after_abs 0 in
                Some (Str.matched_group 1 after_abs)
              with Not_found -> None
            in
            match (lang_before, lang_after) with
            | Some lb, Some la when lb <> la ->
                Some
                  {
                    id = "LANG-013";
                    severity = Info;
                    message = {|Abstract language differs from \selectlanguage|};
                    count = 1;
                  }
            | _ -> None))
  in
  { id = "LANG-013"; run; languages = [] }

(* -- COL-006: xcolor option dvipsnames used with pdfLaTeX ------------ *)
let r_col_006 : rule =
  let run s =
    let preamble = extract_preamble s in
    let pkgs = extract_usepackages_with_opts preamble in
    let has_dvips_xcolor =
      List.exists
        (fun (_pos, opts, name) ->
          name = "xcolor" && contains_substring opts "dvipsnames")
        pkgs
    in
    if not has_dvips_xcolor then None
    else
      let has_pdftex =
        List.exists
          (fun (_, opts, name) ->
            (name = "fontenc" && contains_substring opts "T1")
            || name = "inputenc")
          pkgs
      in
      if has_pdftex then
        Some
          {
            id = "COL-006";
            severity = Warning;
            message = "xcolor option dvipsnames used with pdfLaTeX";
            count = 1;
          }
      else None
  in
  { id = "COL-006"; run; languages = [] }

(* -- L3-008: Expl3 module lacks \ProvidesExplPackage ---------------- *)
let r_l3_008 : rule =
  let expl3_re =
    Str.regexp {|\\\(tl\|cs\|int\|bool\|fp\|clist\|seq\|prop\)_|}
  in
  let _re_provides_expl = Str.regexp_string "\\ProvidesExplPackage" in
  let run s =
    let has_expl3 =
      try
        ignore (Str.search_forward expl3_re s 0);
        true
      with Not_found -> false
    in
    let has_provides =
      try
        ignore (Str.search_forward _re_provides_expl s 0);
        true
      with Not_found -> contains_substring s "\\ProvidesExplClass"
    in
    if has_expl3 && not has_provides then
      Some
        {
          id = "L3-008";
          severity = Warning;
          message = {|Expl3 module lacks \ProvidesExplPackage|};
          count = 1;
        }
    else None
  in
  { id = "L3-008"; run; languages = [] }

(* -- L3-010: \ExplSyntaxOff missing at end of file ----------------- *)
let r_l3_010 : rule =
  let on_re = Str.regexp_string "\\ExplSyntaxOn" in
  let off_re = Str.regexp_string "\\ExplSyntaxOff" in
  let run s =
    let count_matches re str =
      let cnt = ref 0 in
      let i = ref 0 in
      (try
         while true do
           let _ = Str.search_forward re str !i in
           incr cnt;
           i := Str.match_end ()
         done
       with Not_found -> ());
      !cnt
    in
    let on_count = count_matches on_re s in
    let off_count = count_matches off_re s in
    if on_count > 0 && on_count > off_count then
      Some
        {
          id = "L3-010";
          severity = Info;
          message = {|\ExplSyntaxOff missing at end of file|};
          count = on_count - off_count;
        }
    else None
  in
  { id = "L3-010"; run; languages = [] }

(* -- LAY-024: \subsubsubsection depth > 3 without class support ---- *)
let r_lay_024 : rule =
  let re = Str.regexp_string "\\subsubsubsection" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "LAY-024";
          severity = Warning;
          message = "\\subsubsubsection depth > 3 without class support";
          count = !cnt;
        }
    else None
  in
  { id = "LAY-024"; run; languages = [] }

(* -- META-002: Revision hash missing from \date field --------------- *)
let r_meta_002 : rule =
  let date_re = Str.regexp {|\\date{\([^}]*\)}|} in
  let hash_re =
    Str.regexp "[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]"
  in
  let run s =
    let preamble = extract_preamble s in
    let has_date =
      try
        let _ = Str.search_forward date_re preamble 0 in
        let date_content = Str.matched_group 1 preamble in
        let has_hash =
          try
            ignore (Str.search_forward hash_re date_content 0);
            true
          with Not_found -> false
        in
        Some (not has_hash)
      with Not_found -> None
    in
    match has_date with
    | Some true ->
        Some
          {
            id = "META-002";
            severity = Info;
            message = {|Revision hash missing from \date field|};
            count = 1;
          }
    | _ -> None
  in
  { id = "META-002"; run; languages = [] }

(* -- RTL-005: Polyglossia RTL font not specified --------------------- *)
let r_rtl_005 : rule =
  let rtl_langs =
    [
      "arabic";
      "hebrew";
      "persian";
      "farsi";
      "urdu";
      "pashto";
      "sindhi";
      "kurdish";
    ]
  in
  let _re_newfontfamily = Str.regexp_string "\\newfontfamily" in
  let run s =
    let has_rtl_lang =
      List.exists (fun lang -> contains_substring s lang) rtl_langs
    in
    let has_polyglossia = has_package s "polyglossia" in
    if has_rtl_lang && has_polyglossia then
      let has_font_spec =
        try
          ignore (Str.search_forward _re_newfontfamily s 0);
          true
        with Not_found -> contains_substring s "\\setmainfont"
      in
      if not has_font_spec then
        Some
          {
            id = "RTL-005";
            severity = Warning;
            message = "Polyglossia RTL font not specified";
            count = 1;
          }
      else None
    else None
  in
  { id = "RTL-005"; run; languages = [ "ar"; "he" ] }

(* ── BIB rules: bibliography field / entry hygiene ──────────────── *)

(* BIB-002: DOI not normalised to https://doi.org/ form *)
let r_bib_002 : rule =
  let re_doi = Str.regexp {|doi[ \t]*=[ \t]*{|} in
  let re_good = Str.regexp_string "https://doi.org/" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re_doi s !i in
         let after = Str.match_end () in
         let is_good =
           try
             let _ = Str.search_forward re_good s after in
             Str.match_beginning () = after
           with Not_found -> false
         in
         if not is_good then incr cnt;
         i := pos + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-002";
          severity = Info;
          message = "DOI not normalised to https://doi.org/ form";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-002"; run; languages = [] }

(* BIB-003: Journal title capitalisation inconsistent with @string definition *)
let r_bib_003 : rule =
  let re_journal = Str.regexp {|journal[ \t]*=[ \t]*{|} in
  let re_cap_word = Str.regexp {|[A-Z][a-z]+|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re_journal s !i in
         let after = Str.match_end () in
         (* find closing brace *)
         let j = ref after in
         let depth = ref 1 in
         let n = String.length s in
         while !j < n && !depth > 0 do
           (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
           if !depth > 0 then incr j
         done;
         let content = String.sub s after (!j - after) in
         (* Count capitalised words *)
         let cap_count = count_matches re_cap_word content in
         if cap_count >= 2 then incr cnt;
         i := pos + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-003";
          severity = Info;
          message =
            "Journal title capitalisation inconsistent with @string definition";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-003"; run; languages = [] }

(* BIB-004: Book entry lacks publisher field *)
let r_bib_004 : rule =
  let re_book = Str.regexp {|@[Bb]ook{|} in
  let re_publisher = Str.regexp {|publisher[ \t]*=|} in
  let run s =
    let entries = split_bib_entries s in
    let cnt = ref 0 in
    List.iter
      (fun entry ->
        let is_book =
          try
            let _ = Str.search_forward re_book entry 0 in
            true
          with Not_found -> false
        in
        if is_book then
          let has_pub =
            try
              let _ = Str.search_forward re_publisher entry 0 in
              true
            with Not_found -> false
          in
          if not has_pub then incr cnt)
      entries;
    if !cnt > 0 then
      Some
        {
          id = "BIB-004";
          severity = Warning;
          message = "Book entry lacks publisher field";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-004"; run; languages = [] }

(* BIB-005: URL present without urldate *)
let r_bib_005 : rule =
  let re_url = Str.regexp {|url[ \t]*=[ \t]*{|} in
  let re_urldate = Str.regexp {|urldate[ \t]*=[ \t]*{|} in
  let run s =
    let entries = split_bib_entries s in
    let cnt = ref 0 in
    List.iter
      (fun entry ->
        (* Count url= matches minus urldate= matches to get true url count *)
        let url_count = count_matches re_url entry in
        let urldate_count = count_matches re_urldate entry in
        let has_url = url_count > urldate_count in
        if has_url then
          let has_urldate = urldate_count > 0 in
          if not has_urldate then incr cnt)
      entries;
    if !cnt > 0 then
      Some
        {
          id = "BIB-005";
          severity = Info;
          message = "URL present without urldate";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-005"; run; languages = [] }

(* BIB-006: Author/editor names not in "von Last, First" scheme *)
let r_bib_006 : rule =
  let re_author = Str.regexp {|author[ \t]*=[ \t]*{|} in
  let re_first_last = Str.regexp {|{[A-Z][a-z]+ [A-Z]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re_author s !i in
         let after = Str.match_end () in
         (* find closing brace *)
         let j = ref after in
         let depth = ref 1 in
         let n = String.length s in
         while !j < n && !depth > 0 do
           (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
           if !depth > 0 then incr j
         done;
         let content = String.sub s (after - 1) (!j - after + 2) in
         let is_first_last =
           try
             let _ = Str.search_forward re_first_last content 0 in
             (* Check there's no comma before the match — if comma present, it's
                "Last, First" which is fine *)
             let matched_pos = Str.match_beginning () in
             let before = String.sub content 0 matched_pos in
             not (String.contains before ',')
           with Not_found -> false
         in
         if is_first_last then incr cnt;
         i := pos + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-006";
          severity = Info;
          message = "Author/editor names not in “von Last, First” scheme";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-006"; run; languages = [] }

(* BIB-008: Camel-case field names detected *)
let r_bib_008 : rule =
  let re = Str.regexp {|[A-Z][a-z]+ *= *{|} in
  let re_entry = Str.regexp "@[a-zA-Z]+{" in
  let run s =
    (* Only flag inside bib entries *)
    let has_bib =
      try
        let _ = Str.search_forward re_entry s 0 in
        true
      with Not_found -> false
    in
    if not has_bib then None
    else
      let cnt = count_matches re s in
      if cnt > 0 then
        Some
          {
            id = "BIB-008";
            severity = Info;
            message = "Camel‑case field names detected (e.g. `Title` → `title`)";
            count = cnt;
          }
      else None
  in
  { id = "BIB-008"; run; languages = [] }

(* BIB-009: In-proceedings entry missing required `booktitle` field *)
let r_bib_009 : rule =
  let re_inproc = Str.regexp {|@[Ii]n[Pp]roceedings{|} in
  let re_booktitle = Str.regexp {|booktitle[ \t]*=|} in
  let run s =
    let entries = split_bib_entries s in
    let cnt = ref 0 in
    List.iter
      (fun entry ->
        let is_inproc =
          try
            let _ = Str.search_forward re_inproc entry 0 in
            true
          with Not_found -> false
        in
        if is_inproc then
          let has_bt =
            try
              let _ = Str.search_forward re_booktitle entry 0 in
              true
            with Not_found -> false
          in
          if not has_bt then incr cnt)
      entries;
    if !cnt > 0 then
      Some
        {
          id = "BIB-009";
          severity = Error;
          message = "In‑proceedings entry missing required `booktitle` field";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-009"; run; languages = [] }

(* BIB-010: `month` field uses numeric literal instead of `#jan#` macro *)
let r_bib_010 : rule =
  let re = Str.regexp {|month[ \t]*=[ \t]*[{0-9"]|} in
  let run s =
    let cnt = count_matches re s in
    if cnt > 0 then
      Some
        {
          id = "BIB-010";
          severity = Info;
          message =
            "`month` field uses numeric literal instead of `#jan#` macro";
          count = cnt;
        }
    else None
  in
  { id = "BIB-010"; run; languages = [] }

(* BIB-011: Legacy `note = {URL: ...}` field detected; move to `url` *)
let r_bib_011 : rule =
  let re = Str.regexp {|note[ \t]*=[ \t]*{\(URL:\|http\)|} in
  let run s =
    let cnt = count_matches re s in
    if cnt > 0 then
      Some
        {
          id = "BIB-011";
          severity = Info;
          message = "Legacy `note = {URL: …}` field detected; move to `url`";
          count = cnt;
        }
    else None
  in
  { id = "BIB-011"; run; languages = [] }

(* BIB-012: `et al.` hard-coded in author list instead of letting Bib(La)TeX
   truncate *)
let r_bib_012 : rule =
  let re_author = Str.regexp {|author[ \t]*=[ \t]*{|} in
  let re_etal = Str.regexp_string "et al." in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re_author s !i in
         let after = Str.match_end () in
         (* find closing brace *)
         let j = ref after in
         let depth = ref 1 in
         let n = String.length s in
         while !j < n && !depth > 0 do
           (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
           if !depth > 0 then incr j
         done;
         let content = String.sub s after (!j - after) in
         let has_etal =
           try
             let _ = Str.search_forward re_etal content 0 in
             true
           with Not_found -> false
         in
         if has_etal then incr cnt;
         i := pos + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-012";
          severity = Warning;
          message =
            "`et al.` hard‑coded in author list instead of letting Bib(La)TeX \
             truncate";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-012"; run; languages = [] }

(* BIB-015: Trailing period in `title` or `note` field is redundant *)
let r_bib_015 : rule =
  let re = Str.regexp {|\(title\|note\)[ \t]*=[ \t]*{|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re s !i in
         let after = Str.match_end () in
         (* find closing brace *)
         let j = ref after in
         let depth = ref 1 in
         let n = String.length s in
         while !j < n && !depth > 0 do
           (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
           if !depth > 0 then incr j
         done;
         (* Check if char before closing brace is a period *)
         if !j > after && s.[!j - 1] = '.' then incr cnt;
         i := pos + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-015";
          severity = Info;
          message = "Trailing period in `title` or `note` field is redundant";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-015"; run; languages = [] }

(* BIB-016: Both DOI and URL present — duplicate locator information *)
let r_bib_016 : rule =
  let re_doi = Str.regexp {|doi[ \t]*=[ \t]*{|} in
  let re_url = Str.regexp {|url[ \t]*=[ \t]*{|} in
  let re_urldate = Str.regexp {|urldate[ \t]*=[ \t]*{|} in
  let run s =
    let entries = split_bib_entries s in
    let cnt = ref 0 in
    List.iter
      (fun entry ->
        let has_doi =
          try
            let _ = Str.search_forward re_doi entry 0 in
            true
          with Not_found -> false
        in
        (* Count url= matches minus urldate= matches to get true url count *)
        let url_count = count_matches re_url entry in
        let urldate_count = count_matches re_urldate entry in
        let has_url = url_count > urldate_count in
        if has_doi && has_url then incr cnt)
      entries;
    if !cnt > 0 then
      Some
        {
          id = "BIB-016";
          severity = Info;
          message = "Both DOI and URL present—duplicate locator information";
          count = !cnt;
        }
    else None
  in
  { id = "BIB-016"; run; languages = [] }

(* ── PKG rules: package configuration issues ───────────────────── *)

(* PKG-018: hyperref option draft left enabled *)
let r_pkg_018 : rule =
  let re_pkg = Str.regexp {|\\usepackage\[[^]]*draft[^]]*\]{hyperref}|} in
  let re_setup1 = Str.regexp_string "\\hypersetup{draft}" in
  let re_setup2 = Str.regexp_string "\\hypersetup{draft=true" in
  let re_setup3 = Str.regexp {|\\hypersetup{[^}]*draft=true|} in
  let run s =
    let c1 = count_matches re_pkg s in
    let c2 = count_matches re_setup1 s in
    let c3 = count_matches re_setup2 s in
    let c4 = count_matches re_setup3 s in
    let cnt = c1 + c2 + c3 + c4 in
    (* Avoid double-counting: re_setup2 is prefix of re_setup3 matches *)
    let cnt = min cnt (c1 + max c2 0 + max c4 c3) in
    if cnt > 0 then
      Some
        {
          id = "PKG-018";
          severity = Info;
          message = "hyperref option draft left enabled";
          count = cnt;
        }
    else None
  in
  { id = "PKG-018"; run; languages = [] }

(* PKG-019: geometry margin < 1 cm *)
let r_pkg_019 : rule =
  let re_margin_frac =
    Str.regexp
      {|\\\(usepackage\[[^]]*\|geometry{[^}]*\)\(margin\|left\|right\|top\|bottom\)=0\.[0-9]+cm|}
  in
  let re_margin_zero =
    Str.regexp
      {|\\\(usepackage\[[^]]*\|geometry{[^}]*\)\(margin\|left\|right\|top\|bottom\)=0cm|}
  in
  let run s =
    let c1 = count_matches re_margin_frac s in
    let c2 = count_matches re_margin_zero s in
    let cnt = c1 + c2 in
    if cnt > 0 then
      Some
        {
          id = "PKG-019";
          severity = Warning;
          message = "geometry margin < 1 cm";
          count = cnt;
        }
    else None
  in
  { id = "PKG-019"; run; languages = [] }

(* ── FONT rules ────────────────────────────────────────────────── *)

(* FONT-005: Fontspec fallback to Latin Modern detected *)
let r_font_005 : rule =
  let re_fontspec = Str.regexp_string "\\usepackage{fontspec}" in
  let re_setmain = Str.regexp_string "\\setmainfont" in
  let re_lm = Str.regexp_string "\\setmainfont{Latin Modern" in
  let run s =
    let has_fontspec =
      try
        let _ = Str.search_forward re_fontspec s 0 in
        true
      with Not_found -> false
    in
    if not has_fontspec then None
    else
      let has_setmain =
        try
          let _ = Str.search_forward re_setmain s 0 in
          true
        with Not_found -> false
      in
      if has_setmain then
        (* Check if it explicitly sets Latin Modern *)
        let is_lm =
          try
            let _ = Str.search_forward re_lm s 0 in
            true
          with Not_found -> false
        in
        if is_lm then
          Some
            {
              id = "FONT-005";
              severity = Info;
              message = "Fontspec fallback to Latin Modern detected";
              count = 1;
            }
        else None
      else
        Some
          {
            id = "FONT-005";
            severity = Info;
            message = "Fontspec fallback to Latin Modern detected";
            count = 1;
          }
  in
  { id = "FONT-005"; run; languages = [] }

(* ── LAY rules: layout / spacing issues ────────────────────────── *)

(* LAY-015: Line spacing < 1 or > 2 *)
let r_lay_015 : rule =
  let re_linespread = Str.regexp {|\\linespread{\([0-9.]+\)}|} in
  let re_setstretch = Str.regexp {|\\setstretch{\([0-9.]+\)}|} in
  let run s =
    let cnt = ref 0 in
    let check re =
      let i = ref 0 in
      try
        while true do
          let _ = Str.search_forward re s !i in
          let v = Str.matched_group 1 s in
          (try
             let f = float_of_string v in
             if f < 1.0 || f > 2.0 then incr cnt
           with Failure _ -> ());
          i := Str.match_end ()
        done
      with Not_found -> ()
    in
    check re_linespread;
    check re_setstretch;
    if !cnt > 0 then
      Some
        {
          id = "LAY-015";
          severity = Info;
          message = "Line spacing < 1 or > 2";
          count = !cnt;
        }
    else None
  in
  { id = "LAY-015"; run; languages = [] }

(* LAY-020: Float placement parameters modified (\topnumber ...) *)
let r_lay_020 : rule =
  let re_counter =
    Str.regexp {|\\setcounter{\(topnumber\|bottomnumber\|totalnumber\)}|}
  in
  let re_fraction = Str.regexp {|\\renewcommand{\\topfraction}|} in
  let run s =
    let c1 = count_matches re_counter s in
    let c2 = count_matches re_fraction s in
    let cnt = c1 + c2 in
    if cnt > 0 then
      Some
        {
          id = "LAY-020";
          severity = Info;
          message = "Float placement parameters modified (\\topnumber …)";
          count = cnt;
        }
    else None
  in
  { id = "LAY-020"; run; languages = [] }

(* LAY-022: Global negative \parskip detected *)
let r_lay_022 : rule =
  let re = Str.regexp_string "\\setlength{\\parskip}{-" in
  let run s =
    let cnt = count_matches re s in
    if cnt > 0 then
      Some
        {
          id = "LAY-022";
          severity = Warning;
          message = {|Global negative \parskip detected|};
          count = cnt;
        }
    else None
  in
  { id = "LAY-022"; run; languages = [] }

(* ── REF rules ─────────────────────────────────────────────────── *)

(* REF-008: Duplicate cite key in .bib file *)
let r_ref_008 : rule =
  let re_entry = Str.regexp {|@[a-zA-Z]+{[ \t]*\([^, \t\n}]+\)|} in
  let run s =
    let keys = Hashtbl.create 64 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re_entry s !i in
         let key = Str.matched_group 1 s in
         (match Hashtbl.find_opt keys key with
         | Some n -> Hashtbl.replace keys key (n + 1)
         | None -> Hashtbl.replace keys key 1);
         i := Str.match_end ()
       done
     with Not_found -> ());
    let cnt =
      Hashtbl.fold (fun _ n acc -> if n > 1 then acc + 1 else acc) keys 0
    in
    if cnt > 0 then
      Some
        {
          id = "REF-008";
          severity = Warning;
          message = "Duplicate cite key in .bib file";
          count = cnt;
        }
    else None
  in
  { id = "REF-008"; run; languages = [] }

(* ── META rules ────────────────────────────────────────────────── *)

(* META-001: PDF /Producer not set to deterministic hash *)
let r_meta_001 : rule =
  let re_hyperref_with_opts = Str.regexp {|\\usepackage\[[^]]*\]{hyperref}|} in
  let re_hyperref_no_opts = Str.regexp_string "\\usepackage{hyperref}" in
  let re_producer = Str.regexp_string "pdfproducer=" in
  let run s =
    let has_hyperref =
      try
        let _ = Str.search_forward re_hyperref_with_opts s 0 in
        true
      with Not_found -> (
        try
          let _ = Str.search_forward re_hyperref_no_opts s 0 in
          true
        with Not_found -> false)
    in
    if not has_hyperref then None
    else
      let has_producer =
        try
          let _ = Str.search_forward re_producer s 0 in
          true
        with Not_found -> false
      in
      if has_producer then None
      else
        Some
          {
            id = "META-001";
            severity = Info;
            message = "PDF /Producer not set to deterministic hash";
            count = 1;
          }
  in
  { id = "META-001"; run; languages = [] }

(* ── PDF rules ─────────────────────────────────────────────────── *)

(* PDF-010: Outline/bookmark text contains '_' or '#' -- use \texorpdfstring *)
let r_pdf_010 : rule =
  let re_sec =
    Str.regexp {|\\\(section\|subsection\|subsubsection\|chapter\){|}
  in
  let re_texorpdf = Str.regexp_string "\\texorpdfstring" in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    let n = String.length s in
    (try
       while true do
         let pos = Str.search_forward re_sec s !i in
         let after = Str.match_end () in
         (* find matching closing brace *)
         let j = ref after in
         let depth = ref 1 in
         while !j < n && !depth > 0 do
           (match s.[!j] with '{' -> incr depth | '}' -> decr depth | _ -> ());
           if !depth > 0 then incr j
         done;
         let content = String.sub s after (!j - after) in
         let has_special =
           String.contains content '_' || String.contains content '#'
         in
         let has_texorpdf =
           try
             let _ = Str.search_forward re_texorpdf content 0 in
             true
           with Not_found -> false
         in
         if has_special && not has_texorpdf then incr cnt;
         i := pos + 1
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "PDF-010";
          severity = Info;
          message =
            "Outline/bookmark text contains '_' or '#' – use \\texorpdfstring";
          count = !cnt;
        }
    else None
  in
  { id = "PDF-010"; run; languages = [] }

(* ── TIKZ rules ────────────────────────────────────────────────── *)

(* TIKZ-005: TikZ externalisation not enabled for large figures *)
let r_tikz_005 : rule =
  let re_tikz = Str.regexp_string "\\begin{tikzpicture}" in
  let re_ext_lib = Str.regexp_string "\\usetikzlibrary{external}" in
  let re_ext_cmd = Str.regexp_string "\\tikzexternalize" in
  let run s =
    let has_tikz =
      try
        let _ = Str.search_forward re_tikz s 0 in
        true
      with Not_found -> false
    in
    if not has_tikz then None
    else
      let has_ext_lib =
        try
          let _ = Str.search_forward re_ext_lib s 0 in
          true
        with Not_found -> false
      in
      let has_ext_cmd =
        try
          let _ = Str.search_forward re_ext_cmd s 0 in
          true
        with Not_found -> false
      in
      if has_ext_lib || has_ext_cmd then None
      else
        Some
          {
            id = "TIKZ-005";
            severity = Info;
            message = "TikZ externalisation not enabled for large figures";
            count = 1;
          }
  in
  { id = "TIKZ-005"; run; languages = [] }

(* ══════════════════════════════════════════════════════════════════════ Phase
   3: L3-approximable rules (20 rules)
   ══════════════════════════════════════════════════════════════════════ *)

(* BIB-001: Entry missing DOI or ISBN/ISSN *)
let r_bib_001 : rule =
  let re_entry = Str.regexp {|@[a-zA-Z]+{[^,]+,|} in
  let _re_entry_sep = Str.regexp_string "\n@" in
  let run s =
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re_entry s !start);
         let entry_start = Str.match_end () in
         (* find end of entry: next @ at line start or end of string *)
         let entry_end =
           try Str.search_forward _re_entry_sep s entry_start
           with Not_found -> String.length s
         in
         let entry = String.sub s entry_start (entry_end - entry_start) in
         let has_doi = contains_substring entry "doi" in
         let has_isbn =
           contains_substring entry "isbn" || contains_substring entry "issn"
         in
         if (not has_doi) && not has_isbn then incr cnt;
         start := entry_end
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-001";
          severity = Warning;
          message = "Bibliography entry missing DOI or ISBN/ISSN";
          count = !cnt;
        }
    else None
  in
  mk_rule "BIB-001" run

(* BIB-007: Duplicate DOI across entries *)
let r_bib_007 : rule =
  let re_doi = Str.regexp {|doi *= *{?\([^},]+\)}?|} in
  let run s =
    let dois = ref [] in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re_doi s !start);
         let doi = String.trim (Str.matched_group 1 s) in
         dois := doi :: !dois;
         start := Str.match_end ()
       done
     with Not_found -> ());
    let sorted = List.sort String.compare !dois in
    let rec count_dups cnt = function
      | [] | [ _ ] -> cnt
      | a :: (b :: _ as rest) ->
          count_dups (if a = b then cnt + 1 else cnt) rest
    in
    let cnt = count_dups 0 sorted in
    if cnt > 0 then
      Some
        {
          id = "BIB-007";
          severity = Warning;
          message = "Duplicate DOI appears in more than one entry";
          count = cnt;
        }
    else None
  in
  mk_rule "BIB-007" run

(* BIB-013: Title capitalisation incorrect for bibliography style *)
let r_bib_013 : rule =
  let re_title = Str.regexp {|title *= *{\([^}]+\)}|} in
  let run s =
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re_title s !start);
         let title = Str.matched_group 1 s in
         (* Check for sentence-case violation: multiple capitalised words not
            protected by braces *)
         let words = String.split_on_char ' ' title in
         let cap_words =
           List.filter
             (fun w ->
               String.length w > 3
               && w.[0] >= 'A'
               && w.[0] <= 'Z'
               && not (w.[0] = '{'))
             words
         in
         if List.length cap_words > 3 then incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-013";
          severity = Info;
          message =
            "Title capitalisation incorrect for selected bibliography style";
          count = !cnt;
        }
    else None
  in
  mk_rule "BIB-013" run

(* BIB-014: Duplicate author-year key *)
let r_bib_014 : rule =
  let re_author = Str.regexp {|author *= *{\([^}]+\)}|} in
  let re_year = Str.regexp {|year *= *{\([^}]+\)}|} in
  let _re_entry_split = Str.regexp "\n@" in
  let run s =
    let entries = Str.split _re_entry_split s in
    let keys = ref [] in
    List.iter
      (fun entry ->
        let author =
          try
            ignore (Str.search_forward re_author entry 0);
            Str.matched_group 1 entry
          with Not_found -> ""
        in
        let year =
          try
            ignore (Str.search_forward re_year entry 0);
            Str.matched_group 1 entry
          with Not_found -> ""
        in
        if author <> "" && year <> "" then
          keys := (author ^ ":" ^ year) :: !keys)
      entries;
    let sorted = List.sort String.compare !keys in
    let rec count_dups cnt = function
      | [] | [ _ ] -> cnt
      | a :: (b :: _ as rest) ->
          count_dups (if a = b then cnt + 1 else cnt) rest
    in
    let cnt = count_dups 0 sorted in
    if cnt > 0 then
      Some
        {
          id = "BIB-014";
          severity = Warning;
          message = "Duplicate author-year key without disambiguation suffix";
          count = cnt;
        }
    else None
  in
  mk_rule "BIB-014" run

(* BIB-017: Sentence-case title ends with punctuation mark *)
let r_bib_017 : rule =
  let re_title = Str.regexp {|title *= *{\([^}]+\)}|} in
  let run s =
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re_title s !start);
         let title = String.trim (Str.matched_group 1 s) in
         (if String.length title > 0 then
            let last = title.[String.length title - 1] in
            if last = '.' || last = '!' || last = '?' then incr cnt);
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "BIB-017";
          severity = Info;
          message = "Bibliography title ends with punctuation mark";
          count = !cnt;
        }
    else None
  in
  mk_rule "BIB-017" run

(* FONT-003: Microtype protrusion disabled globally *)
let r_font_003 : rule =
  let run s =
    let has_microtype =
      contains_substring s "\\usepackage" && contains_substring s "microtype"
    in
    if not has_microtype then None
    else if contains_substring s "protrusion=false" then
      Some
        {
          id = "FONT-003";
          severity = Warning;
          message = "Microtype protrusion disabled globally";
          count = 1;
        }
    else None
  in
  mk_rule "FONT-003" run

(* FONT-002: Mixed optical sizes in paragraph *)
let r_font_002 : rule =
  let re = Str.regexp {|\\fontsize{\([0-9]+\)}|} in
  let run s =
    let sizes = ref [] in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !start);
         let sz = Str.matched_group 1 s in
         sizes := sz :: !sizes;
         start := Str.match_end ()
       done
     with Not_found -> ());
    let unique = List.sort_uniq String.compare !sizes in
    if List.length unique > 2 then
      Some
        {
          id = "FONT-002";
          severity = Info;
          message = "Mixed optical sizes in paragraph";
          count = List.length unique;
        }
    else None
  in
  mk_rule "FONT-002" run

(* RTL-001: Mixture of RTL and LTR digits within number *)
let r_rtl_001 : rule =
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len - 3 do
      let b0 = Char.code (String.unsafe_get s !i) in
      (* Arabic-Indic digits: U+0660-0669 = D9 A0..A9 *)
      if b0 = 0xd9 then (
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        if b1 >= 0xa0 && b1 <= 0xa9 then (
          (* check if adjacent ASCII digit exists nearby *)
          let has_ascii_nearby = ref false in
          for j = max 0 (!i - 4) to min (len - 1) (!i + 5) do
            let c = String.unsafe_get s j in
            if c >= '0' && c <= '9' then has_ascii_nearby := true
          done;
          if !has_ascii_nearby then incr cnt);
        i := !i + 2)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "RTL-001";
          severity = Warning;
          message = "Mixture of RTL and LTR digits within number";
          count = !cnt;
        }
    else None
  in
  mk_rule "RTL-001" run

(* RTL-002: Missing \textLR around Latin acronym in Arabic text *)
let r_rtl_002 : rule =
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len - 5 do
      let b0 = Char.code (String.unsafe_get s !i) in
      (* Arabic chars: U+0600-06FF = D8 80..DB BF *)
      if b0 >= 0xd8 && b0 <= 0xdb then (
        (* skip the Arabic char *)
        i := !i + 2;
        (* check if followed by space + ASCII uppercase *)
        if !i < len && String.unsafe_get s !i = ' ' then
          let j = !i + 1 in
          if j < len then
            let c = String.unsafe_get s j in
            if c >= 'A' && c <= 'Z' then
              (* check not inside \textLR *)
              if not (j >= 8 && String.sub s (j - 8) 8 = "\\textLR{") then
                incr cnt)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "RTL-002";
          severity = Info;
          message = "Missing \\textLR around Latin acronym in Arabic text";
          count = !cnt;
        }
    else None
  in
  mk_rule "RTL-002" run

(* META-003: Build timestamp not reproducible *)
let r_meta_003 : rule =
  let run s =
    if contains_substring s "\\date{\\today}" then
      Some
        {
          id = "META-003";
          severity = Warning;
          message = "Build timestamp not reproducible (\\date{\\today})";
          count = 1;
        }
    else None
  in
  mk_rule "META-003" run

(* META-004: PDF CreationDate not stripped *)
let r_meta_004 : rule =
  let run s =
    if
      contains_substring s "\\pdfinfo"
      && not (contains_substring s "CreationDate")
    then None
    else if
      contains_substring s "\\pdfinfo" && contains_substring s "CreationDate"
    then
      Some
        {
          id = "META-004";
          severity = Info;
          message = "PDF /CreationDate not stripped — build not reproducible";
          count = 1;
        }
    else None
  in
  mk_rule "META-004" run

(* DOC-005: \\keywords present but absent from PDF/XMP metadata *)
let r_doc_005 : rule =
  let run s =
    let has_keywords = contains_substring s "\\keywords{" in
    let has_hypersetup = contains_substring s "\\hypersetup{" in
    let has_pdfkeywords = contains_substring s "pdfkeywords" in
    if has_keywords && has_hypersetup && not has_pdfkeywords then
      Some
        {
          id = "DOC-005";
          severity = Info;
          message = "\\keywords present but absent from PDF/XMP metadata";
          count = 1;
        }
    else None
  in
  mk_rule "DOC-005" run

(* REF-012: Reference text 'above/below' may contradict float position *)
let r_ref_012 : rule =
  let re =
    Str.regexp
      {|\(above\|below\)[ ,]*\\ref{\|\\ref{[^}]*}[ ,]*\(above\|below\)|}
  in
  let run s =
    let text = strip_math_segments s in
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re text !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "REF-012";
          severity = Info;
          message = "Reference text 'above/below' may contradict float position";
          count = !cnt;
        }
    else None
  in
  mk_rule "REF-012" run

(* FONT-010: Digits in \\textsc not converted to small-caps figures *)
let r_font_010 : rule =
  let re = Str.regexp {|\\textsc{[^}]*[0-9][^}]*}|} in
  let run s =
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "FONT-010";
          severity = Info;
          message = "Digits in \\textsc not converted to small-caps figures";
          count = !cnt;
        }
    else None
  in
  mk_rule "FONT-010" run

(* FONT-013: Mixed proportional and tabular figures in same table column *)
let r_font_013 : rule =
  let run s =
    let has_tabular = contains_substring s "\\begin{tabular" in
    let has_proportional = contains_substring s "\\proportional" in
    let has_tabularfigs = contains_substring s "\\tabularfigures" in
    if has_tabular && has_proportional && has_tabularfigs then
      Some
        {
          id = "FONT-013";
          severity = Warning;
          message = "Mixed proportional and tabular figures in same table";
          count = 1;
        }
    else None
  in
  mk_rule "FONT-013" run

(* PDF-005: PDF/A or PDF/UA compliance flag missing *)
let r_pdf_005 : rule =
  let run s =
    let has_hyperref =
      contains_substring s "\\usepackage" && contains_substring s "hyperref"
    in
    if not has_hyperref then None
    else
      let has_pdfa =
        contains_substring s "pdfa"
        || contains_substring s "pdfuatag"
        || contains_substring s "\\DocumentMetadata"
      in
      if not has_pdfa then
        Some
          {
            id = "PDF-005";
            severity = Warning;
            message = "PDF/A or PDF/UA compliance flag missing";
            count = 1;
          }
      else None
  in
  mk_rule "PDF-005" run

(* ══════════════════════════════════════════════════════════════════════ Phase
   4: FONT + CHEM + LANG misc rules NOTE: LAY-010..014 removed — spec
   descriptions require compile-log analysis that cannot be text-approximated.
   Our implementations checked different things than the spec describes (e.g.
   spec LAY-010 = "page number suppressed on chapter opener" but we checked
   "clearpage before appendix"). Removed to avoid misleading spec-match counts.
   ══════════════════════════════════════════════════════════════════════ *)

(* FONT-009: Small-caps requested but glyphs missing — fallback visible *)
let r_font_009 : rule =
  let re = Str.regexp {|\\textsc{[^}]*}|} in
  let has_nonascii body =
    let found = ref false in
    String.iter (fun c -> if Char.code c > 127 then found := true) body;
    !found
  in
  let run s =
    (* Heuristic: \textsc used with non-Latin chars *)
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !start);
         let m = Str.matched_string s in
         (* Extract body between { and } *)
         let body = String.sub m 8 (String.length m - 9) in
         if has_nonascii body then incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "FONT-009";
          severity = Warning;
          message = "Small-caps with non-ASCII chars — fallback may be visible";
          count = !cnt;
        }
    else None
  in
  mk_rule "FONT-009" run

(* FONT-011: Microtype protrusion mismatch between text and math fonts *)
let r_font_011 : rule =
  let run s =
    let has_microtype = contains_substring s "microtype" in
    let has_mathfont =
      contains_substring s "\\setmathfont"
      || contains_substring s "unicode-math"
    in
    if has_microtype && has_mathfont then
      Some
        {
          id = "FONT-011";
          severity = Warning;
          message =
            "Microtype protrusion may mismatch between text and math fonts";
          count = 1;
        }
    else None
  in
  mk_rule "FONT-011" run

(* FONT-012: ff-ligature disabled adjacent to \texttt *)
let r_font_012 : rule =
  let re =
    Str.regexp
      {|\\texttt{[^}]*}\(ff\|fi\|fl\)\|ff\\texttt\|fi\\texttt\|fl\\texttt|}
  in
  let run s =
    let cnt = ref 0 in
    let start = ref 0 in
    (try
       while true do
         ignore (Str.search_forward re s !start);
         incr cnt;
         start := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "FONT-012";
          severity = Info;
          message = "Ligature adjacent to \\texttt may cause visual clash";
          count = !cnt;
        }
    else None
  in
  mk_rule "FONT-012" run

(* CHEM-010: Reaction scheme exceeds page width heuristic *)
let r_chem_010 : rule =
  let run s =
    let ce_blocks = extract_env_blocks "reaction" s in
    let scheme_blocks = extract_env_blocks "scheme" s in
    let cnt =
      List.fold_left
        (fun acc body ->
          let lines = String.split_on_char '\n' body in
          List.fold_left
            (fun a line -> if String.length line > 120 then a + 1 else a)
            acc lines)
        0
        (ce_blocks @ scheme_blocks)
    in
    if cnt > 0 then
      Some
        {
          id = "CHEM-010";
          severity = Info;
          message = "Reaction scheme line exceeds page width (> 120 chars)";
          count = cnt;
        }
    else None
  in
  mk_rule "CHEM-010" run

(* LANG-009: Ragged-right text in non-Latin script *)
let r_lang_009 : rule =
  let run s =
    let has_ragged = contains_substring s "\\raggedright" in
    (* Check for CJK or Arabic content *)
    let has_nonlatin =
      contains_substring s "\\begin{CJK}"
      || contains_substring s "xeCJK"
      || contains_substring s "\\setdefaultlanguage{arabic}"
    in
    if has_ragged && has_nonlatin then
      Some
        {
          id = "LANG-009";
          severity = Info;
          message = "Ragged-right text in non-Latin script";
          count = 1;
        }
    else None
  in
  mk_rule "LANG-009" run

(* LANG-010: Arabic digits in RTL context not localised *)
let r_lang_010 : rule =
  let run s =
    let has_arabic =
      contains_substring s "\\setdefaultlanguage{arabic}"
      || contains_substring s "{arabic}"
    in
    if not has_arabic then None
    else
      (* Check for ASCII digits in Arabic text *)
      let text = strip_math_segments s in
      let has_ascii_digits =
        let found = ref false in
        String.iter (fun c -> if c >= '0' && c <= '9' then found := true) text;
        !found
      in
      if has_ascii_digits then
        Some
          {
            id = "LANG-010";
            severity = Info;
            message = "Arabic digits in RTL context not localised";
            count = 1;
          }
      else None
  in
  mk_rule "LANG-010" run

(* ══════════════════════════════════════════════════════════════════════ Phase
   5: CJK + LANG final batch NOTE: LAY-016..021 removed — same issue as
   LAY-010..014 above.
   ══════════════════════════════════════════════════════════════════════ *)

(* CJK-009: Western space between CJK glyphs *)
let r_cjk_009 : rule =
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len - 6 do
      let b0 = Char.code (String.unsafe_get s !i) in
      if b0 >= 0xe4 && b0 <= 0xe9 && !i + 5 < len then (
        let after_cjk = !i + 3 in
        (if after_cjk < len && String.unsafe_get s after_cjk = ' ' then
           let next = after_cjk + 1 in
           if next + 2 < len then
             let n0 = Char.code (String.unsafe_get s next) in
             if n0 >= 0xe4 && n0 <= 0xe9 then incr cnt);
        i := !i + 3)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "CJK-009";
          severity = Info;
          message = "Western inter-word space between CJK glyphs";
          count = !cnt;
        }
    else None
  in
  mk_rule "CJK-009" run

(* CJK-011: Hiragana prolonged-sound mark at line start *)
let r_cjk_011 : rule =
  let prolonged = "\xe3\x83\xbc" in
  let run s =
    let lines = String.split_on_char '\n' s in
    let cnt =
      List.fold_left
        (fun acc line ->
          let line = String.trim line in
          if String.length line >= 3 && String.sub line 0 3 = prolonged then
            acc + 1
          else acc)
        0 lines
    in
    if cnt > 0 then
      Some
        {
          id = "CJK-011";
          severity = Info;
          message = "Hiragana prolonged-sound mark at line start";
          count = cnt;
        }
    else None
  in
  mk_rule "CJK-011" run

(* CJK-013: Prohibited break before ideographic full stop U+3002 *)
let r_cjk_013 : rule =
  let fullstop = "\xe3\x80\x82" in
  let run s =
    let lines = String.split_on_char '\n' s in
    let cnt =
      List.fold_left
        (fun acc line ->
          let line = String.trim line in
          if String.length line >= 3 && String.sub line 0 3 = fullstop then
            acc + 1
          else acc)
        0 lines
    in
    if cnt > 0 then
      Some
        {
          id = "CJK-013";
          severity = Info;
          message =
            "Prohibited break before ideographic full stop at line start";
          count = cnt;
        }
    else None
  in
  mk_rule "CJK-013" run

(* LANG-005: Hyphen-penalty too low *)
let r_lang_005 : rule =
  let re = Str.regexp {|\\hyphenpenalty *= *\([0-9]+\)|} in
  let run s =
    try
      ignore (Str.search_forward re s 0);
      let v = int_of_string (Str.matched_group 1 s) in
      if v < 50 then
        Some
          {
            id = "LANG-005";
            severity = Info;
            message = Printf.sprintf "Hyphen-penalty too low (%d < 50)" v;
            count = 1;
          }
      else None
    with Not_found | Failure _ -> None
  in
  mk_rule "LANG-005" run

(* LANG-008: Spell-checker dictionary differs from babel option *)
let r_lang_008 : rule =
  let re_babel = Str.regexp {|\\usepackage\[\([a-z]+\)\]{babel}|} in
  let re_spell = Str.regexp {|\\setspelling{\([a-z]+\)}|} in
  let run s =
    let babel =
      try
        ignore (Str.search_forward re_babel s 0);
        Some (Str.matched_group 1 s)
      with Not_found -> None
    in
    let spell =
      try
        ignore (Str.search_forward re_spell s 0);
        Some (Str.matched_group 1 s)
      with Not_found -> None
    in
    match (babel, spell) with
    | Some b, Some sp when b <> sp ->
        Some
          {
            id = "LANG-008";
            severity = Info;
            message =
              Printf.sprintf
                "Spell-checker dictionary '%s' differs from babel '%s'" sp b;
            count = 1;
          }
    | _ -> None
  in
  mk_rule "LANG-008" run

let rules_l2_approx : rule list =
  [
    r_fig_001;
    r_fig_002;
    r_fig_003;
    r_fig_007;
    r_fig_009;
    r_fig_010;
    r_fig_013;
    r_tab_001;
    r_tab_002;
    r_tab_005;
    r_tab_006;
    r_tab_009;
    r_tab_010;
    r_tab_011;
    r_tab_014;
    r_pkg_001;
    r_pkg_002;
    r_pkg_004;
    r_pkg_005;
    r_pkg_007;
    r_pkg_009;
    r_pkg_011;
    r_pkg_012;
    r_pkg_015;
    r_pkg_020;
    r_pkg_022;
    r_pkg_023;
    r_cjk_004;
    r_cjk_006;
    r_font_006;
    r_font_007;
    r_font_008;
    r_math_032;
    r_math_054;
    r_math_062;
    r_math_063;
    r_math_100;
    r_math_023;
    r_math_024;
    r_ref_010;
    r_cmd_014;
    r_doc_001;
    r_doc_002;
    r_doc_003;
    r_lang_002;
    r_lang_004;
    r_tikz_007;
    r_pkg_008;
    r_pkg_010;
    r_pkg_013;
    r_pkg_014;
    r_pkg_016;
    r_pkg_017;
    r_pkg_021;
    r_pkg_024;
    r_pkg_025;
    r_tab_003;
    r_tab_007;
    r_tab_008;
    r_tab_012;
    r_tab_013;
    r_tab_015;
    r_tab_016;
    r_fig_012;
    r_fig_014;
    r_fig_017;
    r_fig_019;
    r_fig_022;
    r_fig_024;
    r_fig_025;
    r_math_075;
    r_math_080;
    r_cmd_012;
    r_doc_004;
    (* batch 5: expl3 + tikz + lang *)
    r_l3_001;
    r_l3_002;
    r_l3_003;
    r_l3_004;
    r_l3_005;
    r_l3_006;
    r_l3_007;
    r_l3_009;
    r_l3_011;
    r_tikz_001;
    r_tikz_003;
    r_tikz_004;
    r_tikz_006;
    r_tikz_009;
    r_tikz_010;
    r_lang_001;
    r_lang_006;
    r_lang_007;
    r_lang_013;
    r_col_006;
    r_l3_008;
    r_l3_010;
    r_lay_024;
    r_meta_002;
    r_rtl_005;
    r_bib_002;
    r_bib_003;
    r_bib_004;
    r_bib_005;
    r_bib_006;
    r_bib_008;
    r_bib_009;
    r_bib_010;
    r_bib_011;
    r_bib_012;
    r_bib_015;
    r_bib_016;
    r_pkg_018;
    r_pkg_019;
    r_font_005;
    r_lay_015;
    r_lay_020;
    r_lay_022;
    r_ref_008;
    r_meta_001;
    r_pdf_010;
    r_tikz_005;
    (* Phase 3: L3-approximable *)
    r_bib_001;
    r_bib_007;
    r_bib_013;
    r_bib_014;
    r_bib_017;
    r_font_002;
    r_font_003;
    r_font_010;
    r_font_013;
    r_rtl_001;
    r_rtl_002;
    r_meta_003;
    r_meta_004;
    r_doc_005;
    r_ref_012;
    r_pdf_005;
    (* Phase 4: FONT + misc *)
    r_font_009;
    r_font_011;
    r_font_012;
    r_chem_010;
    r_lang_009;
    r_lang_010;
    (* Phase 5: CJK + LANG final batch *)
    r_cjk_009;
    r_cjk_011;
    r_cjk_013;
    r_lang_005;
    r_lang_008;
  ]

(* ── CMD rules: command definition checks ────────────────────────────── *)

(* CMD-002: Command redefined with \def instead of \renewcommand *)
let r_cmd_002 : rule =
  let re = Str.regexp {|\\def\\[a-zA-Z]+|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "CMD-002";
          severity = Warning;
          message = "Command redefined with \\def instead of \\renewcommand";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-002"; run; languages = [] }

(* CMD-004: CamelCase command names discouraged *)
let r_cmd_004 : rule =
  let re = Str.regexp {|\\newcommand\|\\renewcommand\|\\def|} in
  let camel_re = Str.regexp {|{?\\[a-z]+[A-Z][a-zA-Z]*}?|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let pos = Str.search_forward re s !i in
         let after = pos + String.length (Str.matched_string s) in
         (* skip whitespace *)
         let j = ref after in
         while !j < String.length s && (s.[!j] = ' ' || s.[!j] = '\t') do
           incr j
         done;
         (try
            let _ = Str.search_forward camel_re s !j in
            if Str.match_beginning () = !j then incr cnt
          with Not_found -> ());
         i := max (after + 1) (pos + 1)
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "CMD-004";
          severity = Info;
          message = "CamelCase command names discouraged";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-004"; run; languages = [] }

(* CMD-005: Single-letter macro created *)
(* Two patterns: (1) \newcommand{\X} / \renewcommand{\X} with braces around the
   single-letter name; (2) \def\X where X is a single letter followed by a
   non-letter (space, brace, digit, etc.). *)
let r_cmd_005 : rule =
  let re_cmd = Str.regexp "\\\\\\(newcommand\\|renewcommand\\){\\\\[a-zA-Z]}" in
  let re_def = Str.regexp "\\\\def\\\\\\([a-zA-Z]\\)[^a-zA-Z]" in
  let count_matches re s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    !cnt
  in
  let run s =
    let cnt = count_matches re_cmd s + count_matches re_def s in
    if cnt > 0 then
      Some
        {
          id = "CMD-005";
          severity = Warning;
          message = {|Single‑letter macro created (\x)|};
          count = cnt;
        }
    else None
  in
  { id = "CMD-005"; run; languages = [] }

(* CMD-006: Macro defined inside document body *)
let r_cmd_006 : rule =
  let re =
    Str.regexp "\\\\\\(newcommand\\|renewcommand\\|def\\)[ \t\n]*{?\\\\"
  in
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body ->
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let _ = Str.search_forward re body !i in
             incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "CMD-006";
              severity = Info;
              message = "Macro defined inside document body";
              count = !cnt;
            }
        else None
  in
  { id = "CMD-006"; run; languages = [] }

(* CMD-008: Macro uses \@ in name outside maketitle context *)
let r_cmd_008 : rule =
  let re =
    Str.regexp
      "\\\\\\(newcommand\\|renewcommand\\|def\\)[ \t\n\
       ]*{?\\\\[a-zA-Z]*@[a-zA-Z]*}?"
  in
  let _re_makeatletter = Str.regexp_string "\\makeatletter" in
  let run s =
    let has_makeatletter =
      try
        let _ = Str.search_forward _re_makeatletter s 0 in
        true
      with Not_found -> false
    in
    if has_makeatletter then None
    else
      let cnt = ref 0 in
      let i = ref 0 in
      (try
         while true do
           let _ = Str.search_forward re s !i in
           incr cnt;
           i := Str.match_end ()
         done
       with Not_found -> ());
      if !cnt > 0 then
        Some
          {
            id = "CMD-008";
            severity = Warning;
            message = "Macro uses \\@ in name outside maketitle context";
            count = !cnt;
          }
      else None
  in
  { id = "CMD-008"; run; languages = [] }

(* CMD-009: Macro name contains digits *)
let r_cmd_009 : rule =
  let re =
    Str.regexp
      "\\\\\\(newcommand\\|renewcommand\\|def\\)[ \t\n\
       ]*{?\\\\[a-zA-Z]*[0-9]+[a-zA-Z0-9]*}?"
  in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re s !i in
         incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "CMD-009";
          severity = Info;
          message = "Macro name contains digits";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-009"; run; languages = [] }

(* CMD-011: Macro defined with \def/\edef in preamble without \makeatletter
   guard *)
let r_cmd_011 : rule =
  let re = Str.regexp "\\\\\\(def\\|edef\\)[ \t\n]*\\\\[a-zA-Z@]+" in
  let _re_begin_doc_c11 = Str.regexp_string "\\begin{document}" in
  let _re_makeatletter_c11 = Str.regexp_string "\\makeatletter" in
  let run s =
    (* Extract preamble: everything before \begin{document} *)
    let preamble =
      try
        let pos = Str.search_forward _re_begin_doc_c11 s 0 in
        String.sub s 0 pos
      with Not_found -> s
    in
    let has_makeatletter =
      try
        let _ = Str.search_forward _re_makeatletter_c11 preamble 0 in
        true
      with Not_found -> false
    in
    if has_makeatletter then None
    else
      let cnt = ref 0 in
      let i = ref 0 in
      (try
         while true do
           let _ = Str.search_forward re preamble !i in
           incr cnt;
           i := Str.match_end ()
         done
       with Not_found -> ());
      if !cnt > 0 then
        Some
          {
            id = "CMD-011";
            severity = Warning;
            message =
              {|Macro defined with \def/\edef in preamble without \makeatletter guard|};
            count = !cnt;
          }
      else None
  in
  { id = "CMD-011"; run; languages = [] }

(* CMD-013: \def\arraystretch declared inside document body *)
let r_cmd_013 : rule =
  let pat = Str.regexp_string "\\def\\arraystretch" in
  let run s =
    match extract_document_body s with
    | None -> None
    | Some body ->
        let cnt = ref 0 in
        let i = ref 0 in
        (try
           while true do
             let _ = Str.search_forward pat body !i in
             incr cnt;
             i := Str.match_end ()
           done
         with Not_found -> ());
        if !cnt > 0 then
          Some
            {
              id = "CMD-013";
              severity = Info;
              message = "\\def\\arraystretch declared inside document body";
              count = !cnt;
            }
        else None
  in
  { id = "CMD-013"; run; languages = [] }

let rules_cmd : rule list =
  [
    r_cmd_002;
    r_cmd_004;
    r_cmd_005;
    r_cmd_006;
    r_cmd_008;
    r_cmd_009;
    r_cmd_011;
    r_cmd_013;
  ]

(* ── TYPO-062: Literal backslash in text ───────────────────────────── *)
let r_typo_062 : rule =
  let run s =
    (* Count \textbackslash suggestions -- look for \\ not followed by a letter
       (i.e. bare backslash, not a command) outside math *)
    let s = strip_math_segments s in
    let n = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n - 1 do
      if s.[!i] = '\\' && s.[!i + 1] = '\\' then (
        (* Check it's not a linebreak command like \\[2pt] or \\* *)
        if !i + 2 < n then (
          let c = s.[!i + 2] in
          if c <> '[' && c <> '*' then incr cnt)
        else incr cnt;
        i := !i + 2)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "TYPO-062";
          severity = Warning;
          message = "Literal backslash in text; use \\textbackslash";
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-062"; run; languages = [] }

(* ── MATH rules: mathematics-related lexical checks ──────────────── *)

(* MATH-083: Unicode minus U+2212 inside text mode — should be a hyphen-minus in
   text or $-$ / \textminus in math context. We detect U+2212 (E2 88 92) outside
   of math mode segments. *)
let r_math_083 : rule =
  let run s =
    let s_text = strip_math_segments s in
    (* U+2212 MINUS SIGN = E2 88 92 *)
    let cnt = count_substring s_text "\xe2\x88\x92" in
    if cnt > 0 then
      Some
        {
          id = "MATH-083";
          severity = Warning;
          message = "Unicode minus inside text mode";
          count = cnt;
        }
    else None
  in
  { id = "MATH-083"; run; languages = [] }
