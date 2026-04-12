(* ══════════════════════════════════════════════════════════════════════
   Validators_l1_expl3 — CHAR-004, MATH-006, L3-001..L3-011 rules
   ══════════════════════════════════════════════════════════════════════

   12 rules covering private-use Unicode, bra-ket notation, and the full
   LaTeX3/expl3 style family. All are text-scannable heuristics that do not
   require macro expansion or AST parsing.
   ══════════════════════════════════════════════════════════════════════ *)

open Validators_common

(* ── CHAR-004 (L0_Lexer, Info): Private-use (U+E000–F8FF) policy ──── *)
let r_char_004 : rule =
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < len do
      let b0 = Char.code (String.unsafe_get s !i) in
      (* U+E000–U+F8FF encodes as: U+E000 = 0xEE 0x80 0x80 U+F8FF = 0xEF 0xA3
         0xBF 3-byte UTF-8: 1110xxxx 10xxxxxx 10xxxxxx *)
      if b0 = 0xEE && !i + 2 < len then
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        if b1 land 0xC0 = 0x80 && b2 land 0xC0 = 0x80 then (
          (* U+E000 = 0xEE 0x80 0x80 .. U+EFFF = 0xEE 0xBF 0xBF *)
          incr cnt;
          i := !i + 3)
        else i := !i + 1
      else if b0 = 0xEF && !i + 2 < len then
        let b1 = Char.code (String.unsafe_get s (!i + 1)) in
        let b2 = Char.code (String.unsafe_get s (!i + 2)) in
        if b1 land 0xC0 = 0x80 && b2 land 0xC0 = 0x80 then
          if
            (* Decode: cp = (0xEF land 0x0F)<<12 | (b1 land 0x3F)<<6 | b2 land
               0x3F = 0xF000 | ((b1 land 0x3F)<<6) | (b2 land 0x3F) PUA upper
               bound is U+F8FF = 0xEF 0xA3 0xBF so b1 must be <= 0xA3, and if
               b1=0xA3 then b2 <= 0xBF (always true) *)
            b1 <= 0xA3
          then (
            incr cnt;
            i := !i + 3)
          else i := !i + 3 (* skip valid 3-byte seq but not PUA *)
        else i := !i + 1
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHAR-004";
          severity = Info;
          message =
            "Private-use Unicode (U+E000\xe2\x80\x93F8FF) codepoint found";
          count = !cnt;
        }
    else None
  in
  mk_rule "CHAR-004" run

(* ── MATH-006 (L1_Expanded, Info): Bra-ket spacing ────────────────── *)
let r_math_006 : rule =
  let re_braket =
    Re_compat.regexp {|\\langle\([^\\]*\(\\[^r][a-zA-Z]*\)*\)*\\rangle|}
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _mr, _ = Re_compat.search_forward re_braket seg !i in
            let matched = Re_compat.matched_string _mr seg in
            (* Check for separator: \mid or | between \langle and \rangle *)
            let has_mid = contains_substring matched "\\mid" in
            let has_pipe =
              (* look for | that isn't \| *)
              let mlen = String.length matched in
              let found = ref false in
              for j = 7 (* skip \langle *) to mlen - 8 (* before \rangle *) do
                if matched.[j] = '|' then
                  if j = 0 || matched.[j - 1] <> '\\' then found := true
              done;
              !found
            in
            if (not has_mid) && not has_pipe then incr cnt;
            i := Re_compat.match_end _mr
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-006";
          severity = Info;
          message =
            {|Bra-ket notation: \langle...\rangle without \mid or | separator|};
          count = !cnt;
        }
    else None
  in
  mk_rule "MATH-006" run

(* ── L3-001 (L1_Expanded, Info): expl3 + 2e macros in preamble ──── *)
let r_l3_001 : rule =
  let re_expl3 =
    Re_compat.regexp
      {|\\[a-z]+_[a-z_]+:[a-zA-Z]+\|\\tl_new:N\|\\int_new:N\|\\bool_new:N|}
  in
  let re_2e =
    Re_compat.regexp
      {|\\newcommand\|\\renewcommand\|\\newenvironment\|\\renewenvironment|}
  in
  let re_begin_doc = Re_compat.regexp_string {|\begin{document}|} in
  let run s =
    let preamble =
      try
        let _mr, idx = Re_compat.search_forward re_begin_doc s 0 in
        String.sub s 0 idx
      with Not_found -> s
    in
    let has_expl3 =
      try
        let _mr, _ = Re_compat.search_forward re_expl3 preamble 0 in
        ignore _mr;
        true
      with Not_found -> false
    in
    let has_2e =
      try
        let _mr, _ = Re_compat.search_forward re_2e preamble 0 in
        ignore _mr;
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
  mk_rule "L3-001" run

(* ── L3-002 (L1_Expanded, Warning): expl3 variable after \begin{document} *)
let r_l3_002 : rule =
  let re_expl3_decl =
    Re_compat.regexp {|\\[a-z]+_new:N\|\\[a-z]+_const:Nn\|\\[a-z]+_gset:Nn|}
  in
  let re_begin_doc = Re_compat.regexp_string {|\begin{document}|} in
  let run s =
    let body =
      try
        let _mr, idx = Re_compat.search_forward re_begin_doc s 0 in
        let start = idx + 16 in
        if start < String.length s then
          String.sub s start (String.length s - start)
        else ""
      with Not_found -> ""
    in
    if String.length body = 0 then None
    else
      let cnt = count_re_matches re_expl3_decl body in
      if cnt > 0 then
        Some
          {
            id = "L3-002";
            severity = Warning;
            message = {|Expl3 variable declared after \begin{document}|};
            count = cnt;
          }
      else None
  in
  mk_rule "L3-002" run

(* ── L3-003 (L1_Expanded, Warning): expl3 + etoolbox combined ────── *)
let r_l3_003 : rule =
  let re_expl3 =
    Re_compat.regexp {|\\ExplSyntaxOn\|\\[a-z]+_[a-z_]+:[a-zA-Z]|}
  in
  let re_etoolbox =
    Re_compat.regexp
      {|\\patchcmd\|\\apptocmd\|\\pretocmd\|\\robustify\|\\AtBeginEnvironment|}
  in
  let run s =
    let has_expl3 =
      try
        let _mr, _ = Re_compat.search_forward re_expl3 s 0 in
        ignore _mr;
        true
      with Not_found -> false
    in
    let has_etoolbox =
      try
        let _mr, _ = Re_compat.search_forward re_etoolbox s 0 in
        ignore _mr;
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
  mk_rule "L3-003" run

(* ── L3-004 (L1_Expanded, Info): Undocumented \__module_internal:N ── *)
let r_l3_004 : rule =
  let re = Re_compat.regexp {|\\__[a-z_]+:[a-zA-Z]*|} in
  let run s =
    let cnt = count_re_matches re s in
    if cnt > 0 then
      Some
        {
          id = "L3-004";
          severity = Info;
          message = {|Undocumented \__module_internal:N used|};
          count = cnt;
        }
    else None
  in
  mk_rule "L3-004" run

(* ── L3-005 (L1_Expanded, Error): Missing \ExplSyntaxOn guard ────── *)
let r_l3_005 : rule =
  let re_expl3_func = Re_compat.regexp {|\\[a-z]+_[a-z_]+:[nNoVvxfeTFpw]+|} in
  let re_syntax_on = Re_compat.regexp_string {|\ExplSyntaxOn|} in
  let run s =
    let has_expl3 =
      try
        let _mr, _ = Re_compat.search_forward re_expl3_func s 0 in
        ignore _mr;
        true
      with Not_found -> false
    in
    if not has_expl3 then None
    else
      let has_guard =
        try
          let _mr, _ = Re_compat.search_forward re_syntax_on s 0 in
          ignore _mr;
          true
        with Not_found -> false
      in
      if not has_guard then
        Some
          {
            id = "L3-005";
            severity = Error;
            message = {|Missing \ExplSyntaxOn guard around expl3 code|};
            count = 1;
          }
      else None
  in
  mk_rule "L3-005" run

(* ── L3-007 (L1_Expanded, Info): camelCase + snake_case in expl3 ─── *)
let r_l3_007 : rule =
  let re_camel =
    Re_compat.regexp {|\\[a-z]+[A-Z][a-zA-Z]*_[a-z_]+:[a-zA-Z]*|}
  in
  let re_syntax_on = Re_compat.regexp_string {|\ExplSyntaxOn|} in
  let run s =
    let has_expl3 =
      try
        let _mr, _ = Re_compat.search_forward re_syntax_on s 0 in
        ignore _mr;
        true
      with Not_found -> false
    in
    if not has_expl3 then None
    else
      let cnt = count_re_matches re_camel s in
      if cnt > 0 then
        Some
          {
            id = "L3-007";
            severity = Info;
            message = "Mix of camelCase and snake_case in expl3 names";
            count = cnt;
          }
      else None
  in
  mk_rule "L3-007" run

(* ── L3-008 (L2_Ast, Warning): Expl3 module lacks \ProvidesExplPackage *)
let r_l3_008 : rule =
  let expl3_re =
    Re_compat.regexp {|\\\(tl\|cs\|int\|bool\|fp\|clist\|seq\|prop\)_|}
  in
  let re_provides_expl = Re_compat.regexp_string "\\ProvidesExplPackage" in
  let run s =
    let has_expl3 =
      try
        let _mr, _ = Re_compat.search_forward expl3_re s 0 in
        ignore _mr;
        true
      with Not_found ->
        (* Also check for \ExplSyntaxOn *)
        contains_substring s "\\ExplSyntaxOn"
    in
    let has_provides =
      try
        let _mr, _ = Re_compat.search_forward re_provides_expl s 0 in
        ignore _mr;
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
  mk_rule "L3-008" run

(* ── L3-009 (L1_Expanded, Info): deprecated _n: variant ─────────── *)
let r_l3_009 : rule =
  let deprecated =
    [
      {|\tl_to_str:n|};
      {|\tl_count:n|};
      {|\str_if_eq:nn|};
      {|\int_eval:n|};
      {|\fp_eval:n|};
      {|\prop_get:Nn|};
      {|\seq_count:N|};
    ]
  in
  let run s =
    let cnt =
      List.fold_left (fun acc pat -> acc + count_substring s pat) 0 deprecated
    in
    if cnt > 0 then
      Some
        {
          id = "L3-009";
          severity = Info;
          message = "LaTeX3 function deprecated _n: variant used";
          count = cnt;
        }
    else None
  in
  mk_rule "L3-009" run

(* ── L3-010 (L2_Ast, Info): ExplSyntaxOff missing at end of file ─── *)
let r_l3_010 : rule =
  let on_re = Re_compat.regexp_string "\\ExplSyntaxOn" in
  let off_re = Re_compat.regexp_string "\\ExplSyntaxOff" in
  let run s =
    let count_m re str =
      let cnt = ref 0 in
      let i = ref 0 in
      (try
         while true do
           let _mr, _ = Re_compat.search_forward re str !i in
           incr cnt;
           i := Re_compat.match_end _mr
         done
       with Not_found -> ());
      !cnt
    in
    let on_count = count_m on_re s in
    let off_count = count_m off_re s in
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
  mk_rule "L3-010" run

(* ── L3-011 (L1_Expanded, Warning): pdfTeX prim in Lua/XeTeX path ── *)
let r_l3_011 : rule =
  let re_luatex_branch =
    Re_compat.regexp {|\\sys_if_engine_luatex:T\|\\ifluatex\|\\ifLuaTeX|}
  in
  let re_xetex_branch =
    Re_compat.regexp {|\\sys_if_engine_xetex:T\|\\ifxetex\|\\ifXeTeX|}
  in
  let re_fontspec = Re_compat.regexp_string {|\usepackage{fontspec}|} in
  let pdftex_prims =
    [
      {|\pdfoutput|};
      {|\pdfliteral|};
      {|\pdfcatalog|};
      {|\pdfcompresslevel|};
      {|\pdfobjcompresslevel|};
      {|\pdfminorversion|};
      {|\pdfsavepos|};
      {|\pdflastxpos|};
    ]
  in
  let run s =
    let has_lua =
      try
        let _mr, _ = Re_compat.search_forward re_luatex_branch s 0 in
        ignore _mr;
        true
      with Not_found -> false
    in
    let has_xe =
      try
        let _mr, _ = Re_compat.search_forward re_xetex_branch s 0 in
        ignore _mr;
        true
      with Not_found -> false
    in
    let has_fontspec =
      try
        let _mr, _ = Re_compat.search_forward re_fontspec s 0 in
        ignore _mr;
        true
      with Not_found -> false
    in
    if not (has_lua || has_xe || has_fontspec) then None
    else
      let cnt =
        List.fold_left (fun acc p -> acc + count_substring s p) 0 pdftex_prims
      in
      if cnt > 0 then
        Some
          {
            id = "L3-011";
            severity = Warning;
            message =
              "Engine\xe2\x80\x91branch uses pdfTeX primitive in Lua/XeTeX path";
            count = cnt;
          }
      else None
  in
  mk_rule "L3-011" run

(* ── Exported rule list ──────────────────────────────────────────── *)
let rules_l1_expl3 : rule list =
  [
    r_char_004;
    r_math_006;
    r_l3_001;
    r_l3_002;
    r_l3_003;
    r_l3_004;
    r_l3_005;
    r_l3_007;
    r_l3_008;
    r_l3_009;
    r_l3_010;
    r_l3_011;
  ]
