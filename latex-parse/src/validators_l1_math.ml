open Validators_common

(* ═══════════════════════════════════════════════════════════════════════════
   MATH family (L1) — Core math-token validators MATH-009 through MATH-022
   ═══════════════════════════════════════════════════════════════════════════ *)

(* MATH-009: Bare 'sin/log/exp' in math — use \sin, \log, \exp etc. *)
let l1_math_009_rule : rule =
  let operators =
    [
      "sin";
      "cos";
      "tan";
      "cot";
      "sec";
      "csc";
      "log";
      "exp";
      "ln";
      "lim";
      "inf";
      "sup";
      "min";
      "max";
      "det";
      "dim";
      "ker";
      "hom";
      "arg";
      "deg";
      "gcd";
      "Pr";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun op ->
            let oplen = String.length op in
            let n = String.length seg in
            let i = ref 0 in
            while !i + oplen <= n do
              if String.sub seg !i oplen = op then (
                (* Check it's NOT preceded by \ (i.e. not \sin already) *)
                let preceded_by_backslash = !i > 0 && seg.[!i - 1] = '\\' in
                (* Check word boundary before: not alphanumeric *)
                let boundary_before =
                  !i = 0
                  ||
                  let c = seg.[!i - 1] in
                  not
                    ((c >= 'a' && c <= 'z')
                    || (c >= 'A' && c <= 'Z')
                    || (c >= '0' && c <= '9'))
                in
                (* Check word boundary after: not alphanumeric *)
                let boundary_after =
                  !i + oplen >= n
                  ||
                  let c = seg.[!i + oplen] in
                  not
                    ((c >= 'a' && c <= 'z')
                    || (c >= 'A' && c <= 'Z')
                    || (c >= '0' && c <= '9'))
                in
                if
                  (not preceded_by_backslash)
                  && boundary_before
                  && boundary_after
                then incr cnt;
                i := !i + oplen)
              else incr i
            done)
          operators)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-009";
          severity = Warning;
          message = {|Bare ‘sin/log/exp’ in math; use \sin, \log, \exp|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-009"; run; languages = [] }

(* MATH-010: Division symbol ÷ (U+00F7) used — prefer \frac or solidus *)
let l1_math_010_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    (* U+00F7 = \xc3\xb7 in UTF-8 *)
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\xc3\xb7")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-010";
          severity = Warning;
          message = {|Division symbol ÷ used; prefer \frac or solidus|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-010"; run; languages = [] }

(* MATH-011: Vector notation inconsistent within equation — detects when both
   \vec{} and \mathbf{} are used for vectors in the same document *)
let l1_math_011_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let vec_count = ref 0 in
    let mathbf_count = ref 0 in
    List.iter
      (fun seg ->
        vec_count := !vec_count + count_substring seg "\\vec{";
        mathbf_count := !mathbf_count + count_substring seg "\\mathbf{")
      math_segs;
    if !vec_count > 0 && !mathbf_count > 0 then
      Some
        {
          id = "MATH-011";
          severity = Info;
          message = "Vector notation inconsistent within equation";
          count = min !vec_count !mathbf_count;
        }
    else None
  in
  { id = "MATH-011"; run; languages = [] }

(* MATH-012: Multi-letter function not in roman (\operatorname{}) — detects
   sequences of 2+ lowercase letters in math that look like function names but
   aren't standard operators *)
let l1_math_012_rule : rule =
  let re = Re_compat.regexp {|\([a-z][a-z]+\)|} in
  let known_operators =
    [
      "sin";
      "cos";
      "tan";
      "cot";
      "sec";
      "csc";
      "log";
      "exp";
      "ln";
      "lim";
      "inf";
      "sup";
      "min";
      "max";
      "det";
      "dim";
      "ker";
      "hom";
      "arg";
      "deg";
      "gcd";
      "mod";
      "arcsin";
      "arccos";
      "arctan";
      "sinh";
      "cosh";
      "tanh";
      "coth";
      "sech";
      "csch";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _mr, pos = Re_compat.search_forward re seg !i in
            let matched = Re_compat.matched_group _mr 1 seg in
            let next_i = Re_compat.match_end _mr in
            (* Skip if preceded by backslash or inside \text{}/\mathrm{} *)
            let preceded_by_backslash = pos > 0 && seg.[pos - 1] = '\\' in
            let is_known = List.mem matched known_operators in
            (* Skip 2-char that could just be variables like dx, dy *)
            let is_short_var = String.length matched <= 2 in
            (if
               (not preceded_by_backslash) && (not is_known) && not is_short_var
             then
               (* Check prefix for \text{, \mathrm{, \operatorname{ *)
               let prefix_start = max 0 (pos - 16) in
               let prefix = String.sub seg prefix_start (pos - prefix_start) in
               let has_wrapper =
                 count_substring prefix "\\text{"
                 + count_substring prefix "\\mathrm{"
                 + count_substring prefix "\\operatorname{"
                 > 0
               in
               if not has_wrapper then incr cnt);
            i := next_i
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-012";
          severity = Warning;
          message = {|Multi‑letter function not in roman (\operatorname{})|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-012"; run; languages = [] }

(* MATH-013: Differential d not typeset roman — detects bare 'd' before a
   variable in integrands, e.g. \int f(x) dx where d should be \mathrm{d} *)
let l1_math_013_rule : rule =
  let re = Re_compat.regexp {| d\([A-Za-z]\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Only trigger if segment contains integral-like context *)
        if
          count_substring seg "\\int" > 0
          || count_substring seg "\\iint" > 0
          || count_substring seg "\\iiint" > 0
          || count_substring seg "\\oint" > 0
        then
          let i = ref 0 in
          try
            while true do
              let _mr, pos = Re_compat.search_forward re seg !i in
              let next_i = Re_compat.match_end _mr in
              (* Make sure it's not already \mathrm{d} *)
              let prefix_start = max 0 (pos - 9) in
              let prefix =
                String.sub seg prefix_start (pos - prefix_start + 1)
              in
              if
                count_substring prefix "\\mathrm{" = 0
                && count_substring prefix "\\,d" = 0
              then incr cnt;
              i := next_i
            done
          with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-013";
          severity = Info;
          message = "Differential d not typeset roman";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-013"; run; languages = [] }

(* MATH-014: Inline \frac in running text — \frac inside $...$ or \(...\) can be
   hard to read *)
let l1_math_014_rule : rule =
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Count \frac occurrences, exclude \tfrac and \dfrac *)
        let total_frac = count_substring seg "\\frac{" in
        let tfrac = count_substring seg "\\tfrac{" in
        let dfrac = count_substring seg "\\dfrac{" in
        let bare_frac = total_frac - tfrac - dfrac in
        if bare_frac > 0 then cnt := !cnt + bare_frac)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-014";
          severity = Info;
          message = {|Inline \frac in running text|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-014"; run; languages = [] }

(* MATH-015: \stackrel used — prefer \overset *)
let l1_math_015_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\stackrel{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-015";
          severity = Warning;
          message = {|\stackrel used; prefer \overset|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-015"; run; languages = [] }

(* MATH-016: Nested subscripts without braces — e.g. x_i_j instead of x_{i_j} or
   x_{i,j} *)
let l1_math_016_rule : rule =
  let re = Re_compat.regexp {|_\([A-Za-z0-9]\)_|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-016";
          severity = Warning;
          message = "Nested subscripts without braces";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-016"; run; languages = [] }

(* MATH-017: Mismatched \left\{ ... \right] pair — left and right delimiters
   don't match type *)
let l1_math_017_rule : rule =
  let left_delims =
    [
      ("\\left\\{", "brace");
      ("\\left\\[", "bracket");
      ("\\left[", "bracket");
      ("\\left(", "paren");
      ("\\left\\langle", "angle");
      ("\\left\\|", "double_bar");
      ("\\left\\lfloor", "floor");
      ("\\left\\lceil", "ceil");
      ("\\left.", "invisible");
    ]
  in
  let right_delims =
    [
      ("\\right\\}", "brace");
      ("\\right\\]", "bracket");
      ("\\right]", "bracket");
      ("\\right)", "paren");
      ("\\right\\rangle", "angle");
      ("\\right\\|", "double_bar");
      ("\\right\\rfloor", "floor");
      ("\\right\\rceil", "ceil");
      ("\\right.", "invisible");
    ]
  in
  let starts_with s idx prefix =
    let plen = String.length prefix in
    idx + plen <= String.length s && String.sub s idx plen = prefix
  in
  let find_delim_type delims s idx =
    List.fold_left
      (fun acc (prefix, dtype) ->
        match acc with
        | Some _ -> acc
        | None ->
            if starts_with s idx prefix then Some (dtype, String.length prefix)
            else None)
      None delims
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        (* Collect left delimiters in order *)
        let lefts = ref [] in
        let i = ref 0 in
        while !i < n do
          match find_delim_type left_delims seg !i with
          | Some (dtype, plen) ->
              lefts := dtype :: !lefts;
              i := !i + plen
          | None -> incr i
        done;
        let lefts = List.rev !lefts in
        (* Collect right delimiters in order *)
        let rights = ref [] in
        i := 0;
        while !i < n do
          match find_delim_type right_delims seg !i with
          | Some (dtype, plen) ->
              rights := dtype :: !rights;
              i := !i + plen
          | None -> incr i
        done;
        let rights = List.rev !rights in
        (* Compare paired delimiters *)
        let rec check ls rs =
          match (ls, rs) with
          | l :: ls', r :: rs' ->
              if l <> "invisible" && r <> "invisible" && l <> r then incr cnt;
              check ls' rs'
          | _ -> ()
        in
        check lefts rights)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-017";
          severity = Error;
          message = {|Mismatched \left\{ … \right] pair|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-017"; run; languages = [] }

(* MATH-018: π written numerically as 3.14... in math *)
let l1_math_018_rule : rule =
  let re = Re_compat.regexp {|3\.14[0-9]*|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-018";
          severity = Info;
          message = "π written numerically as 3.14";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-018"; run; languages = [] }

(* MATH-019: Inline stacked ^_ order wrong — same concept as SCRIPT-021 but
   specifically for the pattern where _ immediately follows ^ without braces in
   inline math, e.g. $\sum^n_i$ instead of $\sum_{i}^{n}$ *)
let l1_math_019_rule : rule =
  let re =
    Re_compat.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-019";
          severity = Warning;
          message = "Inline stacked ^_ order wrong";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-019"; run; languages = [] }

(* MATH-020: Missing \cdot between coefficient and vector — detects digit
   immediately followed by \vec or \mathbf without \cdot *)
let l1_math_020_rule : rule =
  let re = Re_compat.regexp {|[0-9]\(\\vec{\|\\mathbf{\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-020";
          severity = Info;
          message = {|Missing \cdot between coefficient and vector|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-020"; run; languages = [] }

(* MATH-021: Absolute value bars |x| instead of \lvert ... \rvert *)
let l1_math_021_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if seg.[!i] = '|' then (
            if
              (* Skip \| (double bar) and already-typed \lvert/\rvert *)
              !i > 0 && seg.[!i - 1] = '\\'
            then incr i
            else
              (* Look for matching closing | *)
              let j = ref (!i + 1) in
              while !j < n && seg.[!j] <> '|' do
                if seg.[!j] = '\\' then j := !j + 2 else incr j
              done;
              if !j < n then (
                (* Found |...| pair — this should be \lvert..\rvert *)
                incr cnt;
                i := !j + 1)
              else i := !i + 1)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-021";
          severity = Info;
          message = {|Absolute value bars ‘|x|’ instead of \lvert … \rvert|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-021"; run; languages = [] }

(* MATH-022: Bold math italic without \bm or \mathbf — detects when \textbf is
   used inside math mode for bold math *)
let l1_math_022_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\textbf{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-022";
          severity = Info;
          message = {|Bold math italic without \bm or \mathbf|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-022"; run; languages = [] }

(* MATH-025: align environment with one column — use equation instead. Detects
   \begin{align}...\end{align} blocks with no & inside. *)
let l1_math_025_rule : rule =
  let re_begin = Re_compat.regexp {|\\begin{align\*?}|} in
  let re_end = Re_compat.regexp {|\\end{align\*?}|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    let n = String.length s in
    (try
       while !i < n do
         let _mr, pos = Re_compat.search_forward re_begin s !i in
         let after_begin =
           pos + String.length (Re_compat.matched_string _mr s)
         in
         try
           let _mr, end_pos = Re_compat.search_forward re_end s after_begin in
           let body = String.sub s after_begin (end_pos - after_begin) in
           if not (String.contains body '&') then incr cnt;
           i := end_pos + 1
         with Not_found -> i := n
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "MATH-025";
          severity = Info;
          message = "align environment with one column – use equation";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-025"; run; languages = [] }

(* MATH-028: Array environment inside math without column alignment spec.
   Detects \begin{array} without a brace argument following. *)
let l1_math_028_rule : rule =
  let re = Re_compat.regexp {|\\begin{array}[^{]|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _mr, _ = Re_compat.search_forward re s !i in
         incr cnt;
         i := Re_compat.match_end _mr
       done
     with Not_found -> ());
    (* Also check \begin{array} at end of string with nothing after *)
    let ba = {|\begin{array}|} in
    let ba_len = String.length ba in
    (if String.length s >= ba_len then
       let tail = String.sub s (String.length s - ba_len) ba_len in
       if tail = ba then incr cnt);
    if !cnt > 0 then
      Some
        {
          id = "MATH-028";
          severity = Info;
          message = "Array environment inside math lacks {c} alignment";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-028"; run; languages = [] }

(* MATH-029: Use of eqnarray / eqnarray* instead of align / align*. eqnarray is
   deprecated — spacing around = is wrong. *)
let l1_math_029_rule : rule =
  let re = Re_compat.regexp {|\\begin{eqnarray\*?}|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _mr, _ = Re_compat.search_forward re s !i in
         incr cnt;
         i := Re_compat.match_end _mr
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "MATH-029";
          severity = Warning;
          message = "Use of eqnarray* instead of align*";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-029"; run; languages = [] }

(* MATH-030: Overuse of \displaystyle in inline math — using \displaystyle in
   $...$ or \(...\) hurts line spacing *)
let l1_math_030_rule : rule =
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\displaystyle")
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-030";
          severity = Info;
          message = {|Overuse of \displaystyle in inline math|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-030"; run; languages = [] }

(* MATH-031: Operator spacing error — missing \; before \text in math *)
let l1_math_031_rule : rule =
  let re = Re_compat.regexp {|[A-Za-z0-9}]\\text{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Count \text{ preceded by letter/digit/} without \; \, \quad etc. *)
        cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-031";
          severity = Info;
          message = {|Operator spacing error: missing \; before \text|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-031"; run; languages = [] }

(* MATH-033: Use of \pm where +/- symbol required in text — \pm outside math *)
let l1_math_033_rule : rule =
  let run s =
    let text_parts = strip_math_segments s in
    let cnt = count_substring text_parts "\\pm" in
    if cnt > 0 then
      Some
        {
          id = "MATH-033";
          severity = Info;
          message = {|Use of \pm where ± symbol required in text|};
          count = cnt;
        }
    else None
  in
  { id = "MATH-033"; run; languages = [] }

(* MATH-034: Spacing before differential in integral missing \, — detects \int
   ... dx without \, before d *)
let l1_math_034_rule : rule =
  let diff_vars = "xytszrm" in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        if count_substring seg "\\int" > 0 then
          let n = String.length seg in
          let i = ref 0 in
          while !i < n - 1 do
            if seg.[!i] = 'd' && String.contains diff_vars seg.[!i + 1] then (
              (* Check the char after the differential var is not a letter *)
              let after_ok =
                !i + 2 >= n
                ||
                let c = seg.[!i + 2] in
                not ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'))
              in
              (if after_ok then
                 (* Check preceding context: should have \, before d *)
                 let has_thin_space =
                   !i >= 2 && seg.[!i - 2] = '\\' && seg.[!i - 1] = ','
                 in
                 let has_mathrm =
                   !i >= 8 && String.sub seg (!i - 8) 8 = "\\mathrm{"
                 in
                 if (not has_thin_space) && not has_mathrm then
                   (* Check there's a preceding letter/digit/paren before d *)
                   let prev_ok =
                     !i > 0
                     &&
                     let c = seg.[!i - 1] in
                     (c >= 'A' && c <= 'Z')
                     || (c >= 'a' && c <= 'z')
                     || (c >= '0' && c <= '9')
                     || c = ')'
                     || c = '}'
                     || c = ' '
                   in
                   if prev_ok then incr cnt);
              i := !i + 2)
            else incr i
          done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-034";
          severity = Info;
          message = {|Spacing before differential in integral missing \,|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-034"; run; languages = [] }

(* MATH-035: Multiple subscripts stacked vertically without braces — a_{i}_{j}
   pattern instead of a_{i,j} *)
let l1_math_035_rule : rule =
  let re = Re_compat.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)_|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-035";
          severity = Warning;
          message = "Multiple subscripts stacked vertically without braces";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-035"; run; languages = [] }

(* MATH-036: Superfluous \mathrm{} around single letter — \mathrm{x} is overkill
   for one letter *)
let l1_math_036_rule : rule =
  let re = Re_compat.regexp {|\\mathrm{[A-Za-z]}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-036";
          severity = Info;
          message = {|Superfluous \mathrm{} around single letter|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-036"; run; languages = [] }

(* MATH-037: \sfrac (xfrac package) used outside text mode — \sfrac is for
   inline text fractions *)
let l1_math_037_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\sfrac{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-037";
          severity = Info;
          message = "xfrac package fraction used outside text mode";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-037"; run; languages = [] }

(* MATH-038: Nested \frac three levels deep — readability issue *)
let l1_math_038_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Scan for \frac and track nesting depth via brace counting *)
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if
            !i + 5 < n
            && seg.[!i] = '\\'
            && seg.[!i + 1] = 'f'
            && seg.[!i + 2] = 'r'
            && seg.[!i + 3] = 'a'
            && seg.[!i + 4] = 'c'
            && seg.[!i + 5] = '{'
          then (
            (* Found \frac{, now count how many nested \frac{ appear in its
               arguments *)
            let depth = ref 1 in
            let brace_level = ref 1 in
            let j = ref (!i + 6) in
            let max_depth = ref 1 in
            (* scan through both arguments of \frac *)
            let args_seen = ref 0 in
            while !j < n && !args_seen < 2 do
              if seg.[!j] = '{' then (
                incr brace_level;
                (* Check if this is another \frac{ *)
                if
                  !j >= 5
                  && seg.[!j - 5] = '\\'
                  && seg.[!j - 4] = 'f'
                  && seg.[!j - 3] = 'r'
                  && seg.[!j - 2] = 'a'
                  && seg.[!j - 1] = 'c'
                then (
                  incr depth;
                  if !depth > !max_depth then max_depth := !depth);
                incr j)
              else if seg.[!j] = '}' then (
                decr brace_level;
                if !brace_level = 0 then (
                  incr args_seen;
                  if !args_seen < 2 && !j + 1 < n && seg.[!j + 1] = '{' then (
                    brace_level := 1;
                    j := !j + 2)
                  else incr j)
                else incr j)
              else incr j
            done;
            if !max_depth >= 3 then incr cnt;
            i := !i + 6)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-038";
          severity = Warning;
          message = {|Nested \frac three levels deep|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-038"; run; languages = [] }

(* MATH-039: Stacked relational operators without \substack — detects patterns
   like \underset{x}{\overset{y}{=}} which should use \substack *)
let l1_math_039_rule : rule =
  let re = Re_compat.regexp {|\\underset{[^}]*}{\\overset{|} in
  let re2 = Re_compat.regexp {|\\overset{[^}]*}{\\underset{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        cnt := !cnt + count_re_matches re seg + count_re_matches re2 seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-039";
          severity = Warning;
          message = {|Stacked relational operators without \atop|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-039"; run; languages = [] }

(* MATH-040: Ellipsis \ldots used between operators on the center axis — should
   be \cdots for +, -, = etc. *)
let l1_math_040_rule : rule =
  let re = Re_compat.regexp {|[+=<>-][ ]*\\ldots[ ]*[+=<>-]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-040";
          severity = Info;
          message = {|Ellipsis \ldots used between vertical alignment|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-040"; run; languages = [] }

(* MATH-041: Integral limits written inline in display — use \limits or
   \displaystyle \int for display integrals *)
let l1_math_041_rule : rule =
  let re = Re_compat.regexp {|\\int_|} in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* \int_ in inline math — limits are typeset inline, suggest display *)
        cnt := !cnt + count_re_matches re seg)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-041";
          severity = Info;
          message = {|Integral limits written inline; use \displaystyle \int|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-041"; run; languages = [] }

(* MATH-042: Missing \, between number and unit in math — e.g. 5kg should be
   5\,\mathrm{kg} *)
let l1_math_042_rule : rule =
  let re = Re_compat.regexp {|[0-9]\\mathrm{\|[0-9]\\text{\|[0-9]\\textrm{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-042";
          severity = Info;
          message = {|Missing \, between numbers and units in math|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-042"; run; languages = [] }

(* MATH-043: Use of \text instead of \operatorname for function names in math —
   \text{Var} should be \operatorname{Var} *)
let l1_math_043_rule : rule =
  let re = Re_compat.regexp {|\\text{[A-Z][a-z]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* \text{Xxx} in math is likely a function name that should use
           \operatorname *)
        cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-043";
          severity = Warning;
          message = {|Use of \text instead of \operatorname for function|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-043"; run; languages = [] }

(* MATH-044: Binary relation typed as text char — e.g. < for \le, = for \equiv,
   etc., when text < > appear in math outside of delimiters *)
let l1_math_044_rule : rule =
  let re = Re_compat.regexp {|[^\\]<=\|[^\\]>=|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-044";
          severity = Warning;
          message = {|Binary relation typed as text char (e.g. < for \le)|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-044"; run; languages = [] }

(* MATH-045: Math italic capital Greek without \mathrm — e.g. bare \Gamma when
   the document uses upright Greek capitals *)
let l1_math_045_rule : rule =
  let greek_capitals =
    [
      "\\Gamma";
      "\\Delta";
      "\\Theta";
      "\\Lambda";
      "\\Xi";
      "\\Pi";
      "\\Sigma";
      "\\Upsilon";
      "\\Phi";
      "\\Psi";
      "\\Omega";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let has_upright = ref false in
    let bare_cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun gc ->
            let upright_form = "\\mathrm{" ^ gc ^ "}" in
            if count_substring seg upright_form > 0 then has_upright := true;
            let total = count_substring seg gc in
            let wrapped = count_substring seg upright_form in
            let bare = total - wrapped in
            if bare > 0 then bare_cnt := !bare_cnt + bare)
          greek_capitals)
      math_segs;
    (* Only flag if document mixes upright and italic for the same class *)
    if !has_upright && !bare_cnt > 0 then
      Some
        {
          id = "MATH-045";
          severity = Info;
          message = {|Math italic capital Greek without \mathrm|};
          count = !bare_cnt;
        }
    else None
  in
  { id = "MATH-045"; run; languages = [] }

(* MATH-046: Ellipsis \ldots on relation axis — prefer \cdots between commas, +
   etc. *)
let l1_math_046_rule : rule =
  let re = Re_compat.regexp {|,[ ]*\\ldots[ ]*,|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-046";
          severity = Info;
          message = {|Ellipsis \ldots used on relation axis; prefer \cdots|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-046"; run; languages = [] }

(* MATH-047: Double superscript without braces — a^b^c is a TeX error *)
let l1_math_047_rule : rule =
  let re = Re_compat.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)\^|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-047";
          severity = Error;
          message = "Double superscript without braces a^b^c";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-047"; run; languages = [] }

(* MATH-048: Boldface digits via \mathbf in math — \mathbf{1} etc. is typically
   unnecessary *)
let l1_math_048_rule : rule =
  let re = Re_compat.regexp {|\\mathbf{[0-9]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-048";
          severity = Info;
          message = {|Boldface digits via \mathbf in math – avoid|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-048"; run; languages = [] }

(* MATH-049: Missing spacing around \times — detects a\times b without
   surrounding spaces *)
let l1_math_049_rule : rule =
  let re_no_space_before = Re_compat.regexp {|[A-Za-z0-9}]\\times|} in
  let re_no_space_after = Re_compat.regexp {|\\times[A-Za-z0-9{]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let total_times = count_substring seg "\\times" in
        if total_times > 0 then
          let before = count_re_matches re_no_space_before seg in
          let after = count_re_matches re_no_space_after seg in
          let bad = min total_times (max before after) in
          if bad > 0 then cnt := !cnt + bad)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-049";
          severity = Info;
          message = {|Spacing around \times missing|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-049"; run; languages = [] }

(* MATH-050: Circumflex accent \hat on multi-letter argument — \hat{abc} should
   typically be \widehat{abc} *)
let l1_math_050_rule : rule =
  let re = Re_compat.regexp {|\\hat{[A-Za-z][A-Za-z]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-050";
          severity = Warning;
          message = {|Circumflex accent ^\hat on multi‑letter|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-050"; run; languages = [] }

(* MATH-051: Radical \sqrt nested two levels — \sqrt{\sqrt{}} is hard to read *)
let l1_math_051_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Find \sqrt{ and look for nested \sqrt{ inside its argument *)
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if
            !i + 5 < n
            && seg.[!i] = '\\'
            && seg.[!i + 1] = 's'
            && seg.[!i + 2] = 'q'
            && seg.[!i + 3] = 'r'
            && seg.[!i + 4] = 't'
            && (seg.[!i + 5] = '{' || seg.[!i + 5] = '[')
          then (
            (* Found \sqrt{ or \sqrt[, scan the argument for nested \sqrt *)
            let start =
              if seg.[!i + 5] = '[' then (
                (* Skip optional argument \sqrt[n]{...} *)
                let j = ref (!i + 6) in
                while !j < n && seg.[!j] <> ']' do
                  incr j
                done;
                if !j < n && !j + 1 < n && seg.[!j + 1] = '{' then !j + 2
                else !i + 6)
              else !i + 6
            in
            let brace_level = ref 1 in
            let j = ref start in
            let found_nested = ref false in
            while !j < n && !brace_level > 0 do
              if seg.[!j] = '{' then (
                (* Check if this is \sqrt{ *)
                if
                  !j >= 5
                  && seg.[!j - 5] = '\\'
                  && seg.[!j - 4] = 's'
                  && seg.[!j - 3] = 'q'
                  && seg.[!j - 2] = 'r'
                  && seg.[!j - 1] = 't'
                then found_nested := true;
                incr brace_level;
                incr j)
              else if seg.[!j] = '}' then (
                decr brace_level;
                incr j)
              else incr j
            done;
            if !found_nested then incr cnt;
            i := !i + 6)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-051";
          severity = Warning;
          message = {|Radical \sqrt nested two levels|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-051"; run; languages = [] }

(* MATH-052: \over primitive used — prefer \frac{a}{b} over {a \over b} *)
let l1_math_052_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Count \over that is NOT \overbrace, \overline, \overset,
           \overrightarrow, \overleftarrow, \overleftrightarrow *)
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if
            !i + 5 <= n
            && seg.[!i] = '\\'
            && seg.[!i + 1] = 'o'
            && seg.[!i + 2] = 'v'
            && seg.[!i + 3] = 'e'
            && seg.[!i + 4] = 'r'
          then (
            (* Check it's bare \over (followed by space, brace, or end) and not
               \overbrace etc *)
            let after = if !i + 5 < n then seg.[!i + 5] else ' ' in
            if
              after = ' '
              || after = '{'
              || after = '\\'
              || after = '\n'
              || after = '\t'
              || !i + 5 = n
            then incr cnt;
            i := !i + 5)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-052";
          severity = Warning;
          message = {|\over brace used; prefer \frac|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-052"; run; languages = [] }

(* MATH-053: Space after \left( — spurious space *)
let l1_math_053_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          let prefix = "\\left(" in
          let plen = String.length prefix in
          if
            !i + plen < n
            && String.sub seg !i plen = prefix
            && seg.[!i + plen] = ' '
          then (
            incr cnt;
            i := !i + plen)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-053";
          severity = Info;
          message = {|Space after \left( at line start|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-053"; run; languages = [] }

(* ═══════════════════════════════════════════════════════════════════════
   MATH-C validators: extended math checks (MATH-055..MATH-108)
   ═══════════════════════════════════════════════════════════════════════ *)

(* MATH-055: \mathcal for single character only — flag multi-char argument *)
let l1_math_055_rule : rule =
  let re = Re_compat.regexp {|\\mathcal{[^}][^}]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-055";
          severity = Info;
          message = {|Math font change \mathcal for single character only|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-055"; run; languages = [] }

(* MATH-057: Empty fraction numerator or denominator *)
let l1_math_057_rule : rule =
  let is_empty_brace s i =
    (* Check if s.[i] = '{' and contents are only whitespace up to '}' *)
    let n = String.length s in
    if i >= n || s.[i] <> '{' then false
    else
      let j = ref (i + 1) in
      while !j < n && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\n') do
        incr j
      done;
      !j < n && s.[!j] = '}'
  in
  let skip_brace s i =
    let n = String.length s in
    if i >= n || s.[i] <> '{' then i
    else
      let depth = ref 1 in
      let j = ref (i + 1) in
      while !j < n && !depth > 0 do
        if s.[!j] = '{' then incr depth else if s.[!j] = '}' then decr depth;
        incr j
      done;
      !j
  in
  let tag = "\\frac" in
  let tlen = String.length tag in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i <= n - tlen do
          if String.sub seg !i tlen = tag then (
            (* Skip whitespace after \frac *)
            let j = ref (!i + tlen) in
            while
              !j < n && (seg.[!j] = ' ' || seg.[!j] = '\t' || seg.[!j] = '\n')
            do
              incr j
            done;
            let arg1_start = !j in
            if is_empty_brace seg arg1_start then incr cnt;
            let after_arg1 = skip_brace seg arg1_start in
            (* Skip whitespace between args *)
            let k = ref after_arg1 in
            while
              !k < n && (seg.[!k] = ' ' || seg.[!k] = '\t' || seg.[!k] = '\n')
            do
              incr k
            done;
            if is_empty_brace seg !k then incr cnt;
            i := max (!i + 1) after_arg1)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-057";
          severity = Error;
          message = "Empty fraction numerator or denominator";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-057"; run; languages = [] }

(* MATH-058: Nested \text inside \text *)
let l1_math_058_rule : rule =
  let re = Re_compat.regexp {|\\text{[^}]*\\text{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-058";
          severity = Info;
          message = "Nested \\text inside \\text";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-058"; run; languages = [] }

(* MATH-065: Manual spacing \hspace in math *)
let l1_math_065_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\hspace")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-065";
          severity = Info;
          message = {|Manual spacing \hspace in math detected|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-065"; run; languages = [] }

(* MATH-066: \phantom used; suggest \hphantom or \vphantom *)
let l1_math_066_rule : rule =
  let re = Re_compat.regexp {|\\phantom{|} in
  let not_hv_re = Re_compat.regexp {|\\[hv]phantom{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let total = count_re_matches re seg in
        let hv = count_re_matches not_hv_re seg in
        cnt := !cnt + (total - hv))
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-066";
          severity = Info;
          message = {|\phantom used; suggest \hphantom or \vphantom|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-066"; run; languages = [] }

(* MATH-068: Spacing around \mid missing *)
let l1_math_068_rule : rule =
  let re = Re_compat.regexp "[^ \t\n]\\\\mid\\|\\\\mid[^ \t\n]" in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-068";
          severity = Info;
          message = "Spacing around \\mid missing";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-068"; run; languages = [] }

(* MATH-069: Bold sans-serif math font used *)
let l1_math_069_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        cnt :=
          !cnt
          + count_substring seg "\\mathbfsf"
          + count_substring seg "\\bm{\\mathsf{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-069";
          severity = Info;
          message = "Bold sans‑serif math font used";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-069"; run; languages = [] }

(* MATH-071: Overuse of \cancel in equations — more than 3 per equation *)
let l1_math_071_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = count_substring seg "\\cancel{" in
        if n > 3 then incr cnt)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-071";
          severity = Info;
          message = {|Overuse of \cancel in equations|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-071"; run; languages = [] }

(* MATH-078: Long arrow typed as --> instead of \longrightarrow *)
let l1_math_078_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg "-->") math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-078";
          severity = Info;
          message = {|Long arrow typed as --> instead of \longrightarrow|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-078"; run; languages = [] }

(* MATH-079: \displaystyle inside display math — redundant *)
let l1_math_079_rule : rule =
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
      "displaymath";
    ]
  in
  let run s =
    let cnt = ref 0 in
    (* Check \[...\] blocks *)
    let len = String.length s in
    let i = ref 0 in
    while !i < len - 1 do
      if s.[!i] = '\\' && s.[!i + 1] = '[' then (
        let start = !i + 2 in
        let j = ref start in
        while !j < len - 1 && not (s.[!j] = '\\' && s.[!j + 1] = ']') do
          incr j
        done;
        if !j < len - 1 then (
          let body = String.sub s start (!j - start) in
          cnt := !cnt + count_substring body "\\displaystyle";
          i := !j + 2)
        else i := len)
      else incr i
    done;
    (* Check display math environments *)
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk -> cnt := !cnt + count_substring blk "\\displaystyle")
          blocks)
      display_envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-079";
          severity = Info;
          message = {|\displaystyle inside display math – redundant|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-079"; run; languages = [] }

(* MATH-082: Negative thin space \! misused twice consecutively *)
let l1_math_082_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg "\\!\\!") math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-082";
          severity = Warning;
          message = {|Negative thin space \! misused twice consecutively|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-082"; run; languages = [] }

(* MATH-085: Use of \eqcirc — rarely acceptable *)
let l1_math_085_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\eqcirc")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-085";
          severity = Info;
          message = {|Use of \eqcirc – rarely acceptable|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-085"; run; languages = [] }

(* MATH-094: Manual \kern in math detected *)
let l1_math_094_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg "\\kern") math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-094";
          severity = Info;
          message = {|Manual \kern in math detected – typographic smell|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-094"; run; languages = [] }

(* MATH-105: \textstyle used inside display math — redundant *)
let l1_math_105_rule : rule =
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
      "displaymath";
    ]
  in
  let run s =
    let cnt = ref 0 in
    (* Check \[...\] blocks *)
    let len = String.length s in
    let i = ref 0 in
    while !i < len - 1 do
      if s.[!i] = '\\' && s.[!i + 1] = '[' then (
        let start = !i + 2 in
        let j = ref start in
        while !j < len - 1 && not (s.[!j] = '\\' && s.[!j + 1] = ']') do
          incr j
        done;
        if !j < len - 1 then (
          let body = String.sub s start (!j - start) in
          cnt := !cnt + count_substring body "\\textstyle";
          i := !j + 2)
        else i := len)
      else incr i
    done;
    (* Check display math environments *)
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk -> cnt := !cnt + count_substring blk "\\textstyle")
          blocks)
      display_envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-105";
          severity = Info;
          message = {|\textstyle used inside display math — redundant|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-105"; run; languages = [] }

(* MATH-056: \operatorname duplicated for same function *)
let l1_math_056_rule : rule =
  let re = Re_compat.regexp {|\\operatorname{[^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let names = ref [] in
        let i = ref 0 in
        try
          while true do
            let _mr, _ = Re_compat.search_forward re seg !i in
            let m = Re_compat.matched_string _mr seg in
            if List.mem m !names then incr cnt else names := m :: !names;
            i := Re_compat.match_end _mr
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-056";
          severity = Info;
          message = "\\operatorname duplicated for same function";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-056"; run; languages = [] }

(* MATH-059: Math accent \bar on group expression needs braces *)
let l1_math_059_rule : rule =
  let re = Re_compat.regexp {|\\bar{[^}]*[ +\-=][^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-059";
          severity = Warning;
          message = {|Math accent \bar on group expression needs braces|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-059"; run; languages = [] }

(* MATH-060: Differential d typeset italic — detect bare d in integral *)
let l1_math_060_rule : rule =
  let re = Re_compat.regexp {|\\int[^$]*[^\\]d[xyzt ]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        if
          count_substring seg "\\int" > 0
          && count_substring seg "\\mathrm{d}" = 0
          && count_re_matches re seg > 0
        then incr cnt)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-060";
          severity = Info;
          message = "Differential d typeset italic";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-060"; run; languages = [] }

(* MATH-061: Log base missing braces \log_10x *)
let l1_math_061_rule : rule =
  let re = Re_compat.regexp {|\\log_[0-9][0-9a-zA-Z]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-061";
          severity = Warning;
          message = {|Log base missing braces in \log_10x|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-061"; run; languages = [] }

(* MATH-067: Stacked limits on non-operator *)
let l1_math_067_rule : rule =
  let big_ops =
    [
      "\\sum";
      "\\prod";
      "\\int";
      "\\oint";
      "\\bigcup";
      "\\bigcap";
      "\\bigoplus";
      "\\bigotimes";
      "\\bigsqcup";
      "\\coprod";
      "\\lim";
      "\\sup";
      "\\inf";
      "\\max";
      "\\min";
      "\\limsup";
      "\\liminf";
    ]
  in
  let re = Re_compat.regexp {|\\limits|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _mr, pos = Re_compat.search_forward re seg !i in
            (* Check if preceded by a big operator *)
            let before = String.sub seg 0 pos in
            let preceded_by_op =
              List.exists
                (fun op ->
                  let olen = String.length op in
                  String.length before >= olen
                  && String.sub before (String.length before - olen) olen = op)
                big_ops
            in
            if not preceded_by_op then incr cnt;
            i := Re_compat.match_end _mr
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-067";
          severity = Warning;
          message = "Stacked limits on non‑operator";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-067"; run; languages = [] }

(* MATH-070: Multiline subscripts lack \substack *)
let l1_math_070_rule : rule =
  let re = Re_compat.regexp {|_{[^}]*\\\\[^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let matches = count_re_matches re seg in
        let substack_count = count_substring seg "\\substack" in
        if matches > substack_count then cnt := !cnt + (matches - substack_count))
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-070";
          severity = Info;
          message = {|Multiline subscripts lack \substack|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-070"; run; languages = [] }

(* MATH-073: \color used inside math *)
let l1_math_073_rule : rule =
  let re = Re_compat.regexp {|\\color{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-073";
          severity = Warning;
          message = {|xcolor macro \color used inside math|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-073"; run; languages = [] }

(* MATH-077: Alignment point & outside alignment environment *)
let l1_math_077_rule : rule =
  let align_envs =
    [
      "align";
      "align*";
      "aligned";
      "alignat";
      "alignat*";
      "array";
      "matrix";
      "pmatrix";
      "bmatrix";
      "Bmatrix";
      "vmatrix";
      "Vmatrix";
      "cases";
      "split";
      "eqnarray";
      "eqnarray*";
      "tabular";
    ]
  in
  let run s =
    let cnt = ref 0 in
    (* Check equation environments that are NOT alignment envs *)
    let non_align_envs =
      [ "equation"; "equation*"; "gather"; "gather*"; "multline"; "multline*" ]
    in
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            (* Count bare & not inside nested align env *)
            let has_align_inner =
              List.exists
                (fun aenv -> count_substring blk ("\\begin{" ^ aenv ^ "}") > 0)
                align_envs
            in
            if not has_align_inner then
              let n = String.length blk in
              for i = 0 to n - 1 do
                if blk.[i] = '&' && (i = 0 || blk.[i - 1] <> '\\') then incr cnt
              done)
          blocks)
      non_align_envs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-077";
          severity = Error;
          message = "Alignment point & outside alignment environment";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-077"; run; languages = [] }

(* MATH-081: Improper kerning f(x) — suggest f\!\left(x\right) *)
let l1_math_081_rule : rule =
  let re = Re_compat.regexp {|[a-zA-Z]([^)]*)|} in
  let is_part_of_cmd seg pos =
    (* Check if the letter at pos is part of a \command like \left, \right,
       etc. *)
    let rec find_bs i =
      if i < 0 then false
      else if seg.[i] = '\\' then
        let cmd_len = pos - i in
        cmd_len >= 2
      else if
        (seg.[i] >= 'a' && seg.[i] <= 'z') || (seg.[i] >= 'A' && seg.[i] <= 'Z')
      then find_bs (i - 1)
      else false
    in
    pos > 0 && find_bs (pos - 1)
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _mr, pos = Re_compat.search_forward re seg !i in
            (* Check it's not preceded by \! and the letter is not part of a
               \cmd *)
            let has_kern =
              pos >= 2 && seg.[pos - 2] = '\\' && seg.[pos - 1] = '!'
            in
            if (not has_kern) && not (is_part_of_cmd seg pos) then incr cnt;
            i := Re_compat.match_end _mr
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-081";
          severity = Info;
          message = {|Improper kerning f(x) – suggest f\!\left(x\right)|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-081"; run; languages = [] }

(* MATH-084: Displaystyle \sum in inline math *)
let l1_math_084_rule : rule =
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        if
          count_substring seg "\\displaystyle" > 0
          && count_substring seg "\\sum" > 0
        then incr cnt)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-084";
          severity = Info;
          message = {|Displaystyle \sum in inline math|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-084"; run; languages = [] }

(* MATH-086: Nested root \sqrt{\sqrt{...}} depth > 2 *)
let l1_math_086_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\sqrt{\\sqrt{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-086";
          severity = Warning;
          message = {|Nested root \sqrt{\sqrt{…}} depth > 2|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-086"; run; languages = [] }

(* MATH-090: Nested \frac depth > 3 *)
let l1_math_090_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\\frac{\\frac{\\frac{")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-090";
          severity = Warning;
          message = {|Nested \frac depth > 3 – suggest \dfrac + \smash|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-090"; run; languages = [] }

(* MATH-093: Multi-letter italic variable — suggest \mathit{} *)
let l1_math_093_rule : rule =
  let re = Re_compat.regexp {|[^\\a-zA-Z{]\([a-zA-Z][a-zA-Z]+\)[^a-zA-Z}]|} in
  let known_funcs =
    [
      "sin";
      "cos";
      "tan";
      "log";
      "ln";
      "exp";
      "lim";
      "max";
      "min";
      "sup";
      "inf";
      "det";
      "dim";
      "ker";
      "deg";
      "gcd";
      "hom";
      "arg";
      "Pr";
      "mod";
      "if";
      "then";
      "else";
      "and";
      "or";
      "not";
      "for";
      "where";
      "such";
      "that";
      "with";
      "let";
      "set";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let padded = " " ^ seg ^ " " in
        let i = ref 0 in
        try
          while true do
            let _mr, _ = Re_compat.search_forward re padded !i in
            let word = Re_compat.matched_group _mr 1 padded in
            if not (List.mem word known_funcs) then incr cnt;
            i := Re_compat.match_end _mr - 1
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-093";
          severity = Info;
          message = {|Multi‑letter italic variable should be \mathit{}|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-093"; run; languages = [] }

(* MATH-098: Too many \qquad (> 2) in single line *)
let l1_math_098_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let lines = String.split_on_char '\n' seg in
        List.iter
          (fun line -> if count_substring line "\\qquad" > 2 then incr cnt)
          lines)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-098";
          severity = Info;
          message = {|Too many \qquad (> 2) in single line|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-098"; run; languages = [] }

(* MATH-072: Unknown math operator name — \operatorname{X} where X is a
   predefined LaTeX function like \det, \lim, \sin etc. *)
let l1_math_072_rule : rule =
  let known_ops =
    [
      "det";
      "lim";
      "sin";
      "cos";
      "tan";
      "log";
      "ln";
      "exp";
      "sup";
      "inf";
      "max";
      "min";
      "gcd";
      "deg";
      "dim";
      "hom";
      "ker";
      "arg";
      "Pr";
      "sec";
      "csc";
      "cot";
      "arcsin";
      "arccos";
      "arctan";
      "sinh";
      "cosh";
      "tanh";
      "limsup";
      "liminf";
      "projlim";
      "injlim";
      "varlimsup";
      "varliminf";
    ]
  in
  let re = Re_compat.regexp {|\\operatorname{[^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _mr, _ = Re_compat.search_forward re seg !i in
            let m = Re_compat.matched_string _mr seg in
            (* Extract the name between { and } *)
            let brace_start =
              (try String.index_from m 0 '{' with Not_found -> -1) + 1
            in
            let brace_end =
              try String.index_from m brace_start '}'
              with Not_found -> String.length m
            in
            let name = String.sub m brace_start (brace_end - brace_start) in
            if List.mem name known_ops then incr cnt;
            i := Re_compat.match_end _mr
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-072";
          severity = Warning;
          message = "Unknown math operator name";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-072"; run; languages = [] }

(* MATH-074: TikZ \node inside math without math mode key *)
let l1_math_074_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        if
          count_substring seg "\\node" > 0
          && count_substring seg "math mode" = 0
        then cnt := !cnt + count_substring seg "\\node")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-074";
          severity = Warning;
          message = "TikZ node inside math without math mode set";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-074"; run; languages = [] }

(* MATH-087: Fake bold digits via \mathbf{0}...\mathbf{9} *)
let l1_math_087_rule : rule =
  let re = Re_compat.regexp {|\\mathbf{[0-9]+}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-087";
          severity = Info;
          message = {|Maths uses fake bold via \mathbf on digits|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-087"; run; languages = [] }

(* MATH-088: Bare \partial lacks thin space *)
let l1_math_088_rule : rule =
  let re = Re_compat.regexp "[^ \t,\\\\]\\\\partial\\|\\\\partial[^ \t{\\\\]" in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-088";
          severity = Info;
          message = {|Bare \partial lacks thin‑space before/after|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-088"; run; languages = [] }

(* MATH-091: \operatorname{X} used when predefined \X exists *)
let l1_math_091_rule : rule =
  (* This is the same detection as MATH-072 but with a different message. We
     alias it via the same logic registered under a separate ID. *)
  let known_ops =
    [
      "det";
      "lim";
      "sin";
      "cos";
      "tan";
      "log";
      "ln";
      "exp";
      "sup";
      "inf";
      "max";
      "min";
      "gcd";
      "deg";
      "dim";
      "hom";
      "ker";
      "arg";
      "Pr";
    ]
  in
  let re = Re_compat.regexp {|\\operatorname{[^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _mr, _ = Re_compat.search_forward re seg !i in
            let m = Re_compat.matched_string _mr seg in
            let brace_start =
              (try String.index_from m 0 '{' with Not_found -> -1) + 1
            in
            let brace_end =
              try String.index_from m brace_start '}'
              with Not_found -> String.length m
            in
            let name = String.sub m brace_start (brace_end - brace_start) in
            if List.mem name known_ops then incr cnt;
            i := Re_compat.match_end _mr
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-091";
          severity = Info;
          message = {|\operatorname{det} used – predefined \det exists|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-091"; run; languages = [] }

(* MATH-092: \sum with explicit limits in inline math *)
let l1_math_092_rule : rule =
  let re = Re_compat.regexp "\\\\sum[ \t]*_" in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-092";
          severity = Info;
          message = "\\sum with explicit limits in inline math";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-092"; run; languages = [] }

(* MATH-095: Log base without braces — alias of MATH-061 logic *)
let l1_math_095_rule : rule =
  let re = Re_compat.regexp {|\\log_[0-9][0-9a-zA-Z]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-095";
          severity = Warning;
          message = {|Log base typeset without braces (\log_10x)|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-095"; run; languages = [] }

(* MATH-096: Bold Greek via \mathbf — use \boldsymbol *)
let l1_math_096_rule : rule =
  let greek_letters =
    [
      "\\alpha";
      "\\beta";
      "\\gamma";
      "\\delta";
      "\\epsilon";
      "\\zeta";
      "\\eta";
      "\\theta";
      "\\iota";
      "\\kappa";
      "\\lambda";
      "\\mu";
      "\\nu";
      "\\xi";
      "\\pi";
      "\\rho";
      "\\sigma";
      "\\tau";
      "\\upsilon";
      "\\phi";
      "\\chi";
      "\\psi";
      "\\omega";
      "\\Gamma";
      "\\Delta";
      "\\Theta";
      "\\Lambda";
      "\\Xi";
      "\\Pi";
      "\\Sigma";
      "\\Phi";
      "\\Psi";
      "\\Omega";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun gl -> cnt := !cnt + count_substring seg ("\\mathbf{" ^ gl ^ "}"))
          greek_letters)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-096";
          severity = Info;
          message = {|Bold Greek via \mathbf – use \boldsymbol|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-096"; run; languages = [] }

(* MATH-097: Arrow => typed instead of \implies *)
let l1_math_097_rule : rule =
  let re = Re_compat.regexp {|[^=!<>\\]=>|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let padded = " " ^ seg in
        cnt := !cnt + count_re_matches re padded)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-097";
          severity = Info;
          message = {|Arrow '=>' typed instead of \implies|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-097"; run; languages = [] }

(* MATH-099: Large operator (\bigcup/\bigcap/\bigoplus) in inline math *)
let l1_math_099_rule : rule =
  let big_ops =
    [ "\\bigcup"; "\\bigcap"; "\\bigoplus"; "\\bigotimes"; "\\bigsqcup" ]
  in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter (fun op -> cnt := !cnt + count_substring seg op) big_ops)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-099";
          severity = Info;
          message = {|Large operator (\bigcup) used inline|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-099"; run; languages = [] }

(* MATH-101: Deprecated \over primitive used *)
let l1_math_101_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg "\\over") math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-101";
          severity = Warning;
          message = {|Deprecated \over primitive used; replace with \frac|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-101"; run; languages = [] }

(* MATH-104: Repeated \left(...\right) pairs without \DeclarePairedDelimiter *)
let l1_math_104_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let pairs = count_substring seg "\\left(" in
        if pairs > 2 && count_substring seg "\\DeclarePairedDelimiter" = 0 then
          cnt := !cnt + 1)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-104";
          severity = Info;
          message =
            {|Paired delimiters repeated without \DeclarePairedDelimiter|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-104"; run; languages = [] }

(* MATH-106: Misuse of \not= — prefer \neq *)
let l1_math_106_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg "\\not=") math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-106";
          severity = Info;
          message = {|Misuse of \not=; prefer \neq|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-106"; run; languages = [] }

(* MATH-108: Middle dot U+00B7 in math — use \cdot *)
let l1_math_108_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg "\xc2\xb7")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "MATH-108";
          severity = Info;
          message = {|Scalar product uses • (⋅) directly; require \cdot|};
          count = !cnt;
        }
    else None
  in
  { id = "MATH-108"; run; languages = [] }
