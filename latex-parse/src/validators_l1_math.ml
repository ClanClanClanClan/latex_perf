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
  let is_alnum c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
  in
  (* Fix producer (v27.1.11): backslash each bare operator (sin -> \sin). The
     detector's COUNT (below, over extract_math_segments) is untouched; the fix
     mirrors the SAME predicate on the ORIGINAL source [s] (offsets valid for
     the edit), gated to real math ranges via [find_math_ranges]. Whole-operator
     ASCII replace, so no multibyte sequence is ever split. Idempotent: after
     the rewrite the operator is preceded by '\', so [preceded_by_backslash]
     holds and it is no longer counted/rewritten -> the converge loop reaches a
     fixpoint. *)
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let n = String.length s in
    let edits = ref [] in
    List.iter
      (fun op ->
        let oplen = String.length op in
        let i = ref 0 in
        while !i + oplen <= n do
          if String.sub s !i oplen = op then (
            let preceded_by_backslash = !i > 0 && s.[!i - 1] = '\\' in
            let boundary_before = !i = 0 || not (is_alnum s.[!i - 1]) in
            let boundary_after =
              !i + oplen >= n || not (is_alnum s.[!i + oplen])
            in
            if
              (not preceded_by_backslash)
              && boundary_before
              && boundary_after
              && is_in_math_range math !i
            then
              edits :=
                Cst_edit.replace ~start_offset:!i ~end_offset:(!i + oplen)
                  ("\\" ^ op)
                :: !edits;
            i := !i + oplen)
          else incr i
        done)
      operators;
    List.rev !edits
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
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-009" ~severity:Warning
             ~message:{|Bare ‘sin/log/exp’ in math; use \sin, \log, \exp|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-009" ~severity:Warning
             ~message:{|Bare ‘sin/log/exp’ in math; use \sin, \log, \exp|}
             ~count:!cnt ~fix)
    else None
  in
  { id = "MATH-009"; run; languages = [] }

(* MATH-010: Division symbol ÷ (U+00F7) used — prefer \frac or solidus.

   v27.0.50: math-aware fix producer that replaces each `÷` (U+00F7, 2 bytes
   UTF-8 `\xc3\xb7`) with the canonical LaTeX `\div` (4 bytes ASCII) INSIDE math
   regions. The spec's "prefer \frac or solidus" advice asks the user to
   RESTRUCTURE the expression (a÷b → \frac{a}{b} or a/b); that's a
   context-dependent edit requiring argument parsing. Replacing `÷` with the
   equivalent `\div` macro is the conservative minimum-surprise fix: same glyph,
   correct math-mode spacing, no semantic restructuring. The diagnostic still
   fires to encourage the user to consider the restructuring option; the
   auto-fix gives them at least the canonical macro form. Same shape as
   MATH-082/106/108/015/078 (math-mode-only positive filter). Severity Warning
   preserved. *)
let l1_math_010_rule : rule =
  let needle = "\xc3\xb7" in
  let replacement = "\\div" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off
          ~end_offset:(off + String.length needle)
          (control_word_repl s (off + String.length needle) replacement))
      offsets
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg needle) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-010" ~severity:Warning
             ~message:{|Division symbol ÷ used; prefer \frac or solidus|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-010" ~severity:Warning
             ~message:{|Division symbol ÷ used; prefer \frac or solidus|}
             ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-011" ~severity:Info
           ~message:"Vector notation inconsistent within equation"
           ~count:(min !vec_count !mathbf_count))
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
    (* Bucket-C CANDIDATE fixes: wrap each detected multi-letter token in
       \operatorname{...}. Rebuilt on absolute offsets via find_math_ranges so
       the edit lands in the real source; the SAME gating as the count pass (not
       backslash-prefixed, not a known operator, length > 2, no
       \text/\mathrm/\operatorname wrapper). vcu-exempt keeps in-math candidates
       but drops any that fall in verbatim/comment/url. *)
    let candidates =
      let ranges = find_math_ranges s in
      let cands = ref [] in
      List.iter
        (fun (rs, re_end) ->
          let seg = String.sub s rs (re_end - rs) in
          let i = ref 0 in
          try
            while true do
              let mr, pos = Re_compat.search_forward re seg !i in
              let matched = Re_compat.matched_group mr 1 seg in
              let next_i = Re_compat.match_end mr in
              let preceded_by_backslash = pos > 0 && seg.[pos - 1] = '\\' in
              (* A letter run that is the TAIL of a control word (e.g. `amma` in
                 `\\Gamma`) is NOT a function name — scan back over letters and
                 check for a leading backslash, else `\\operatorname{amma}`
                 would corrupt the macro. *)
              let in_control_word =
                let j = ref (pos - 1) in
                while
                  !j >= 0
                  && ((seg.[!j] >= 'a' && seg.[!j] <= 'z')
                     || (seg.[!j] >= 'A' && seg.[!j] <= 'Z'))
                do
                  decr j
                done;
                !j >= 0 && seg.[!j] = '\\'
              in
              let is_known = List.mem matched known_operators in
              let is_short_var = String.length matched <= 2 in
              (if
                 (not preceded_by_backslash)
                 && (not in_control_word)
                 && (not is_known)
                 && not is_short_var
               then
                 let prefix_start = max 0 (pos - 16) in
                 let prefix =
                   String.sub seg prefix_start (pos - prefix_start)
                 in
                 let has_wrapper =
                   count_substring prefix "\\text{"
                   + count_substring prefix "\\mathrm{"
                   + count_substring prefix "\\operatorname{"
                   > 0
                 in
                 (* find_math_ranges includes the `\begin{env}` / `\end{env}`
                    delimiters of math environments; those env NAMES are
                    lowercase multi-letter tokens but must never be wrapped in
                    \operatorname. Skip a token sitting right after `\begin{` /
                    `\end{`. The count pass (body-only segments) never sees
                    these, so this keeps candidates consistent with the
                    diagnostic. *)
                 let ends_with suf =
                   let sl = String.length suf and pl = String.length prefix in
                   pl >= sl && String.sub prefix (pl - sl) sl = suf
                 in
                 let is_env_name = ends_with "\\begin{" || ends_with "\\end{" in
                 if (not has_wrapper) && not is_env_name then
                   cands :=
                     {
                       c_edits =
                         [
                           Cst_edit.replace ~start_offset:(rs + pos)
                             ~end_offset:(rs + next_i)
                             (Printf.sprintf {|\operatorname{%s}|} matched);
                         ];
                       c_label = {|Wrap multi-letter function in \operatorname|};
                     }
                     :: !cands);
              i := next_i
            done
          with Not_found -> ())
        ranges;
      candidates_drop_vcu_exempt s (List.rev !cands)
    in
    if !cnt > 0 then
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-012" ~severity:Warning
             ~message:{|Multi‑letter function not in roman (\operatorname{})|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-012" ~severity:Warning
             ~message:{|Multi‑letter function not in roman (\operatorname{})|}
             ~count:!cnt ~candidates)
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
    if !cnt > 0 then (
      (* Bucket-C candidate (v27.1.24): typeset the differential upright,
         replacing the bare `d` before the integration variable with
         `\mathrm{d}` (` dx` -> ` \mathrm{d}x`). Collected over the ORIGINAL
         source and gated to math ranges containing an integral. The `
         d[letter]` needle requires a space before `d`, so `\mathrm{d}` / `\,d`
         are already excluded. The replacement ends in `}`, which terminates
         cleanly before the variable. *)
      let ranges = find_math_ranges s in
      let int_ranges =
        List.filter
          (fun (a, b) ->
            let sub = String.sub s a (b - a) in
            count_substring sub "\\int" > 0
            || count_substring sub "\\iint" > 0
            || count_substring sub "\\iiint" > 0
            || count_substring sub "\\oint" > 0)
          ranges
      in
      let in_int_math off =
        List.exists (fun (a, b) -> off >= a && off < b) int_ranges
      in
      let cands = ref [] in
      let i = ref 0 in
      (try
         while true do
           let mr, pos = Re_compat.search_forward re s !i in
           let e = Re_compat.match_end mr in
           let d_off = pos + 1 in
           if in_int_math d_off then
             cands :=
               {
                 c_edits =
                   [
                     Cst_edit.make ~start_offset:d_off ~end_offset:(d_off + 1)
                       ~replacement:"\\mathrm{d}";
                   ];
                 c_label = "Typeset the differential d upright with \\mathrm{d}";
               }
               :: !cands;
           i := e
         done
       with Not_found -> ());
      let candidates = candidates_drop_vcu_exempt s (List.rev !cands) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-013" ~severity:Info
             ~message:"Differential d not typeset roman" ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-013" ~severity:Info
             ~message:"Differential d not typeset roman" ~count:!cnt ~candidates))
    else None
  in
  { id = "MATH-013"; run; languages = [] }

(* MATH-014: Inline \frac in running text — \frac inside $..$ or \(..\) is hard
   to read; prefer the text-style \tfrac.

   v27.0.67: inline-math-only fix producer that replaces each `\frac{` (6 bytes)
   inside an inline math range with `\tfrac{` (7 bytes). Inline-math gating via
   new helper `Validators_common.range_is_inline_math` (composes with
   `find_math_ranges` to filter out display math ranges). Single-needle match
   via `Validators_l0_typo.find_all_non_overlapping`; the needle `\frac{` does
   NOT substring-match `\tfrac{` or `\dfrac{` (different bytes at position 1),
   so existing `\tfrac` / `\dfrac` calls are correctly not affected.

   Same shape family as MATH-015 (v27.0.48 — `\stackrel{` → `\overset{` inside
   math) but inline-only filtered. Severity Info preserved. *)
let l1_math_014_rule : rule =
  let needle = "\\frac{" in
  let replacement = "\\tfrac{" in
  let inline_offsets s =
    let ranges = find_math_ranges s in
    let inline_ranges = List.filter (range_is_inline_math s) ranges in
    let inside off =
      List.exists (fun (a, b) -> a <= off && off < b) inline_ranges
    in
    List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
  in
  let mk_fix_edits s =
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off
          ~end_offset:(off + String.length needle)
          replacement)
      (inline_offsets s)
  in
  let run s =
    let offsets = inline_offsets s in
    let cnt = List.length offsets in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-014" ~severity:Info
             ~message:{|Inline \frac in running text|} ~count:cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-014" ~severity:Info
             ~message:{|Inline \frac in running text|} ~count:cnt ~fix)
    else None
  in
  { id = "MATH-014"; run; languages = [] }

(* MATH-015: \stackrel used — prefer \overset.

   v27.0.48: math-aware fix producer that replaces `\stackrel{` (10 bytes) with
   `\overset{` (9 bytes) INSIDE math regions. `\stackrel` is a plain-TeX legacy
   macro from amsmath's pre-history; the modern `\overset` (also from amsmath)
   takes the same {top}{bottom} argument structure and is now the canonical
   form. The replace only swaps the macro name — the opening brace and the
   subsequent arguments are untouched, so the fix is structurally safe. Same
   shape as MATH-082 / MATH-106 / MATH-108 (math-mode-only positive filter via
   `find_math_ranges`). Severity Warning preserved. *)
let l1_math_015_rule : rule =
  let needle = "\\stackrel{" in
  let replacement = "\\overset{" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off
          ~end_offset:(off + String.length needle)
          replacement)
      offsets
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg needle) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-015" ~severity:Warning
             ~message:{|\stackrel used; prefer \overset|} ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-015" ~severity:Warning
             ~message:{|\stackrel used; prefer \overset|} ~count:!cnt ~fix)
    else None
  in
  { id = "MATH-015"; run; languages = [] }

(* MATH-016: Nested subscripts without braces — e.g. x_i_j instead of x_{i_j} or
   x_{i,j} *)
let l1_math_016_rule : rule =
  let re = Re_compat.regexp {|_\([A-Za-z0-9]\)_|} in
  (* Fix regex additionally captures the trailing subscript token so the whole
     `_X_Y` span is bounded (X single alnum; Y single alnum or `{...}`). *)
  let re_fix = Re_compat.regexp {|_\([A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|} in
  let strip_braces g =
    let n = String.length g in
    if n >= 2 && g.[0] = '{' && g.[n - 1] = '}' then String.sub g 1 (n - 2)
    else g
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      (* Bucket-C candidate (v27.1.22): brace nested subscripts `a_b_c` ->
         `a_{b_{c}}` when both tokens are cleanly bounded. Intent-dependent
         (author may have meant `a_{b,c}` — see MATH-035), so review only. *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re_fix s i)
          with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let x = Re_compat.matched_group mr 1 s in
            let y = strip_braces (Re_compat.matched_group mr 2 s) in
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:("_{" ^ x ^ "_{" ^ y ^ "}}");
                    ];
                  c_label = "Brace nested subscripts as _{...}";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-016" ~severity:Warning
             ~message:"Nested subscripts without braces" ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-016" ~severity:Warning
             ~message:"Nested subscripts without braces" ~count:!cnt ~candidates)
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
        (mk_result ~id:"MATH-017" ~severity:Error
           ~message:{|Mismatched \left\{ … \right] pair|} ~count:!cnt)
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
        (mk_result ~id:"MATH-018" ~severity:Info
           ~message:"π written numerically as 3.14" ~count:!cnt)
    else None
  in
  { id = "MATH-018"; run; languages = [] }

(* MATH-019: Inline stacked ^_ order wrong — same concept as SCRIPT-021 but
   specifically for the pattern where _ immediately follows ^ without braces in
   inline math, e.g. $\sum^n_i$ instead of $\sum_{i}^{n}$ *)
let l1_math_019_rule : rule =
  (* MATH-019 targets inline OPERATOR-LIMIT-style stacked scripts (e.g.
     `\sum^n_i`), where sub-before-super `\sum_i^n` (lower limit first) is the
     conventional form — distinct from SCRIPT-021, which canonicalises general
     BRACED atoms to super-before-sub `a^{c}_{b}`. The two do not target the
     same construct (unbraced operator stack vs braced atom), so their opposite
     directions are intentional, not a conflict. *)
  let re =
    Re_compat.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) inline_segs;
    if !cnt > 0 then
      (* Bucket-C candidate (v27.1.22): reorder `x^a_b` -> `x_b^a`
         (operator-limit sub-before-super order). Both scripts are cleanly
         bounded by the same regex (single token or `{...}`); restricted to
         inline math to mirror the diagnostic scope. Semantics-preserving, but
         surfaced for review. *)
      let ranges = find_math_ranges s in
      let inline_ranges =
        List.filter (fun r -> range_is_inline_math s r) ranges
      in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re s i) with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let sup = Re_compat.matched_group mr 1 s in
            let sub = Re_compat.matched_group mr 2 s in
            let acc =
              if is_in_math_range inline_ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:("_" ^ sub ^ "^" ^ sup);
                    ];
                  c_label = "Reorder scripts to subscript-before-superscript";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-019" ~severity:Warning
             ~message:"Inline stacked ^_ order wrong" ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-019" ~severity:Warning
             ~message:"Inline stacked ^_ order wrong" ~count:!cnt ~candidates)
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
        (mk_result ~id:"MATH-020" ~severity:Info
           ~message:{|Missing \cdot between coefficient and vector|} ~count:!cnt)
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
        (mk_result ~id:"MATH-021" ~severity:Info
           ~message:{|Absolute value bars ‘|x|’ instead of \lvert … \rvert|}
           ~count:!cnt)
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
        (mk_result ~id:"MATH-022" ~severity:Info
           ~message:{|Bold math italic without \bm or \mathbf|} ~count:!cnt)
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
    (* Bucket-C CANDIDATE fixes: a single-column `align` is better written as
       `equation` (proper spacing, no phantom alignment tab), but swapping the
       environment can interact with cross-references / numbering, so surface it
       for review. Two edits rename the env name in the \begin and \end,
       preserving any trailing star (so `align*` becomes `equation*`). Count is
       untouched. *)
    let candidates = ref [] in
    let i = ref 0 in
    let n = String.length s in
    (try
       while !i < n do
         let _mr, pos = Re_compat.search_forward re_begin s !i in
         let after_begin =
           pos + String.length (Re_compat.matched_string _mr s)
         in
         try
           let _emr, end_pos = Re_compat.search_forward re_end s after_begin in
           let body = String.sub s after_begin (end_pos - after_begin) in
           if not (String.contains body '&') then (
             incr cnt;
             (* `\begin{align...}`: `\begin{` is 7 bytes, so "align" (5 bytes)
                begins at pos+7; any trailing star is left in place. `\end{` is
                5 bytes, so "align" begins at end_pos+5. *)
             let begin_name_off = pos + 7 in
             let end_name_off = end_pos + 5 in
             candidates :=
               {
                 c_edits =
                   [
                     Cst_edit.replace ~start_offset:begin_name_off
                       ~end_offset:(begin_name_off + 5) "equation";
                     Cst_edit.replace ~start_offset:end_name_off
                       ~end_offset:(end_name_off + 5) "equation";
                   ];
                 c_label = "Use equation instead of one-column align";
               }
               :: !candidates);
           i := end_pos + 1
         with Not_found -> i := n
       done
     with Not_found -> ());
    if !cnt > 0 then
      let candidates = candidates_drop_vcu_exempt s (List.rev !candidates) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-025" ~severity:Info
             ~message:"align environment with one column – use equation"
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-025" ~severity:Info
             ~message:"align environment with one column – use equation"
             ~count:!cnt ~candidates)
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
        (mk_result ~id:"MATH-028" ~severity:Info
           ~message:"Array environment inside math lacks {c} alignment"
           ~count:!cnt)
    else None
  in
  { id = "MATH-028"; run; languages = [] }

(* MATH-029: Use of eqnarray / eqnarray* instead of align / align*. eqnarray is
   deprecated — spacing around = is wrong. auto_replace fix: swap the
   environment name `eqnarray`/`eqnarray*` → `align`/`align*` on BOTH the
   `\begin{...}` and the matching `\end{...}` so the document stays well-formed.
   The diagnostic count (number of `\begin{eqnarray}`/`\begin{eqnarray*}`
   occurrences) is unchanged. Edits land on the environment delimiters, which
   sit at the boundary of the math range, so we filter against verbatim /
   comment / url ranges only (vcu-exempt) and KEEP in-math edits — a stray
   `\begin{eqnarray}` inside a verbatim block is counted but not rewritten. *)
let l1_math_029_rule : rule =
  let re = Re_compat.regexp {|\\begin{eqnarray\*?}|} in
  (* (needle, replacement) pairs. Each exact string is distinct (the `*` and `}`
     differ at the same offset) so no occurrence is matched twice. *)
  let pairs =
    [
      ("\\begin{eqnarray*}", "\\begin{align*}");
      ("\\begin{eqnarray}", "\\begin{align}");
      ("\\end{eqnarray*}", "\\end{align*}");
      ("\\end{eqnarray}", "\\end{align}");
    ]
  in
  let mk_fix_edits s =
    let vcu = find_verbatim_comment_url_ranges s in
    let outside off = not (is_in_exempt_range vcu off) in
    List.concat_map
      (fun (needle, replacement) ->
        let offsets =
          List.filter outside
            (Validators_l0_typo.find_all_non_overlapping s needle)
        in
        List.map
          (fun off ->
            Cst_edit.replace ~start_offset:off
              ~end_offset:(off + String.length needle)
              replacement)
          offsets)
      pairs
  in
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
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-029" ~severity:Warning
             ~message:"Use of eqnarray* instead of align*" ~count:!cnt)
      else
        Some
          (mk_result_with_fix ~id:"MATH-029" ~severity:Warning
             ~message:"Use of eqnarray* instead of align*" ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-030" ~severity:Info
           ~message:{|Overuse of \displaystyle in inline math|} ~count:!cnt)
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
    if !cnt > 0 then (
      (* Bucket-C candidate (v27.1.24): insert a medium space `\;` before a
         `\text{` that abuts a letter/digit/brace in math (`x\text{if}` ->
         `x\;\text{if}`). The needle is `<char>\text{`; `\;` is inserted just
         before the backslash. Gated to real math ranges. *)
      let ranges = find_math_ranges s in
      let cands = ref [] in
      let i = ref 0 in
      (try
         while true do
           let mr, pos = Re_compat.search_forward re s !i in
           let e = Re_compat.match_end mr in
           if is_in_math_range ranges pos then
             cands :=
               {
                 c_edits = [ Cst_edit.insert ~at:(pos + 1) "\\;" ];
                 c_label = "Insert a medium space \\; before \\text";
               }
               :: !cands;
           i := e
         done
       with Not_found -> ());
      let candidates = candidates_drop_vcu_exempt s (List.rev !cands) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-031" ~severity:Info
             ~message:{|Operator spacing error: missing \; before \text|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-031" ~severity:Info
             ~message:{|Operator spacing error: missing \; before \text|}
             ~count:!cnt ~candidates))
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
        (mk_result ~id:"MATH-033" ~severity:Info
           ~message:{|Use of \pm where ± symbol required in text|} ~count:cnt)
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
    if !cnt > 0 then (
      (* Bucket-C candidate (v27.1.24): insert a thin space `\,` before the
         differential `d` in an integral (`\int f(x)dx` -> `\int f(x)\,dx`). If
         the byte before `d` is a space, that space is REPLACED by `\,` so the
         result is tight (`f dx` -> `f\,dx`); otherwise `\,` is inserted.
         Collected over the ORIGINAL source, gated to math ranges that contain
         an integral, mirroring the diagnostic predicate exactly. `\,` is a
         control SYMBOL, so it never glues onto the following letter `d`. *)
      let ranges = find_math_ranges s in
      let int_ranges =
        List.filter
          (fun (a, b) -> count_substring (String.sub s a (b - a)) "\\int" > 0)
          ranges
      in
      let in_int_math off =
        List.exists (fun (a, b) -> off >= a && off < b) int_ranges
      in
      let n = String.length s in
      let cands = ref [] in
      let i = ref 0 in
      while !i < n - 1 do
        (if
           s.[!i] = 'd'
           && String.contains diff_vars s.[!i + 1]
           && in_int_math !i
         then
           let after_ok =
             !i + 2 >= n
             ||
             let c = s.[!i + 2] in
             not ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'))
           in
           let has_thin_space =
             !i >= 2 && s.[!i - 2] = '\\' && s.[!i - 1] = ','
           in
           let has_mathrm = !i >= 8 && String.sub s (!i - 8) 8 = "\\mathrm{" in
           let prev_ok =
             !i > 0
             &&
             let c = s.[!i - 1] in
             (c >= 'A' && c <= 'Z')
             || (c >= 'a' && c <= 'z')
             || (c >= '0' && c <= '9')
             || c = ')'
             || c = '}'
             || c = ' '
           in
           if after_ok && (not has_thin_space) && (not has_mathrm) && prev_ok
           then
             let start_off = if s.[!i - 1] = ' ' then !i - 1 else !i in
             cands :=
               {
                 c_edits =
                   [
                     Cst_edit.make ~start_offset:start_off ~end_offset:!i
                       ~replacement:"\\,";
                   ];
                 c_label = "Insert a thin space \\, before the differential";
               }
               :: !cands);
        incr i
      done;
      let candidates = candidates_drop_vcu_exempt s (List.rev !cands) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-034" ~severity:Info
             ~message:{|Spacing before differential in integral missing \,|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-034" ~severity:Info
             ~message:{|Spacing before differential in integral missing \,|}
             ~count:!cnt ~candidates))
    else None
  in
  { id = "MATH-034"; run; languages = [] }

(* MATH-035: Multiple subscripts stacked vertically without braces — a_{i}_{j}
   pattern instead of a_{i,j} *)
let l1_math_035_rule : rule =
  let re = Re_compat.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)_|} in
  (* Fix regex also captures the trailing subscript token so `_A_B` is
     bounded. *)
  let re_fix =
    Re_compat.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let strip_braces g =
    let n = String.length g in
    if n >= 2 && g.[0] = '{' && g.[n - 1] = '}' then String.sub g 1 (n - 2)
    else g
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      (* Bucket-C candidate (v27.1.22): combine stacked subscripts `a_{i}_{j}`
         -> `a_{i,j}` when both tokens are cleanly bounded. Intent-dependent
         (author may have meant nesting — see MATH-016), so review only. *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re_fix s i)
          with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let a = strip_braces (Re_compat.matched_group mr 1 s) in
            let bb = strip_braces (Re_compat.matched_group mr 2 s) in
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:("_{" ^ a ^ "," ^ bb ^ "}");
                    ];
                  c_label = "Combine stacked subscripts into _{i,j}";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-035" ~severity:Warning
             ~message:"Multiple subscripts stacked vertically without braces"
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-035" ~severity:Warning
             ~message:"Multiple subscripts stacked vertically without braces"
             ~count:!cnt ~candidates)
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
      (* Bucket-C candidate (v27.1.22): unwrap `\mathrm{x}` -> `x` for a single
         letter — render-identical, but roman on one letter can be intentional
         (a unit/constant), so surface for review rather than auto-apply. *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re s i) with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let letter = String.make 1 s.[e - 2] in
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:letter;
                    ];
                  c_label = "Drop superfluous \\mathrm around a single letter";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-036" ~severity:Info
             ~message:{|Superfluous \mathrm{} around single letter|} ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-036" ~severity:Info
             ~message:{|Superfluous \mathrm{} around single letter|} ~count:!cnt
             ~candidates)
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
        (mk_result ~id:"MATH-037" ~severity:Info
           ~message:"xfrac package fraction used outside text mode" ~count:!cnt)
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
        (mk_result ~id:"MATH-038" ~severity:Warning
           ~message:{|Nested \frac three levels deep|} ~count:!cnt)
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
        (mk_result ~id:"MATH-039" ~severity:Warning
           ~message:{|Stacked relational operators without \atop|} ~count:!cnt)
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
        (mk_result ~id:"MATH-040" ~severity:Info
           ~message:{|Ellipsis \ldots used between vertical alignment|}
           ~count:!cnt)
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
        (mk_result ~id:"MATH-041" ~severity:Info
           ~message:{|Integral limits written inline; use \displaystyle \int|}
           ~count:!cnt)
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
    if !cnt > 0 then (
      (* Bucket-C candidate (v27.1.24): insert a thin space `\,` between a
         number and the following unit macro in math (`5\mathrm{kg}` ->
         `5\,\mathrm{kg}`). The needle is `<digit>\mathrm{` / `<digit>\text{` /
         `<digit>\textrm{`; the thin space is inserted right after the digit
         (before the backslash), so it cannot glue onto a control word. Gated to
         real math ranges. *)
      let ranges = find_math_ranges s in
      let cands = ref [] in
      let i = ref 0 in
      (try
         while true do
           let mr, pos = Re_compat.search_forward re s !i in
           let e = Re_compat.match_end mr in
           if is_in_math_range ranges pos then
             cands :=
               {
                 c_edits = [ Cst_edit.insert ~at:(pos + 1) "\\," ];
                 c_label = "Insert a thin space \\, between the number and unit";
               }
               :: !cands;
           i := e
         done
       with Not_found -> ());
      let candidates = candidates_drop_vcu_exempt s (List.rev !cands) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-042" ~severity:Info
             ~message:{|Missing \, between numbers and units in math|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-042" ~severity:Info
             ~message:{|Missing \, between numbers and units in math|}
             ~count:!cnt ~candidates))
    else None
  in
  { id = "MATH-042"; run; languages = [] }

(* MATH-043: Use of \text instead of \operatorname for function names in math —
   \text{Var} should be \operatorname{Var} *)
let l1_math_043_rule : rule =
  let re = Re_compat.regexp {|\\text{[A-Z][a-z]+}|} in
  (* Fix offsets are computed from the ORIGINAL source `s` (never from the
     length-changing `extract_math_segments` copy — the STYLE-033 bug), by
     re-running the SAME non-overlapping regex scan the counter uses and keeping
     only matches whose `\text` byte lands inside a real math range. The count
     itself is untouched: it is still tallied via `extract_math_segments` /
     `count_re_matches` below, so the diagnostic (and the differential) is
     byte-identical. *)
  let fix_offsets s =
    let math = find_math_ranges s in
    let acc = ref [] in
    let i = ref 0 in
    (try
       while true do
         let mr, _ = Re_compat.search_forward re s !i in
         let b = Re_compat.match_beginning mr in
         let e = Re_compat.match_end mr in
         if is_in_math_range math b then acc := b :: !acc;
         i := e
       done
     with Not_found -> ());
    List.rev !acc
  in
  let mk_fix_edits s =
    List.map
      (fun off ->
        (* Replace only the 5-byte command name `\text` (5C 74 65 78 74) with
           the 13-byte `\operatorname`, leaving the `{Xxx}` argument intact.
           Idempotent + convergent: `\operatorname` does not contain the
           substring `\text`, so the regex `\\text{[A-Z][a-z]+}` cannot re-fire
           at a rewritten site, and no producer rewrites `\operatorname` back to
           `\text`. *)
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 5)
          "\\operatorname")
      (fix_offsets s)
  in
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
      let fix = mk_fix_edits s in
      Some
        (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-043" ~severity:Warning
           ~message:{|Use of \text instead of \operatorname for function|}
           ~count:!cnt ~fix)
    else None
  in
  { id = "MATH-043"; run; languages = [] }

(* MATH-044: Binary relation typed as text char — e.g. < for \le, = for \equiv,
   etc., when text < > appear in math outside of delimiters.

   Fix producer (catalog fix: replace_with_symbol): inside math regions, the
   ASCII relations `<=` / `>=` are replaced by their LaTeX symbols `\le ` / `\ge
   ` (each 2 bytes → 4 bytes incl. a trailing space). The trailing space is
   required so the control word does not glue to a following letter (`a<=b`
   would otherwise become the undefined `\leb`); inside math spaces are ignored
   by TeX, so the rendering is unaffected and the edit is idempotent (`<=` no
   longer present after the replace).

   The DIAGNOSE-ONLY count is untouched (same per-segment regex). The fix
   offsets are computed independently over the ORIGINAL string via
   `find_all_non_overlapping`, filtered to math ranges (`find_math_ranges`) and
   to a non-backslash preceding byte (mirroring the regex's `[^\\]` guard), and
   any edit inside verbatim/comment/url (`find_verbatim_comment_url_ranges`) is
   dropped while in-math edits are kept. *)
let l1_math_044_rule : rule =
  let re = Re_compat.regexp {|[^\\]<=\|[^\\]>=|} in
  let repl_of needle = if needle = "<=" then "\\le " else "\\ge " in
  let fix_offsets s =
    let math = find_math_ranges s in
    let vcu = find_verbatim_comment_url_ranges s in
    let keep off =
      off > 0
      && s.[off - 1] <> '\\'
      && is_in_math_range math off
      && not (is_in_math_range vcu off)
    in
    let for_needle needle =
      List.filter_map
        (fun off -> if keep off then Some (off, needle) else None)
        (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    for_needle "<=" @ for_needle ">="
  in
  let mk_fix_edits s =
    List.map
      (fun (off, needle) ->
        Cst_edit.replace ~start_offset:off
          ~end_offset:(off + String.length needle)
          (repl_of needle))
      (fix_offsets s)
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-044" ~severity:Warning
             ~message:{|Binary relation typed as text char (e.g. < for \le)|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_fix ~id:"MATH-044" ~severity:Warning
             ~message:{|Binary relation typed as text char (e.g. < for \le)|}
             ~count:!cnt ~fix)
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
  (* A control word `\<Capital><letters...>` — the trailing `[A-Za-z]*` enforces
     a proper control-word boundary so `\Pi` never matches inside `\Pion`. *)
  let re_cw = Re_compat.regexp {|\\[A-Z][A-Za-z]*|} in
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
      (* Bucket-C candidate (v27.1.22): wrap each BARE capital Greek in
         `\mathrm{}` to match the document's upright convention. Skips macros
         already wrapped as `\mathrm{\Gamma}`. Style-dependent, so review. *)
      let len = String.length s in
      let ranges = find_math_ranges s in
      let already_wrapped b e =
        b >= 8 && String.sub s (b - 8) 8 = "\\mathrm{" && e < len && s.[e] = '}'
      in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re_cw s i) with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let macro = String.sub s b (e - b) in
            let acc =
              if
                List.mem macro greek_capitals
                && is_in_math_range ranges b
                && not (already_wrapped b e)
              then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:("\\mathrm{" ^ macro ^ "}");
                    ];
                  c_label = "Wrap capital Greek in \\mathrm to match upright";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-045" ~severity:Info
             ~message:{|Math italic capital Greek without \mathrm|}
             ~count:!bare_cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-045" ~severity:Info
             ~message:{|Math italic capital Greek without \mathrm|}
             ~count:!bare_cnt ~candidates)
    else None
  in
  { id = "MATH-045"; run; languages = [] }

(* MATH-046: Ellipsis \ldots on relation axis — prefer \cdots between commas, +
   etc.

   Fix producer (v27.1.10): for each counted `,[ ]*\ldots[ ]*,` occurrence,
   replace the 6-byte `\ldots` with the 6-byte `\cdots`. Offsets are computed on
   the ORIGINAL source `s` (never on a length-changing transform — the STYLE-033
   corruption bug), re-scanning with the SAME non-overlapping regex the count
   uses (search restarts at match_end) and gated to `find_math_ranges s` so the
   fix set never exceeds the counted set. `\ldots`/`\cdots` are pure ASCII, so
   the 6→6 replace never splits a multibyte sequence. Idempotent: after the
   rewrite the needle is `\cdots`, which the regex no longer matches. Count is
   left byte-identical (guarantees release differential 0-diff). *)
let l1_math_046_rule : rule =
  let re = Re_compat.regexp {|,[ ]*\\ldots[ ]*,|} in
  let ldots = "\\ldots" in
  let matches_at s pos sub =
    let n = String.length sub in
    pos + n <= String.length s && String.sub s pos n = sub
  in
  (* Absolute offsets of every `\ldots` that begins a counted match, filtered to
     math ranges on the original source. *)
  let fix_offsets s =
    let math = find_math_ranges s in
    let acc = ref [] in
    let i = ref 0 in
    (try
       while true do
         let mr, _ = Re_compat.search_forward re s !i in
         let mstart = Re_compat.match_beginning mr in
         let mend = Re_compat.match_end mr in
         (* Skip the leading comma + optional spaces to reach `\ldots`. *)
         let p = ref (mstart + 1) in
         while !p < String.length s && s.[!p] = ' ' do
           incr p
         done;
         if matches_at s !p ldots && is_in_math_range math !p then
           acc := !p :: !acc;
         i := mend
       done
     with Not_found -> ());
    List.rev !acc
  in
  let mk_fix_edits s =
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off
          ~end_offset:(off + String.length ldots)
          "\\cdots")
      (fix_offsets s)
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-046" ~severity:Info
             ~message:{|Ellipsis \ldots used on relation axis; prefer \cdots|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-046" ~severity:Info
             ~message:{|Ellipsis \ldots used on relation axis; prefer \cdots|}
             ~count:!cnt ~fix)
    else None
  in
  { id = "MATH-046"; run; languages = [] }

(* MATH-047: Double superscript without braces — a^b^c is a TeX error *)
let l1_math_047_rule : rule =
  let re = Re_compat.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)\^|} in
  (* Fix regex also captures the trailing superscript token so `^A^B` is
     bounded. *)
  let re_fix =
    Re_compat.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)\^\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let strip_braces g =
    let n = String.length g in
    if n >= 2 && g.[0] = '{' && g.[n - 1] = '}' then String.sub g 1 (n - 2)
    else g
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      (* Bucket-C candidate (v27.1.22): brace double superscript `a^b^c` ->
         `a^{b^{c}}` when both tokens are cleanly bounded (this is otherwise a
         TeX error). Review only. *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re_fix s i)
          with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let x = strip_braces (Re_compat.matched_group mr 1 s) in
            let y = strip_braces (Re_compat.matched_group mr 2 s) in
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:("^{" ^ x ^ "^{" ^ y ^ "}}");
                    ];
                  c_label = "Brace double superscript as ^{...}";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-047" ~severity:Error
             ~message:"Double superscript without braces a^b^c" ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-047" ~severity:Error
             ~message:"Double superscript without braces a^b^c" ~count:!cnt
             ~candidates)
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
      (* Bucket-C candidate (v27.1.22): unwrap `\mathbf{<digits>}` -> `<digits>`
         (upright digits are already the default; boldface may be
         intentional). *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re s i) with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let digits = String.sub s (b + 8) (e - b - 9) in
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:digits;
                    ];
                  c_label = "Drop \\mathbf boldface on digits";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-048" ~severity:Info
             ~message:{|Boldface digits via \mathbf in math – avoid|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-048" ~severity:Info
             ~message:{|Boldface digits via \mathbf in math – avoid|}
             ~count:!cnt ~candidates)
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
      (* Bucket-C candidate (v27.1.41): insert a plain space at a tight
         `\times` boundary. Render-identical — TeX ignores source spaces in
         math and the binary-operator spacing comes from `\times` itself — but
         a space also disambiguates `\times`+letter, so surfaced for review
         rather than auto-applied. Offsets scanned on the ORIGINAL source, math
         gated by [find_math_ranges]/[is_in_math_range], vcu-exempt. *)
      let ranges = find_math_ranges s in
      let is_alnum c =
        (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
      in
      let n = String.length s in
      let cand_of off =
        if not (is_in_math_range ranges off) then []
        else
          let mk at =
            {
              c_edits = [ Cst_edit.insert ~at " " ];
              c_label = "Insert a space around \\times";
            }
          in
          let before =
            if off >= 1 then
              let c = s.[off - 1] in
              is_alnum c || c = '}'
            else false
          in
          let after =
            let a = off + 6 in
            if a < n then
              let c = s.[a] in
              is_alnum c || c = '{'
            else false
          in
          (if before then [ mk off ] else [])
          @ if after then [ mk (off + 6) ] else []
      in
      let raw =
        List.concat_map cand_of
          (Validators_l0_typo.find_all_non_overlapping s "\\times")
      in
      let candidates = candidates_drop_vcu_exempt s raw in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-049" ~severity:Info
             ~message:{|Spacing around \times missing|} ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-049" ~severity:Info
             ~message:{|Spacing around \times missing|} ~count:!cnt ~candidates)
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
      (* Bucket-C candidate (v27.1.22): `\hat{multi}` -> `\widehat{multi}` (wide
         accent for multi-letter args). Render-affecting (wider hat), so
         review. *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re s i) with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            (* replace the `\hat` prefix (4 bytes) with `\widehat`, keep
               `{...}` *)
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:(b + 4)
                        ~replacement:"\\widehat";
                    ];
                  c_label = "Use \\widehat for a multi-letter accent";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-050" ~severity:Warning
             ~message:{|Circumflex accent ^\hat on multi‑letter|} ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-050" ~severity:Warning
             ~message:{|Circumflex accent ^\hat on multi‑letter|} ~count:!cnt
             ~candidates)
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
        (mk_result ~id:"MATH-051" ~severity:Warning
           ~message:{|Radical \sqrt nested two levels|} ~count:!cnt)
    else None
  in
  { id = "MATH-051"; run; languages = [] }

(* Bucket-C helper shared by MATH-052 and MATH-101: for every bare `\over`
   primitive inside a math range, build a CANDIDATE that rewrites the enclosing
   brace group `{ num \over den }` into `{\frac{num}{den}}`. Best-effort group
   bounding: when the enclosing `{...}` cannot be located within the math range
   the candidate degrades to LABEL-ONLY (empty edits). Every candidate's trigger
   offset is self-gated against verbatim / comment / url regions so a literal
   `\over` inside a code block yields no suggestion; genuine in-math `\over`
   candidates are kept. Candidates are the same for both rules, so the two
   diagnostics stay independent while sharing one suggestion. *)
let over_frac_candidates (s : string) : candidate_fix list =
  let vcu = find_verbatim_comment_url_ranges s in
  let ranges = find_math_ranges s in
  let n = String.length s in
  let label = {|Use \frac{...}{...} instead of \over|} in
  let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  (* parity of the backslash run ending at [idx-1]: an odd count means the byte
     at [idx] is escaped. *)
  let is_escaped idx =
    let rec count back acc =
      if back < 0 then acc
      else if s.[back] = '\\' then count (back - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let cands = ref [] in
  List.iter
    (fun (rs, re) ->
      let i = ref rs in
      while !i <= re - 5 do
        if
          s.[!i] = '\\'
          && !i + 4 < n
          && s.[!i + 1] = 'o'
          && s.[!i + 2] = 'v'
          && s.[!i + 3] = 'e'
          && s.[!i + 4] = 'r'
          && (not (is_escaped !i))
          && not (!i + 5 < n && is_letter s.[!i + 5])
        then (
          let over_start = !i in
          let over_end = !i + 5 in
          if not (is_in_math_range vcu over_start) then (
            (* scan backward for the enclosing unescaped '{' within [rs,re) *)
            let opener = ref (-1) in
            let depth = ref 0 in
            let j = ref (over_start - 1) in
            (try
               while !j >= rs do
                 (if not (is_escaped !j) then
                    match s.[!j] with
                    | '}' -> incr depth
                    | '{' ->
                        if !depth = 0 then (
                          opener := !j;
                          raise Exit)
                        else decr depth
                    | _ -> ());
                 decr j
               done
             with Exit -> ());
            (* scan forward for the enclosing unescaped '}' within [rs,re) *)
            let closer = ref (-1) in
            let depth2 = ref 0 in
            let k = ref over_end in
            (try
               while !k < re do
                 (if not (is_escaped !k) then
                    match s.[!k] with
                    | '{' -> incr depth2
                    | '}' ->
                        if !depth2 = 0 then (
                          closer := !k;
                          raise Exit)
                        else decr depth2
                    | _ -> ());
                 incr k
               done
             with Exit -> ());
            if !opener >= 0 && !closer >= 0 then
              let num =
                String.trim
                  (String.sub s (!opener + 1) (over_start - (!opener + 1)))
              in
              let den =
                String.trim (String.sub s over_end (!closer - over_end))
              in
              let repl = Printf.sprintf {|{\frac{%s}{%s}}|} num den in
              cands :=
                {
                  c_edits =
                    [
                      Cst_edit.replace ~start_offset:!opener
                        ~end_offset:(!closer + 1) repl;
                    ];
                  c_label = label;
                }
                :: !cands
            else cands := { c_edits = []; c_label = label } :: !cands);
          i := over_end)
        else incr i
      done)
    ranges;
  List.rev !cands

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
      let candidates = candidates_drop_vcu_exempt s (over_frac_candidates s) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-052" ~severity:Warning
             ~message:{|\over brace used; prefer \frac|} ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-052" ~severity:Warning
             ~message:{|\over brace used; prefer \frac|} ~count:!cnt ~candidates)
    else None
  in
  { id = "MATH-052"; run; languages = [] }

(* MATH-053: Space after \left( — spurious space inside math.

   v27.0.66: math-aware fix producer that deletes the single space byte after
   each `\left(` occurrence inside math. Single-needle match for `\left( ` (7
   bytes: `\left(` + space) inside `find_math_ranges`; the fix emits a 1-byte
   delete at offset+6 (the space position). Same shape family as MATH-082 /
   MATH-106 / MATH-108 / MATH-015 / MATH-078 / MATH-010 / MATH-097 —
   math-mode-only positive filter via `find_math_ranges` + `is_in_math_range`.

   First MATH-family fix producer since v27.0.51 (14 cycles ago). Severity Info
   preserved. *)
let l1_math_053_rule : rule =
  let needle = "\\left( " in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    let space_off = String.length needle - 1 in
    List.map
      (fun off ->
        Cst_edit.delete ~start_offset:(off + space_off)
          ~end_offset:(off + space_off + 1))
      offsets
  in
  let run s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    let cnt = List.length offsets in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-053" ~severity:Info
             ~message:{|Space after \left( at line start|} ~count:cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-053" ~severity:Info
             ~message:{|Space after \left( at line start|} ~count:cnt ~fix)
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
        (mk_result ~id:"MATH-055" ~severity:Info
           ~message:{|Math font change \mathcal for single character only|}
           ~count:!cnt)
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
        (mk_result ~id:"MATH-057" ~severity:Error
           ~message:"Empty fraction numerator or denominator" ~count:!cnt)
    else None
  in
  { id = "MATH-057"; run; languages = [] }

(* MATH-058: Nested \text inside \text *)
let l1_math_058_rule : rule =
  let re = Re_compat.regexp {|\\text{[^}]*\\text{|} in
  (* Direct-nesting form `\text{\text{` (inner opens immediately) — the only
     shape that is safely unwrappable. *)
  let re_direct = Re_compat.regexp {|\\text{\\text{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      (* Bucket-C candidate (v27.1.22): unwrap redundant DIRECT nesting
         `\text{\text{..}}` -> `\text{..}` by deleting the inner `\text{` and
         its matching close brace. Only offered when the inner group's close
         brace is immediately followed by the outer close (i.e. the outer holds
         nothing but the inner \text). Review only. *)
      let len = String.length s in
      let ranges = find_math_ranges s in
      (* Return the offset of the brace that closes the group opened at
         [open_pos] (which must be '{'), honouring escaped braces; None if
         unbalanced. *)
      let matching_close open_pos =
        let j = ref (open_pos + 1) in
        let depth = ref 1 in
        let res = ref None in
        while !res = None && !j < len do
          if s.[!j] = '\\' then j := !j + 2
          else if s.[!j] = '{' then (
            incr depth;
            incr j)
          else if s.[!j] = '}' then (
            decr depth;
            if !depth = 0 then res := Some !j else incr j)
          else incr j
        done;
        !res
      in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re_direct s i)
          with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            (* outer `\text{` = [b,b+6); inner `\text{` = [b+6,b+12) *)
            let inner_open = b + 11 in
            let acc =
              match matching_close inner_open with
              | Some ic
                when is_in_math_range ranges b
                     && ic + 1 < len
                     && s.[ic + 1] = '}' ->
                  {
                    c_edits =
                      [
                        (* drop inner `\text{` *)
                        Cst_edit.make ~start_offset:(b + 6) ~end_offset:(b + 12)
                          ~replacement:"";
                        (* drop the inner group's close brace *)
                        Cst_edit.make ~start_offset:ic ~end_offset:(ic + 1)
                          ~replacement:"";
                      ];
                    c_label = "Unwrap redundant nested \\text";
                  }
                  :: acc
              | _ -> acc
            in
            collect (b + 12) acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-058" ~severity:Info
             ~message:"Nested \\text inside \\text" ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-058" ~severity:Info
             ~message:"Nested \\text inside \\text" ~count:!cnt ~candidates)
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
        (mk_result ~id:"MATH-065" ~severity:Info
           ~message:{|Manual spacing \hspace in math detected|} ~count:!cnt)
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
        (mk_result ~id:"MATH-066" ~severity:Info
           ~message:{|\phantom used; suggest \hphantom or \vphantom|}
           ~count:!cnt)
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
    if !cnt > 0 then (
      (* Bucket-C candidate (v27.1.24): add thin spaces `\,` on each side of a
         tight `\mid` (`a\mid b` -> `a\,\mid\,b`). Only real `\mid` control
         words are considered (the next byte must not be a letter, so
         `\middle`/`\midrule` are skipped) and only when at least one side is
         tight; a side that already has a space has that space REPLACED by `\,`
         (no doubling). Two-edit candidate, gated to real math ranges. *)
      let ranges = find_math_ranges s in
      let n = String.length s in
      let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
      let is_ws c = c = ' ' || c = '\t' || c = '\n' in
      let cands = ref [] in
      let i = ref 0 in
      while !i + 4 <= n do
        if
          String.sub s !i 4 = "\\mid"
          && (!i = 0 || s.[!i - 1] <> '\\')
          && (!i + 4 >= n || not (is_letter s.[!i + 4]))
          && is_in_math_range ranges !i
        then (
          let mid_start = !i in
          let mid_end = !i + 4 in
          let tight_before = mid_start > 0 && not (is_ws s.[mid_start - 1]) in
          let tight_after = mid_end < n && not (is_ws s.[mid_end]) in
          (if tight_before || tight_after then
             let left_edit =
               if mid_start > 0 && s.[mid_start - 1] = ' ' then
                 Cst_edit.make ~start_offset:(mid_start - 1)
                   ~end_offset:mid_start ~replacement:"\\,"
               else Cst_edit.insert ~at:mid_start "\\,"
             in
             let right_edit =
               if mid_end < n && s.[mid_end] = ' ' then
                 Cst_edit.make ~start_offset:mid_end ~end_offset:(mid_end + 1)
                   ~replacement:"\\,"
               else Cst_edit.insert ~at:mid_end "\\,"
             in
             cands :=
               {
                 c_edits = [ left_edit; right_edit ];
                 c_label = "Add thin spaces \\, around \\mid";
               }
               :: !cands);
          i := mid_end)
        else incr i
      done;
      let candidates = candidates_drop_vcu_exempt s (List.rev !cands) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-068" ~severity:Info
             ~message:"Spacing around \\mid missing" ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-068" ~severity:Info
             ~message:"Spacing around \\mid missing" ~count:!cnt ~candidates))
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
        (mk_result ~id:"MATH-069" ~severity:Info
           ~message:"Bold sans‑serif math font used" ~count:!cnt)
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
        (mk_result ~id:"MATH-071" ~severity:Info
           ~message:{|Overuse of \cancel in equations|} ~count:!cnt)
    else None
  in
  { id = "MATH-071"; run; languages = [] }

(* MATH-078: Long arrow typed as --> instead of \longrightarrow.

   v27.0.49: math-aware fix producer that replaces each `-->` (3 ASCII bytes)
   with `\longrightarrow` (15 ASCII bytes) INSIDE math regions. The canonical
   LaTeX long-arrow macro renders with correct typographic spacing; the
   hand-typed `-->` renders as a minus + minus + greater- than sign with no
   math-mode adjustment. Same shape as MATH-082 / MATH-106 / MATH-108 / MATH-015
   (math-mode-only positive filter). Severity Info preserved. *)
let l1_math_078_rule : rule =
  let needle = "-->" in
  let replacement = "\\longrightarrow" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off
          ~end_offset:(off + String.length needle)
          (control_word_repl s (off + String.length needle) replacement))
      offsets
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg needle) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-078" ~severity:Info
             ~message:{|Long arrow typed as --> instead of \longrightarrow|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-078" ~severity:Info
             ~message:{|Long arrow typed as --> instead of \longrightarrow|}
             ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-079" ~severity:Info
           ~message:{|\displaystyle inside display math – redundant|}
           ~count:!cnt)
    else None
  in
  { id = "MATH-079"; run; languages = [] }

(* MATH-082: Negative thin space \! misused twice consecutively.

   v27.0.46: math-aware fix producer that collapses each `\!\!` (4 bytes) to a
   single `\!` (2 bytes) inside math regions. Two consecutive negative thin
   spaces compose to `-2/6 em ≈ -1/3 em`, which a careful typesetter
   occasionally wants, but it is overwhelmingly a typo — there is no standard
   LaTeX idiom that produces this exact byte sequence. Restricted to math via
   `find_math_ranges` + `is_in_math_range` (positive filter — `\!` is a
   math-mode-only macro), mirroring the v27.0.7 TYPO-005 / v27.0.44 TYPO-053
   shape with the math filter INVERTED.

   Count semantic preserved (uses `extract_math_segments` per the pre-v27.0.46
   implementation); fix uses `find_math_ranges` for offsets in the original
   source. Documented TYPO-002/003 divergence pattern. Severity Warning
   preserved. *)
let l1_math_082_rule : rule =
  let needle = "\\!\\!" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 4) "\\!")
      offsets
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg needle) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-082" ~severity:Warning
             ~message:{|Negative thin space \! misused twice consecutively|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-082" ~severity:Warning
             ~message:{|Negative thin space \! misused twice consecutively|}
             ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-085" ~severity:Info
           ~message:{|Use of \eqcirc – rarely acceptable|} ~count:!cnt)
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
        (mk_result ~id:"MATH-094" ~severity:Info
           ~message:{|Manual \kern in math detected – typographic smell|}
           ~count:!cnt)
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
        (mk_result ~id:"MATH-105" ~severity:Info
           ~message:{|\textstyle used inside display math — redundant|}
           ~count:!cnt)
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
        (mk_result ~id:"MATH-056" ~severity:Info
           ~message:"\\operatorname duplicated for same function" ~count:!cnt)
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
      (* Bucket-C candidate (v27.1.22): `\bar{a+b}` (a short bar over a whole
         group) -> `\overline{a+b}` (a proper wide bar). Render-affecting, so
         review. The `\bar` prefix (4 bytes) is swapped, keeping `{...}`. *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re s i) with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:(b + 4)
                        ~replacement:"\\overline";
                    ];
                  c_label = "Use \\overline for a bar over a group expression";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-059" ~severity:Warning
             ~message:{|Math accent \bar on group expression needs braces|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-059" ~severity:Warning
             ~message:{|Math accent \bar on group expression needs braces|}
             ~count:!cnt ~candidates)
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
    if !cnt > 0 then (
      (* Bucket-C candidate (v27.1.24): same upright-differential rewrite as
         MATH-013 — replace the italic `d` before x/y/z/t with `\mathrm{d}`. The
         needle `\int[^$]*[^\\]d[xyzt ]` ends in `d[xyzt ]`, so the `d` byte
         sits at `match_end - 2`; that single byte is replaced, gated to math
         ranges. *)
      let ranges = find_math_ranges s in
      let cands = ref [] in
      let i = ref 0 in
      (try
         while true do
           let mr, _pos = Re_compat.search_forward re s !i in
           let e = Re_compat.match_end mr in
           let d_off = e - 2 in
           if d_off >= 0 && s.[d_off] = 'd' && is_in_math_range ranges d_off
           then
             cands :=
               {
                 c_edits =
                   [
                     Cst_edit.make ~start_offset:d_off ~end_offset:(d_off + 1)
                       ~replacement:"\\mathrm{d}";
                   ];
                 c_label = "Typeset the differential d upright with \\mathrm{d}";
               }
               :: !cands;
           i := e
         done
       with Not_found -> ());
      let candidates = candidates_drop_vcu_exempt s (List.rev !cands) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-060" ~severity:Info
             ~message:"Differential d typeset italic" ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-060" ~severity:Info
             ~message:"Differential d typeset italic" ~count:!cnt ~candidates))
    else None
  in
  { id = "MATH-060"; run; languages = [] }

(* MATH-061: Log base missing braces \log_10x

   Fix producer (v27.1.11): wrap the unbraced multi-character subscript base of
   `\log` in braces — `\log_10x` -> `\log_{10}x`. Offsets are computed on the
   ORIGINAL source `s` (never a length-changing transform — the STYLE-033
   corruption bug), re-scanning with the SAME non-overlapping regex the count
   uses (search restarts at match_end), gated to `find_math_ranges s` so the fix
   set never exceeds the counted set. One pure-ASCII REPLACE per firing: `_` +
   maximal-digit-run -> `_{` + digits + `}` (e.g. `_10` -> `_{10}`). The replace
   spans whole ASCII bytes (`_` and the digits), so it can never split a
   multibyte UTF-8 sequence. A REPLACE (not two insertions) is deliberate: the
   neighbouring producer SCRIPT-001 also fixes this trigger — it rewrites the
   WHOLE alnum subscript run `_10x` -> `_{10x}` via a replace over `[_,
   after-x)`. With a replace over `[_, after-10)`, MATH-061 either (a) is
   byte-identical to SCRIPT-001 for a pure-digit base (`\log_100`) and dedups,
   or (b) overlaps SCRIPT-001's range for a digit+letter base (`\log_10x`) and
   the engine keeps exactly one — never both. Two boundary-touching INSERTIONS
   would instead escape overlap detection and leave a stray `}` (`\log_100` ->
   `\log_{100}}`). Idempotent + convergent: after the rewrite the `_` is
   followed by `{`, which the count regex (`\\log_[0-9]`) no longer matches, so
   a second --apply-fixes pass is a byte-identical no-op; neither MATH-061 nor
   SCRIPT-001 ever removes a brace, so the interaction is monotone and cannot
   oscillate. Count is left byte-identical (release differential 0-diff).
   vcu-exempt so a `$\log_10x$` written inside verbatim/comment/url is still
   counted but not rewritten. *)
let l1_math_061_rule : rule =
  let re = Re_compat.regexp {|\\log_[0-9][0-9a-zA-Z]|} in
  (* For every counted match, emit a single replace of `_` + the maximal
     ASCII-digit run that forms the base with `_{<digits>}`, filtered to math
     ranges on the original source. *)
  let fix_edits_for s =
    let math = find_math_ranges s in
    let len = String.length s in
    let acc = ref [] in
    let i = ref 0 in
    (try
       while true do
         let mr, _ = Re_compat.search_forward re s !i in
         let mstart = Re_compat.match_beginning mr in
         let mend = Re_compat.match_end mr in
         (* mstart points at the `\` of `\log`; the `_` is at mstart+4 and the
            first digit of the base at mstart+5. *)
         let us = mstart + 4 in
         let base_start = mstart + 5 in
         if is_in_math_range math mstart then (
           let e = ref base_start in
           while !e < len && s.[!e] >= '0' && s.[!e] <= '9' do
             incr e
           done;
           let digits = String.sub s base_start (!e - base_start) in
           acc :=
             Cst_edit.replace ~start_offset:us ~end_offset:!e
               ("_{" ^ digits ^ "}")
             :: !acc);
         i := mend
       done
     with Not_found -> ());
    List.rev !acc
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      let fix = fix_edits_for s in
      Some
        (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-061" ~severity:Warning
           ~message:{|Log base missing braces in \log_10x|} ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-067" ~severity:Warning
           ~message:"Stacked limits on non‑operator" ~count:!cnt)
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
        (mk_result ~id:"MATH-070" ~severity:Info
           ~message:{|Multiline subscripts lack \substack|} ~count:!cnt)
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
        (mk_result ~id:"MATH-073" ~severity:Warning
           ~message:{|xcolor macro \color used inside math|} ~count:!cnt)
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
        (mk_result ~id:"MATH-077" ~severity:Error
           ~message:"Alignment point & outside alignment environment"
           ~count:!cnt)
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
      (* Bucket-C candidate (v27.1.41): insert a `\!` (negative thin space)
         between a function letter and an immediately-following `(`, tightening
         the `f(x)` kerning. This nudges spacing (not render-identical), so it
         is a review candidate, never auto-applied. Restricted to the exact
         `letter(` shape (a subset of the diagnostic), excluding a letter that
         is the tail of a `\command`. Offsets on the ORIGINAL source, math
         gated, vcu-exempt. *)
      let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
      (* True iff the letter at [lp] is the tail of a `\cmd` (>=1 letters after
         a backslash), mirroring [is_part_of_cmd] but on absolute offsets. *)
      let letter_is_cmd_tail lp =
        let rec find_bs i =
          if i < 0 then false
          else if s.[i] = '\\' then lp - i >= 1
          else if is_letter s.[i] then find_bs (i - 1)
          else false
        in
        find_bs (lp - 1)
      in
      let ranges = find_math_ranges s in
      let cand_of off =
        (* off = index of `(`. *)
        if
          off >= 1 && s.[off] = '(' && is_letter s.[off - 1]
          && (not (letter_is_cmd_tail (off - 1)))
          && is_in_math_range ranges off
        then
          [
            {
              c_edits = [ Cst_edit.insert ~at:off "\\!" ];
              c_label = "Insert \\! before ( for function kerning";
            };
          ]
        else []
      in
      let raw =
        List.concat_map cand_of (Validators_l0_typo.find_all_non_overlapping s "(")
      in
      let candidates = candidates_drop_vcu_exempt s raw in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-081" ~severity:Info
             ~message:{|Improper kerning f(x) – suggest f\!\left(x\right)|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-081" ~severity:Info
             ~message:{|Improper kerning f(x) – suggest f\!\left(x\right)|}
             ~count:!cnt ~candidates)
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
        (mk_result ~id:"MATH-084" ~severity:Info
           ~message:{|Displaystyle \sum in inline math|} ~count:!cnt)
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
        (mk_result ~id:"MATH-086" ~severity:Warning
           ~message:{|Nested root \sqrt{\sqrt{…}} depth > 2|} ~count:!cnt)
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
        (mk_result ~id:"MATH-090" ~severity:Warning
           ~message:{|Nested \frac depth > 3 – suggest \dfrac + \smash|}
           ~count:!cnt)
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
        (mk_result ~id:"MATH-093" ~severity:Info
           ~message:{|Multi‑letter italic variable should be \mathit{}|}
           ~count:!cnt)
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
        (mk_result ~id:"MATH-098" ~severity:Info
           ~message:{|Too many \qquad (> 2) in single line|} ~count:!cnt)
    else None
  in
  { id = "MATH-098"; run; languages = [] }

(* Shared fix helper for MATH-072 / MATH-091 (v27.1.21): rewrite each in-math
   `\operatorname{NAME}` whose NAME is a predefined operator into the dedicated
   control word `\NAME`. Matches the ORIGINAL source at absolute offsets (gated
   by [find_math_ranges]); a trailing space is appended by [control_word_repl]
   when a letter follows, so `\operatorname{det}x` becomes `\det x`, never the
   undefined `\detx`. Render-identical (both forms typeset an upright operator
   with operator spacing). Idempotent: the output contains no `\operatorname{`.
   Callers pass their own operator list so each rule's diagnostic count is left
   intact; the fix set is a strict subset of the counted occurrences. *)
let operatorname_fix_edits (s : string) (known_ops : string list) :
    Cst_edit.t list =
  let ranges = find_math_ranges s in
  let needle = "\\operatorname{" in
  let nlen = String.length needle in
  List.filter_map
    (fun off ->
      if not (is_in_math_range ranges off) then None
      else
        let bstart = off + nlen in
        match
          try Some (String.index_from s bstart '}') with Not_found -> None
        with
        | Some bend when bend > bstart ->
            let name = String.sub s bstart (bend - bstart) in
            if List.mem name known_ops then
              Some
                (Cst_edit.replace ~start_offset:off ~end_offset:(bend + 1)
                   (control_word_repl s (bend + 1) ("\\" ^ name)))
            else None
        | _ -> None)
    (Validators_l0_typo.find_all_non_overlapping s needle)

(* MATH-072: \operatorname used for a predefined operator — \operatorname{X}
   where X is a predefined LaTeX function like \det, \lim, \sin etc.; the
   dedicated \X command should be used instead. (The rule deliberately fires on
   KNOWN operators — an UNKNOWN name like \operatorname{argmax} is the correct
   idiom and must NOT fire; an audit briefly misread the old "Unknown ..."
   message as the spec and inverted the guard — reverted.)

   Fix producer (v27.1.21): emits `\operatorname{NAME}` → `\NAME` via
   [operatorname_fix_edits]; vcu-exempt so a `$…$` written inside verbatim /
   comment / url is not rewritten. Count/severity/message preserved. *)
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
      let fix = operatorname_fix_edits s known_ops in
      let message =
        "Predefined operator wrapped in \\operatorname; use the dedicated \
         command"
      in
      if fix = [] then
        Some (mk_result ~id:"MATH-072" ~severity:Warning ~message ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-072" ~severity:Warning
             ~message ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-074" ~severity:Warning
           ~message:"TikZ node inside math without math mode set" ~count:!cnt)
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
      (* Bucket-C candidate (v27.1.22): unwrap `\mathbf{<digits>}` -> `<digits>`
         (upright digits are already the default; boldface may be
         intentional). *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re s i) with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            let digits = String.sub s (b + 8) (e - b - 9) in
            let acc =
              if is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      Cst_edit.make ~start_offset:b ~end_offset:e
                        ~replacement:digits;
                    ];
                  c_label = "Drop \\mathbf boldface on digits";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-087" ~severity:Info
             ~message:{|Maths uses fake bold via \mathbf on digits|} ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-087" ~severity:Info
             ~message:{|Maths uses fake bold via \mathbf on digits|} ~count:!cnt
             ~candidates)
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
      (* Bucket-C candidate (v27.1.41): insert a `\,` thin space on the tight
         side(s) of a bare `\partial`, mirroring the diagnostic's two alts
         (`[^ \t,\\]\partial` and `\partial[^ \t{\\]`). Spacing nudge, not
         render-identical, so a review candidate. Offsets on ORIGINAL source,
         math gated, vcu-exempt. *)
      let n = String.length s in
      let ranges = find_math_ranges s in
      let cand_of off =
        (* off = index of the backslash of `\partial`; spans [off, off+8). *)
        if not (is_in_math_range ranges off) then []
        else
          let before =
            if off >= 1 then
              match s.[off - 1] with
              | ' ' | '\t' | ',' | '\\' -> false
              | _ -> true
            else false
          in
          let after =
            let a = off + 8 in
            if a < n then
              match s.[a] with ' ' | '\t' | '{' | '\\' -> false | _ -> true
            else false
          in
          (if before then
             [
               {
                 c_edits = [ Cst_edit.insert ~at:off "\\," ];
                 c_label = "Insert \\, thin space before \\partial";
               };
             ]
           else [])
          @
          if after then
            [
              {
                c_edits = [ Cst_edit.insert ~at:(off + 8) "\\," ];
                c_label = "Insert \\, thin space after \\partial";
              };
            ]
          else []
      in
      let raw =
        List.concat_map cand_of
          (Validators_l0_typo.find_all_non_overlapping s "\\partial")
      in
      let candidates = candidates_drop_vcu_exempt s raw in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-088" ~severity:Info
             ~message:{|Bare \partial lacks thin‑space before/after|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-088" ~severity:Info
             ~message:{|Bare \partial lacks thin‑space before/after|}
             ~count:!cnt ~candidates)
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
      let fix = operatorname_fix_edits s known_ops in
      let message = {|\operatorname{det} used – predefined \det exists|} in
      if fix = [] then
        Some (mk_result ~id:"MATH-091" ~severity:Info ~message ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-091" ~severity:Info
             ~message ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-092" ~severity:Info
           ~message:"\\sum with explicit limits in inline math" ~count:!cnt)
    else None
  in
  { id = "MATH-092"; run; languages = [] }

(* MATH-095: Log base without braces — alias of MATH-061 logic

   Fix producer (v27.1.13): identical detector regex to MATH-061, so the fix is
   the SAME provably-safe rewrite — wrap the unbraced multi-character subscript
   base of `\log` in braces (`\log_10x` -> `\log_{10}x`). Offsets are computed
   on the ORIGINAL source `s` (never a length-changing transform — the STYLE-033
   corruption class), re-scanning with the SAME non-overlapping regex the count
   uses (search restarts at match_end), gated to `find_math_ranges s` so the fix
   set never exceeds the counted set. One pure-ASCII REPLACE per firing: `_` +
   maximal-digit-run -> `_{` + digits + `}`. The replaced span is whole ASCII
   bytes, so it can never split a multibyte UTF-8 sequence. The emitted text
   ends in `}` (a brace, not a control word) so there is no letter-glue class.
   After the rewrite the `_` is followed by `{`, which the count regex
   (`\\log_[0-9]`) no longer matches, so a second --apply-fixes pass is a
   byte-identical no-op — idempotent + convergent. Count is left byte-identical
   (differential 0-diff). vcu-exempt so a `$\log_10x$` inside
   verbatim/comment/url is counted, not rewritten. *)
let l1_math_095_rule : rule =
  let re = Re_compat.regexp {|\\log_[0-9][0-9a-zA-Z]|} in
  let fix_edits_for s =
    let math = find_math_ranges s in
    let len = String.length s in
    let acc = ref [] in
    let i = ref 0 in
    (try
       while true do
         let mr, _ = Re_compat.search_forward re s !i in
         let mstart = Re_compat.match_beginning mr in
         let mend = Re_compat.match_end mr in
         let us = mstart + 4 in
         let base_start = mstart + 5 in
         if is_in_math_range math mstart then (
           let e = ref base_start in
           while !e < len && s.[!e] >= '0' && s.[!e] <= '9' do
             incr e
           done;
           let digits = String.sub s base_start (!e - base_start) in
           acc :=
             Cst_edit.replace ~start_offset:us ~end_offset:!e
               ("_{" ^ digits ^ "}")
             :: !acc);
         i := mend
       done
     with Not_found -> ());
    List.rev !acc
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      let fix = fix_edits_for s in
      Some
        (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-095" ~severity:Warning
           ~message:{|Log base typeset without braces (\log_10x)|} ~count:!cnt
           ~fix)
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
  let re_fix = Re_compat.regexp {|\\mathbf{\\[A-Za-z]+}|} in
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
      (* Bucket-C candidate (v27.1.22): `\mathbf{<greek>}` ->
         `\boldsymbol{<greek>}` — bold Greek should use \boldsymbol, but this is
         a stylistic call, so surface for review rather than auto-apply. Only
         the fixed greek_letters set qualifies. *)
      let ranges = find_math_ranges s in
      let rec collect i acc =
        match
          try Some (Re_compat.search_forward re_fix s i)
          with Not_found -> None
        with
        | None -> List.rev acc
        | Some (mr, _) ->
            let b = Re_compat.match_beginning mr in
            let e = Re_compat.match_end mr in
            (* inner control word between `\mathbf{` (8 bytes) and `}` *)
            let macro = String.sub s (b + 8) (e - (b + 8) - 1) in
            let acc =
              if List.mem macro greek_letters && is_in_math_range ranges b then
                {
                  c_edits =
                    [
                      (* swap the `\mathbf` prefix (7 bytes) -> `\boldsymbol`,
                         keep `{<greek>}` *)
                      Cst_edit.make ~start_offset:b ~end_offset:(b + 7)
                        ~replacement:"\\boldsymbol";
                    ];
                  c_label =
                    "Use \\boldsymbol for bold Greek instead of \\mathbf";
                }
                :: acc
              else acc
            in
            collect e acc
      in
      let candidates = candidates_drop_vcu_exempt s (collect 0 []) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-096" ~severity:Info
             ~message:{|Bold Greek via \mathbf – use \boldsymbol|} ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-096" ~severity:Info
             ~message:{|Bold Greek via \mathbf – use \boldsymbol|} ~count:!cnt
             ~candidates)
    else None
  in
  { id = "MATH-096"; run; languages = [] }

(* MATH-097: Arrow => typed instead of \implies.

   v27.0.51: math-aware fix producer that replaces each `=>` (2 bytes ASCII)
   with `\implies` (8 bytes ASCII) INSIDE math regions, subject to the same
   before-byte exclusion as the count regex `[^=!<>\\]=>` (skip when the
   preceding byte is in {=,!,<,>,\} to avoid corrupting `==>`, `<=>`, `\=>`,
   `>=>`, `!=>`). Same math-mode positive-filter shape as MATH-010/082/106/108.
   Count semantic preserved (uses pre-v27.0.51 padded-segment regex match).
   Severity Info preserved. *)
let l1_math_097_rule : rule =
  let re = Re_compat.regexp {|[^=!<>\\]=>|} in
  let find_arrow_offsets s =
    let n = String.length s in
    let rec scan i acc =
      if i + 1 >= n then List.rev acc
      else if s.[i] = '=' && s.[i + 1] = '>' then
        let bad_before =
          i > 0
          &&
          let c = s.[i - 1] in
          c = '=' || c = '!' || c = '<' || c = '>' || c = '\\'
        in
        if bad_before then scan (i + 1) acc else scan (i + 2) (i :: acc)
      else scan (i + 1) acc
    in
    scan 0 []
  in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets = List.filter inside (find_arrow_offsets s) in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 2)
          (control_word_repl s (off + 2) "\\implies"))
      offsets
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let padded = " " ^ seg in
        cnt := !cnt + count_re_matches re padded)
      math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-097" ~severity:Info
             ~message:{|Arrow '=>' typed instead of \implies|} ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-097" ~severity:Info
             ~message:{|Arrow '=>' typed instead of \implies|} ~count:!cnt ~fix)
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
        (mk_result ~id:"MATH-099" ~severity:Info
           ~message:{|Large operator (\bigcup) used inline|} ~count:!cnt)
    else None
  in
  { id = "MATH-099"; run; languages = [] }

(* MATH-101: Deprecated \over primitive used *)
let l1_math_101_rule : rule =
  (* Count occurrences of the control word "\over" only when it is the WHOLE
     control word, i.e. the character following "\over" is not a letter. This
     avoids false positives on \overline, \overbrace, \overrightarrow, \overset,
     \overparen, etc. *)
  let count_over_word seg =
    let needle = "\\over" in
    let nlen = String.length needle in
    let len = String.length seg in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i <= len - nlen do
      if String.sub seg !i nlen = needle then (
        let next_is_letter =
          !i + nlen < len
          &&
          let c = seg.[!i + nlen] in
          (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        in
        if not next_is_letter then incr cnt;
        i := !i + nlen)
      else incr i
    done;
    !cnt
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_over_word seg) math_segs;
    if !cnt > 0 then
      let candidates = candidates_drop_vcu_exempt s (over_frac_candidates s) in
      if candidates = [] then
        Some
          (mk_result ~id:"MATH-101" ~severity:Warning
             ~message:{|Deprecated \over primitive used; replace with \frac|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_candidates ~id:"MATH-101" ~severity:Warning
             ~message:{|Deprecated \over primitive used; replace with \frac|}
             ~count:!cnt ~candidates)
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
        (mk_result ~id:"MATH-104" ~severity:Info
           ~message:
             {|Paired delimiters repeated without \DeclarePairedDelimiter|}
           ~count:!cnt)
    else None
  in
  { id = "MATH-104"; run; languages = [] }

(* MATH-106: Misuse of \not= — prefer \neq.

   v27.0.47: math-aware fix producer that replaces each `\not=` (5 bytes) with
   the canonical `\neq` (4 bytes) INSIDE math regions. `\not=` is the
   TeX-primitive negation that overlays a slash on `=`; the semantically
   equivalent `\neq` is shorter, more readable, and universally preferred by
   LaTeX style guides (rules_v3.yaml default_severity=Info, fix=auto_replace).
   Mirrors the v27.0.46 MATH-082 shape exactly (math-mode-only single-needle
   replace via `find_math_ranges` + positive `is_in_math_range` filter). *)
let l1_math_106_rule : rule =
  let needle = "\\not=" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 5)
          (control_word_repl s (off + 5) "\\neq"))
      offsets
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg needle) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-106" ~severity:Info
             ~message:{|Misuse of \not=; prefer \neq|} ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-106" ~severity:Info
             ~message:{|Misuse of \not=; prefer \neq|} ~count:!cnt ~fix)
    else None
  in
  { id = "MATH-106"; run; languages = [] }

(* MATH-108: Middle dot U+00B7 in math — use \cdot.

   v27.0.47: math-aware fix producer that replaces each `·` (U+00B7, 2 bytes
   UTF-8 `\xc2\xb7`) with the canonical LaTeX `\cdot` (5 bytes ASCII) INSIDE
   math regions. In math, `·` is the Unicode middle dot which is meant to denote
   scalar product, but it renders with wrong spacing in math mode — `\cdot` is
   the correct macro. Same shape as MATH-106 (math-mode-only single-needle
   replace). Severity Info. *)
let l1_math_108_rule : rule =
  let needle = "\xc2\xb7" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let inside off = is_in_math_range math off in
    let offsets =
      List.filter inside (Validators_l0_typo.find_all_non_overlapping s needle)
    in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 2)
          (control_word_repl s (off + 2) "\\cdot"))
      offsets
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_substring seg needle) math_segs;
    if !cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"MATH-108" ~severity:Info
             ~message:{|Scalar product uses • (⋅) directly; require \cdot|}
             ~count:!cnt)
      else
        Some
          (mk_result_with_fix_vcu_exempt ~src:s ~id:"MATH-108" ~severity:Info
             ~message:{|Scalar product uses • (⋅) directly; require \cdot|}
             ~count:!cnt ~fix)
    else None
  in
  { id = "MATH-108"; run; languages = [] }
