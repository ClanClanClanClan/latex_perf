open Validators_common

(* Pilot L0 rules (IDs aligned with rules_v3.yaml). Info-level mapped to
   Warning. *)

let r_typo_001 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_char s '"' in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-001" ~severity:Error
           ~message:{|ASCII straight quotes (" … ") must be curly quotes|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-001"; run; languages = [] }

(** [find_all_non_overlapping s needle] — offsets of every occurrence of
    [needle] in [s], advancing by [|needle|] after each match (no overlaps).
    Used by TYPO-002/003 fix producers to build a non-overlapping replace-edit
    set. Differs from [count_substring] (which allows overlaps) — the fix-count
    may therefore be smaller than the rule-[count] on pathological input like
    "----" (count=3 with overlaps, 2 non-overlapping [--] matches). Acceptable:
    the fix-set is always applicable; the rule-[count] is a separate severity
    indicator. *)
let find_all_non_overlapping (s : string) (needle : string) : int list =
  let nlen = String.length needle in
  let slen = String.length s in
  if nlen = 0 || slen < nlen then []
  else
    let rec loop i acc =
      if i + nlen > slen then List.rev acc
      else if String.sub s i nlen = needle then loop (i + nlen) (i :: acc)
      else loop (i + 1) acc
    in
    loop 0 []

(** [find_consecutive_runs s c ~min_len] — list of [(start, stop)] half-open
    ranges where [s] has a maximal run of character [c] of length at least
    [min_len]. Used by TYPO-018 to collapse multi-space runs to a single space. *)
let find_consecutive_runs (s : string) (c : char) ~(min_len : int) :
    (int * int) list =
  let n = String.length s in
  let rec loop i acc =
    if i >= n then List.rev acc
    else if s.[i] = c then (
      let j = ref i in
      while !j < n && s.[!j] = c do
        incr j
      done;
      if !j - i >= min_len then loop !j ((i, !j) :: acc) else loop !j acc)
    else loop (i + 1) acc
  in
  loop 0 []

(** Build a list of single-needle replace edits for v26.3 fix producers. Each
    match becomes a non-overlapping [Cst_edit.replace] of [needle] →
    [replacement]. *)
let mk_replace_edits (s : string) (needle : string) (replacement : string) :
    Cst_edit.t list =
  let nlen = String.length needle in
  List.map
    (fun off ->
      Cst_edit.replace ~start_offset:off ~end_offset:(off + nlen) replacement)
    (find_all_non_overlapping s needle)

let r_typo_002 : rule =
  let message = "Double hyphen -- should be en‑dash –" in
  let mk_fix_edits s =
    List.map
      (fun off -> Cst_edit.replace ~start_offset:off ~end_offset:(off + 2) "–")
      (find_all_non_overlapping s "--")
  in
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.ch, b.ch) with
                | Some '-', Some '-' -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          let fix = mk_fix_edits s in
          if fix = [] then
            Some
              (mk_result ~id:"TYPO-002" ~severity:Warning ~message ~count:cnt)
          else
            Some
              (mk_result_with_fix ~id:"TYPO-002" ~severity:Warning ~message
                 ~count:cnt ~fix)
        else None
    | _ ->
        let cnt = count_substring s "--" in
        if cnt > 0 then
          let fix = mk_fix_edits s in
          if fix = [] then
            Some
              (mk_result ~id:"TYPO-002" ~severity:Warning ~message ~count:cnt)
          else
            Some
              (mk_result_with_fix ~id:"TYPO-002" ~severity:Warning ~message
                 ~count:cnt ~fix)
        else None
  in
  { id = "TYPO-002"; run; languages = [] }

let r_typo_003 : rule =
  let message = "Triple hyphen --- should be em‑dash —" in
  let mk_fix_edits s =
    List.map
      (fun off -> Cst_edit.replace ~start_offset:off ~end_offset:(off + 3) "—")
      (find_all_non_overlapping s "---")
  in
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: c' :: rest -> (
                match (a.ch, b.ch, c'.ch) with
                | Some '-', Some '-', Some '-' -> loop (c + 1) (b :: c' :: rest)
                | _ -> loop c (b :: c' :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          let fix = mk_fix_edits s in
          if fix = [] then
            Some
              (mk_result ~id:"TYPO-003" ~severity:Warning ~message ~count:cnt)
          else
            Some
              (mk_result_with_fix ~id:"TYPO-003" ~severity:Warning ~message
                 ~count:cnt ~fix)
        else None
    | _ ->
        let cnt = count_substring s "---" in
        if cnt > 0 then
          let fix = mk_fix_edits s in
          if fix = [] then
            Some
              (mk_result ~id:"TYPO-003" ~severity:Warning ~message ~count:cnt)
          else
            Some
              (mk_result_with_fix ~id:"TYPO-003" ~severity:Warning ~message
                 ~count:cnt ~fix)
        else None
  in
  { id = "TYPO-003"; run; languages = [] }

let r_typo_004 : rule =
  let run s =
    let cnt = count_substring s "``" + count_substring s "''" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-004" ~severity:Warning
           ~message:
             "TeX double back‑tick ``…'' not allowed; use opening curly quotes"
           ~count:cnt)
    else None
  in
  { id = "TYPO-004"; run; languages = [] }

let r_typo_005 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s "..." in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-005" ~severity:Warning
           ~message:"Ellipsis typed as three periods ...; use \\dots" ~count:cnt)
    else None
  in
  { id = "TYPO-005"; run; languages = [] }

let r_typo_006 : rule =
  let run s =
    let cnt = count_char s '\t' in
    if cnt > 0 then
      let n = String.length s in
      let edits = ref [] in
      for i = n - 1 downto 0 do
        if s.[i] = '\t' then
          edits := Cst_edit.replace ~start_offset:i ~end_offset:(i + 1) "    " :: !edits
      done;
      let fix = !edits in
      if fix = [] then
        Some (mk_result ~id:"TYPO-006" ~severity:Error ~message:"Tab character U+0009 forbidden" ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-006" ~severity:Error ~message:"Tab character U+0009 forbidden" ~count:cnt
             ~fix)
    else None
  in
  { id = "TYPO-006"; run; languages = [] }

let r_typo_007 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        (* Count Space tokens that directly precede a Newline token *)
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind) with
                | Space, Newline -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            (mk_result ~id:"TYPO-007" ~severity:Info
               ~message:"Trailing spaces at end of line" ~count:cnt)
        else None
    | _ ->
        let _total, matched =
          any_line_pred s (fun line ->
              let len = String.length line in
              len > 0
              &&
              let last = String.unsafe_get line (len - 1) in
              last = ' ' || last = '\t')
        in
        if matched > 0 then
          (* Build fix edits: for each line ending in trailing whitespace, emit
             a single delete spanning the whitespace run before the line break.
             Walk the source linearly; trailing-WS at file end (no newline) is
             handled by the final segment. *)
          let n = String.length s in
          let edits = ref [] in
          let line_start = ref 0 in
          let i = ref 0 in
          while !i < n do
            if s.[!i] = '\n' then (
              let line_end = !i in
              let trim_start = ref line_end in
              while
                !trim_start > !line_start
                && (let c = s.[!trim_start - 1] in
                    c = ' ' || c = '\t' || c = '\r')
              do
                decr trim_start
              done;
              if !trim_start < line_end then
                edits :=
                  Cst_edit.replace ~start_offset:!trim_start
                    ~end_offset:line_end ""
                  :: !edits;
              line_start := !i + 1;
              incr i)
            else incr i
          done;
          (* Final line without trailing newline. *)
          let trim_start = ref n in
          while
            !trim_start > !line_start
            && (let c = s.[!trim_start - 1] in
                c = ' ' || c = '\t' || c = '\r')
          do
            decr trim_start
          done;
          if !trim_start < n then
            edits :=
              Cst_edit.replace ~start_offset:!trim_start ~end_offset:n ""
              :: !edits;
          let fix = List.rev !edits in
          if fix = [] then
            Some
              (mk_result ~id:"TYPO-007" ~severity:Info
                 ~message:"Trailing spaces at end of line" ~count:matched)
          else
            Some
              (mk_result_with_fix ~id:"TYPO-007" ~severity:Info
                 ~message:"Trailing spaces at end of line" ~count:matched ~fix)
        else None
  in
  { id = "TYPO-007"; run; languages = [] }

let r_typo_008 : rule =
  (* Collapse runs of 3+ consecutive '\n' down to 2 by deleting the surplus. *)
  let mk_fix_edits s =
    let n = String.length s in
    let edits = ref [] in
    let i = ref 0 in
    while !i < n do
      if s.[!i] = '\n' then (
        let run_start = !i in
        while !i < n && s.[!i] = '\n' do
          incr i
        done;
        let run_len = !i - run_start in
        if run_len >= 3 then
          edits :=
            Cst_edit.replace ~start_offset:(run_start + 2)
              ~end_offset:(run_start + run_len) ""
            :: !edits)
      else incr i
    done;
    List.rev !edits
  in
  let emit cnt fix =
    if fix = [] then
      Some (mk_result ~id:"TYPO-008" ~severity:Info ~message:"Multiple consecutive blank lines (> 2) in source" ~count:cnt)
    else
      Some
        (mk_result_with_fix ~id:"TYPO-008" ~severity:Info ~message:"Multiple consecutive blank lines (> 2) in source" ~count:cnt
           ~fix)
  in
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let cnt =
          let n = String.length s in
          let rec loop i acc =
            if i + 2 >= n then acc
            else if
              String.unsafe_get s i = '\n'
              && String.unsafe_get s (i + 1) = '\n'
              && String.unsafe_get s (i + 2) = '\n'
            then loop (i + 3) (acc + 1)
            else loop (i + 1) acc
          in
          loop 0 0
        in
        if cnt > 0 then emit cnt (mk_fix_edits s) else None
    | _ ->
        let cnt = count_substring s "\n\n\n" in
        if cnt > 0 then emit cnt (mk_fix_edits s) else None
  in
  { id = "TYPO-008"; run; languages = [] }

let r_typo_009 : rule =
  let run s =
    let n = String.length s in
    let starts = if n > 0 && String.unsafe_get s 0 = '~' then 1 else 0 in
    let cnt = starts + count_substring s "\n~" in
    if cnt > 0 then
      let edits = ref [] in
      if starts = 1 then
        edits := Cst_edit.replace ~start_offset:0 ~end_offset:1 "" :: !edits;
      let i = ref 0 in
      while !i < n - 1 do
        if String.unsafe_get s !i = '\n' && String.unsafe_get s (!i + 1) = '~'
        then
          edits :=
            Cst_edit.replace ~start_offset:(!i + 1) ~end_offset:(!i + 2) ""
            :: !edits;
        incr i
      done;
      let fix = List.rev !edits in
      if fix = [] then
        Some (mk_result ~id:"TYPO-009" ~severity:Warning ~message:"Non‑breaking space ~ used incorrectly at line start" ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-009" ~severity:Warning ~message:"Non‑breaking space ~ used incorrectly at line start"
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-009"; run; languages = [] }

let r_typo_010 : rule =
  let run s =
    match Sys.getenv_opt "L0_TOKEN_AWARE" with
    | Some ("1" | "true" | "on") ->
        let open Tokenizer_lite in
        let toks = tokenize s in
        let is_punct = function
          | Some (',' | '.' | ';' | ':' | '?' | '!') -> true
          | _ -> false
        in
        let cnt =
          let rec loop c = function
            | [] -> c
            | a :: b :: rest -> (
                match (a.kind, b.kind, b.ch) with
                | Space, Symbol, ch when is_punct ch -> loop (c + 1) (b :: rest)
                | _ -> loop c (b :: rest))
            | _ -> c
          in
          loop 0 toks
        in
        if cnt > 0 then
          Some
            (mk_result ~id:"TYPO-010" ~severity:Info
               ~message:"Space before punctuation , . ; : ? !" ~count:cnt)
        else None
    | _ ->
        let combos = [ " ,"; " ."; " ;"; " :"; " ?"; " !" ] in
        let cnt =
          List.fold_left (fun acc sub -> acc + count_substring s sub) 0 combos
        in
        if cnt > 0 then
          Some
            (mk_result ~id:"TYPO-010" ~severity:Info
               ~message:"Space before punctuation , . ; : ? !" ~count:cnt)
        else None
  in
  { id = "TYPO-010"; run; languages = [] }

(* TYPO-011: Missing thin space before differential d in integrals *)
let r_typo_011 : rule =
  let re = Re_compat.regexp {|\\int[^}]*[^\\,]d[a-z]|} in
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
        (mk_result ~id:"TYPO-011" ~severity:Info
           ~message:
             {|Missing thin space (\,) before differential d in integrals|}
           ~count:!cnt)
    else None
  in
  { id = "TYPO-011"; run; languages = [] }

(* TYPO-012: Straight apostrophe used for minutes/feet *)
let r_typo_012 : rule =
  let re = Re_compat.regexp {|[0-9]'|} in
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
        (mk_result ~id:"TYPO-012" ~severity:Warning
           ~message:
             {|Straight apostrophe ' used for minutes/feet; use ^\prime or ′|}
           ~count:!cnt)
    else None
  in
  { id = "TYPO-012"; run; languages = [] }

(* TYPO-013: ASCII back-tick used as opening quote *)
let r_typo_013 : rule =
  let run s =
    let n = String.length s in
    let cnt = ref 0 in
    let edits = ref [] in
    for i = 0 to n - 1 do
      if s.[i] = '`' then
        (* Only flag single backtick, not `` (TeX opening quote) *)
        let is_double =
          (i + 1 < n && s.[i + 1] = '`') || (i > 0 && s.[i - 1] = '`')
        in
        if not is_double then (
          incr cnt;
          edits :=
            Cst_edit.replace ~start_offset:i ~end_offset:(i + 1) "\xe2\x80\x98"
            :: !edits)
    done;
    if !cnt > 0 then
      let fix = List.rev !edits in
      if fix = [] then
        Some (mk_result ~id:"TYPO-013" ~severity:Warning ~message:"ASCII back‑tick ` used as opening quote" ~count:!cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-013" ~severity:Warning ~message:"ASCII back‑tick ` used as opening quote"
             ~count:!cnt ~fix)
    else None
  in
  { id = "TYPO-013"; run; languages = [] }

(* TYPO-014: Space before percent sign — relocated from old TYPO-028 *)
let r_typo_014 : rule =
  let run s =
    let cnt = count_substring s " %" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-014" ~severity:Info
           ~message:{|Space before percent sign \%|} ~count:cnt)
    else None
  in
  { id = "TYPO-014"; run; languages = [] }

(* TYPO-015: Double \% in source; likely stray percent *)
let r_typo_015 : rule =
  let run s =
    let cnt = count_substring s "\\%\\%" in
    if cnt > 0 then
      let fix = mk_replace_edits s "\\%\\%" "\\%" in
      if fix = [] then
        Some (mk_result ~id:"TYPO-015" ~severity:Warning ~message:{|Double \% in source; likely stray percent|} ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-015" ~severity:Warning ~message:{|Double \% in source; likely stray percent|}
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-015"; run; languages = [] }

(* TYPO-016: Non-breaking space ~ missing before \cite / \ref *)
let r_typo_016 : rule =
  let re = Re_compat.regexp {| \\\(cite\|ref\)[^a-zA-Z]|} in
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
    let cnt = !cnt in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-016" ~severity:Info
           ~message:{|Non‑breaking space ~ missing before \cite / \ref|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-016"; run; languages = [] }

(* TYPO-017: TeX accent commands in text; prefer UTF-8 *)
let r_typo_017 : rule =
  let re = Re_compat.regexp {|\\['^`"~=.][{][a-zA-Z][}]|} in
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
        (mk_result ~id:"TYPO-017" ~severity:Info
           ~message:{|TeX accent commands (\'{e}) in text; prefer UTF‑8 é|}
           ~count:!cnt)
    else None
  in
  { id = "TYPO-017"; run; languages = [] }

(* TYPO-018: Multiple consecutive spaces — relocated from old TYPO-011. v26.3 §3
   item E: fix collapses each maximal run of >= 2 spaces to a single space. *)
let r_typo_018 : rule =
  let message = "Multiple consecutive spaces in text" in
  let run s =
    let cnt = count_substring s "  " in
    if cnt > 0 then
      let runs = find_consecutive_runs s ' ' ~min_len:2 in
      let fix =
        List.map
          (fun (start_offset, end_offset) ->
            Cst_edit.replace ~start_offset ~end_offset " ")
          runs
      in
      if fix = [] then
        Some (mk_result ~id:"TYPO-018" ~severity:Info ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-018" ~severity:Info ~message ~count:cnt
             ~fix)
    else None
  in
  { id = "TYPO-018"; run; languages = [] }

(* ── DEFERRED NLP STUBS ──────────────────────────────────────────────
   TYPO-019, -020, -030, -031 require NLP analysis and return None
   unconditionally. They are included in rules_pilot for API completeness but
   are excluded from rules_vpd_catalogue and have no VPD pattern entries or Coq
   soundness proofs. Status: blocked on NLP integration (tracked in
   WEEKLY_STATUS.md).
   ──────────────────────────────────────────────────────────────────── *)

(* TYPO-019: Comma splice detected — DEFERRED: requires NLP analysis *)
let r_typo_019 : rule =
  let run _s = None in
  { id = "TYPO-019"; run; languages = [] }

(* TYPO-020: Sentence without ending punctuation — DEFERRED: requires NLP *)
let r_typo_020 : rule =
  let run _s = None in
  { id = "TYPO-020"; run; languages = [] }

(* TYPO-021: Capital letter after ellipsis without space *)
let r_typo_021 : rule =
  let re = Re_compat.regexp {|\(\.\.\.\|…\)[A-Z]|} in
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
        (mk_result ~id:"TYPO-021" ~severity:Info
           ~message:"Capital letter after ellipsis without space" ~count:!cnt)
    else None
  in
  { id = "TYPO-021"; run; languages = [] }

(* TYPO-022: Space before closing punctuation — relocated from old TYPO-012.
   v26.3 §3 item E: fix replaces each [ )]/[ ]]/[ }] with the closer alone. *)
let r_typo_022 : rule =
  let message = "Space before closing punctuation ) ] }" in
  let run s =
    let combos = [ (" )", ")"); (" ]", "]"); (" }", "}") ] in
    let cnt =
      List.fold_left (fun acc (sub, _) -> acc + count_substring s sub) 0 combos
    in
    if cnt > 0 then
      let fix =
        List.concat_map
          (fun (needle, replacement) -> mk_replace_edits s needle replacement)
          combos
      in
      if fix = [] then
        Some (mk_result ~id:"TYPO-022" ~severity:Info ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-022" ~severity:Info ~message ~count:cnt
             ~fix)
    else None
  in
  { id = "TYPO-022"; run; languages = [] }

(* TYPO-023: ASCII ampersand & outside tabular env; use \& *)
let r_typo_023 : rule =
  let tabular_re =
    Re_compat.regexp
      {|\\begin{tabular\|\\begin{array\|\\begin{align\|\\begin{tabularx\|\\begin{longtable|}
  in
  let end_re =
    Re_compat.regexp
      {|\\end{tabular\|\\end{array\|\\end{align\|\\end{tabularx\|\\end{longtable|}
  in
  let _re_close_brace = Re_compat.regexp "}" in
  let run s =
    (* Strip out tabular/array/align environments *)
    let stripped = ref s in
    (try
       while true do
         let _mr, start_pos = Re_compat.search_forward tabular_re !stripped 0 in
         try
           let _mr, end_pos =
             Re_compat.search_forward end_re !stripped start_pos
           in
           let end_pos =
             try
               let _mr, _ =
                 Re_compat.search_forward _re_close_brace !stripped end_pos
               in
               Re_compat.match_end _mr
             with Not_found -> end_pos + 10
           in
           let before = String.sub !stripped 0 start_pos in
           let after =
             if end_pos < String.length !stripped then
               String.sub !stripped end_pos (String.length !stripped - end_pos)
             else ""
           in
           stripped := before ^ after
         with Not_found ->
           (* No matching end — strip from start to end of string *)
           stripped := String.sub !stripped 0 start_pos
       done
     with Not_found -> ());
    (* Count bare & (not \&) in stripped text *)
    let n = String.length !stripped in
    let cnt = ref 0 in
    for i = 0 to n - 1 do
      if !stripped.[i] = '&' && not (i > 0 && !stripped.[i - 1] = '\\') then
        incr cnt
    done;
    if !cnt > 0 then
      Some
        (mk_result ~id:"TYPO-023" ~severity:Error
           ~message:{|ASCII ampersand & outside tabular env; use \&|}
           ~count:!cnt)
    else None
  in
  { id = "TYPO-023"; run; languages = [] }

(* TYPO-024: Dangling dash at line end. v26.3 §3 item E: fix deletes the
   trailing dash run + any intervening whitespace before the newline. *)
let r_typo_024 : rule =
  let message = "Dangling dash at line end" in
  (* [\r] in the char class so CRLF lines also match — split_on_char '\n' leaves
     the [\r] at the end of each line. *)
  let re = Re_compat.regexp "-+[ \t\r]*$" in
  let run s =
    let lines = String.split_on_char '\n' s in
    let cnt =
      List.fold_left
        (fun acc line ->
          try
            let _mr, _ = Re_compat.search_forward re line 0 in
            acc + 1
          with Not_found -> acc)
        0 lines
    in
    if cnt > 0 then (
      (* Walk source to compute absolute offsets of each [-+[ \t]*] just before
         a newline (or end-of-source). Each match becomes a delete edit. *)
      let n = String.length s in
      let edits = ref [] in
      let i = ref 0 in
      while !i < n do
        (* Find next newline or EOS *)
        let line_start = !i in
        while !i < n && s.[!i] <> '\n' do
          incr i
        done;
        let line_end_with_terminator = !i in
        (* Step backward past a [\r] before the [\n] so the delete range stops
           short of the CRLF terminator. *)
        let line_end =
          if
            line_end_with_terminator > line_start
            && s.[line_end_with_terminator - 1] = '\r'
          then line_end_with_terminator - 1
          else line_end_with_terminator
        in
        (* Walk backwards from line_end over [ \t] then [-]+. *)
        let j = ref line_end in
        while !j > line_start && (s.[!j - 1] = ' ' || s.[!j - 1] = '\t') do
          decr j
        done;
        let trailing_ws_start = !j in
        while !j > line_start && s.[!j - 1] = '-' do
          decr j
        done;
        let dash_start = !j in
        if dash_start < trailing_ws_start then
          edits :=
            Cst_edit.delete ~start_offset:dash_start ~end_offset:line_end
            :: !edits;
        ignore trailing_ws_start;
        if !i < n then incr i (* skip the newline *)
      done;
      let fix = List.rev !edits in
      if fix = [] then
        Some (mk_result ~id:"TYPO-024" ~severity:Info ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-024" ~severity:Info ~message ~count:cnt
             ~fix))
    else None
  in
  { id = "TYPO-024"; run; languages = [] }

(* TYPO-025: Space before en-dash in number range *)
let r_typo_025 : rule =
  let re = Re_compat.regexp {|[0-9] +\(–\|--\)[0-9]|} in
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
        (mk_result ~id:"TYPO-025" ~severity:Warning
           ~message:{|Space before en‑dash in number range|} ~count:!cnt)
    else None
  in
  { id = "TYPO-025"; run; languages = [] }

(* TYPO-026: Wrong dash in page range — should use -- *)
let r_typo_026 : rule =
  let re = Re_compat.regexp {|[0-9]–[0-9]|} in
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
        (mk_result ~id:"TYPO-026" ~severity:Warning
           ~message:{|Wrong dash in page range – should use --|} ~count:!cnt)
    else None
  in
  { id = "TYPO-026"; run; languages = [] }

(* TYPO-027: Multiple exclamation marks — relocated from old TYPO-016. v26.3 §3
   item E (deferred batch): fix collapses each maximal run of >= 2 [!]
   characters to a single [!]. *)
let r_typo_027 : rule =
  let message = {|Multiple exclamation marks ‼|} in
  let run s =
    let cnt = count_substring s "!!" in
    if cnt > 0 then
      let runs = find_consecutive_runs s '!' ~min_len:2 in
      let fix =
        List.map
          (fun (start_offset, end_offset) ->
            Cst_edit.replace ~start_offset ~end_offset "!")
          runs
      in
      if fix = [] then
        Some (mk_result ~id:"TYPO-027" ~severity:Info ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-027" ~severity:Info ~message ~count:cnt
             ~fix)
    else None
  in
  { id = "TYPO-027"; run; languages = [] }

(* TYPO-028: Use of $$ display math delimiter *)
let r_typo_028 : rule =
  let run s =
    let cnt = count_substring s "$$" in
    (* Each pair of $$ counts as one — divide by 2 *)
    let cnt = cnt / 2 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-028" ~severity:Error
           ~message:{|Use of ``$$'' display math delimiter|} ~count:cnt)
    else None
  in
  { id = "TYPO-028"; run; languages = [] }

(* TYPO-029: Non-breaking space after \ref missing *)
let r_typo_029 : rule =
  let re = Re_compat.regexp {|\\ref{[^}]*} [a-zA-Z]|} in
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
        (mk_result ~id:"TYPO-029" ~severity:Info
           ~message:{|Non‑breaking space after \ref missing|} ~count:!cnt)
    else None
  in
  { id = "TYPO-029"; run; languages = [] }

(* TYPO-030: UK spelling inconsistency — DEFERRED: requires NLP (see comment
   block before TYPO-019 above) *)
let r_typo_030 : rule =
  let run _s = None in
  { id = "TYPO-030"; run; languages = [] }

(* TYPO-031: American punctuation placement inside quotes — DEFERRED: requires
   NLP (see comment block before TYPO-019 above) *)
let r_typo_031 : rule =
  let run _s = None in
  { id = "TYPO-031"; run; languages = [] }

(* TYPO-032: Comma before \cite *)
let r_typo_032 : rule =
  let re = Re_compat.regexp {|,[ ]*\\cite|} in
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
        (mk_result ~id:"TYPO-032" ~severity:Warning
           ~message:{|Comma before \cite|} ~count:!cnt)
    else None
  in
  { id = "TYPO-032"; run; languages = [] }

(* TYPO-033: Abbreviation et.al without space. v26.3 §3 item E: fix replaces
   "et.al" with "et al.". *)
let r_typo_033 : rule =
  let message = "Abbreviation et.al without space" in
  let run s =
    let cnt = count_substring s "et.al" in
    if cnt > 0 then
      let fix = mk_replace_edits s "et.al" "et al." in
      if fix = [] then
        Some (mk_result ~id:"TYPO-033" ~severity:Warning ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-033" ~severity:Warning ~message
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-033"; run; languages = [] }

let rules_pilot : rule list =
  [
    r_typo_001;
    r_typo_002;
    r_typo_003;
    r_typo_004;
    r_typo_005;
    r_typo_006;
    r_typo_007;
    r_typo_008;
    r_typo_009;
    r_typo_010;
    r_typo_011;
    r_typo_012;
    r_typo_013;
    r_typo_014;
    r_typo_015;
    r_typo_016;
    r_typo_017;
    r_typo_018;
    r_typo_019;
    r_typo_020;
    r_typo_021;
    r_typo_022;
    r_typo_023;
    r_typo_024;
    r_typo_025;
    r_typo_026;
    r_typo_027;
    r_typo_028;
    r_typo_029;
    r_typo_030;
    r_typo_031;
    r_typo_032;
    r_typo_033;
  ]

(* BEGIN VPD-generated validators v0.4.0 — DO NOT EDIT BELOW THIS LINE *)
(* 80 VPD-catalogue rules: 56 TYPO + 24 ENC Pattern definitions in
   specs/rules/vpd_patterns.json Soundness proofs in proofs/RegexFamily.v *)

(* Spurious space before footnote command \footnote *)
let r_typo_034 : rule =
  let run s =
    let cnt = count_substring s " \\footnote" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-034" ~severity:Info
           ~message:{|Spurious space before footnote command \footnote|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-034"; run; languages = [] }

(* French punctuation requires NBSP before ; : ! ? v26.3 §3 item E (deferred
   batch): fix replaces each [SPACE+PUNCT] with [NBSP+PUNCT]. NBSP = U+00A0 =
   0xC2 0xA0 in UTF-8. *)
let r_typo_035 : rule =
  let message = "French punctuation requires NBSP before ; : ! ?" in
  let nbsp = "\xc2\xa0" in
  let run s =
    let cnt =
      count_substring s " ;"
      + count_substring s " :"
      + count_substring s " !"
      + count_substring s " ?"
    in
    if cnt > 0 then
      let pairs =
        [
          (" ;", nbsp ^ ";");
          (" :", nbsp ^ ":");
          (" !", nbsp ^ "!");
          (" ?", nbsp ^ "?");
        ]
      in
      let fix = List.concat_map (fun (n, r) -> mk_replace_edits s n r) pairs in
      if fix = [] then
        Some (mk_result ~id:"TYPO-035" ~severity:Warning ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-035" ~severity:Warning ~message
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-035"; run; languages = [] }

(* Suspicious consecutive capitalised words (shouting) *)
let r_typo_036 : rule =
  let re =
    Re_compat.regexp
      {|\(^\|[ \t({]\)[A-Z][A-Z]+ [A-Z][A-Z]+ [A-Z][A-Z]+\($\|[ \t.,;:!?)}]\)|}
  in
  let run s =
    let rec loop i acc =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        ignore _mr;
        loop (Re_compat.match_end _mr) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-036" ~severity:Info
           ~message:"Suspicious consecutive capitalised words (shouting)"
           ~count:cnt)
    else None
  in
  { id = "TYPO-036"; run; languages = [] }

(* Space before comma. v26.3 §3 item E: fix replaces " ," with ",". *)
let r_typo_037 : rule =
  let message = "Space before comma" in
  let run s =
    let cnt = count_substring s " ," in
    if cnt > 0 then
      let fix = mk_replace_edits s " ," "," in
      if fix = [] then
        Some (mk_result ~id:"TYPO-037" ~severity:Info ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-037" ~severity:Info ~message ~count:cnt
             ~fix)
    else None
  in
  { id = "TYPO-037"; run; languages = [] }

(* E-mail address not in \href *)
let r_typo_038 : rule =
  let re = Re_compat.regexp "[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]+" in
  let run s =
    let rec loop i acc =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        ignore _mr;
        loop (Re_compat.match_end _mr) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-038" ~severity:Info
           ~message:{|E‑mail address not in \href|} ~count:cnt)
    else None
  in
  { id = "TYPO-038"; run; languages = [] }

(* Incorrect spacing around \ldots *)
let r_typo_041 : rule =
  let run s =
    let cnt =
      count_substring s ".\\ldots"
      + count_substring s "\\ldots."
      + count_substring s ",\\ldots"
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-041" ~severity:Info
           ~message:{|Incorrect spacing around \ldots|} ~count:cnt)
    else None
  in
  { id = "TYPO-041"; run; languages = [] }

(* Multiple consecutive question marks ?? *)
let r_typo_042 : rule =
  let run s =
    let cnt = count_substring s "??" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-042" ~severity:Info
           ~message:"Multiple consecutive question marks ??" ~count:cnt)
    else None
  in
  { id = "TYPO-042"; run; languages = [] }

(* Smart quotes inside verbatim detected *)
let r_typo_043 : rule =
  let run s =
    let cnt =
      count_substring s "\xe2\x80\x9c"
      + count_substring s "\xe2\x80\x9d"
      + count_substring s "\xe2\x80\x98"
      + count_substring s "\xe2\x80\x99"
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-043" ~severity:Warning
           ~message:"Smart quotes inside verbatim detected" ~count:cnt)
    else None
  in
  { id = "TYPO-043"; run; languages = [] }

(* TYPO-044: Acronym not defined on first use — scan for uppercase sequences of
   2+ letters (e.g., "API", "NASA") and check whether their first occurrence in
   the document is accompanied by a parenthetical expansion like "Application
   Programming Interface (API)" or "API (Application Programming Interface)". If
   not, we flag it as undefined on first use. We exclude common well-known
   abbreviations that don't need expansion: e.g., USA, UK, PDF, etc. and LaTeX
   command names. *)
let r_typo_044 : rule =
  let well_known =
    [
      "OK";
      "USA";
      "UK";
      "EU";
      "UN";
      "NATO";
      "NASA";
      "CEO";
      "PhD";
      "Dr";
      "Mr";
      "Mrs";
      "Ms";
      "Jr";
      "Sr";
      "II";
      "III";
      "IV";
      "AM";
      "PM";
      "BC";
      "AD";
      "PDF";
      "HTML";
      "URL";
      "USB";
      "CPU";
      "GPU";
      "RAM";
      "ROM";
      "DVD";
      "CD";
      "TV";
      "FM";
      "AC";
      "DC";
      "ID";
      "IP";
      "OS";
      "PC";
      "AI";
      "ML";
      "API";
      "FAQ";
      "DIY";
      "GPS";
      "VPN";
      "PhD";
      "MBA";
      "MD";
      "IEEE";
      "ACM";
      "ISO";
      "RFC";
      "HTTP";
      "HTTPS";
      "SSH";
      "FTP";
      "DNS";
      "TCP";
      "UDP";
      "XML";
      "JSON";
      "YAML";
      "CSV";
      "SQL";
      "CSS";
      "RSS";
      "SMTP";
      "IMAP";
      "POP";
      "SSL";
      "TLS";
      "AES";
      "RSA";
      "SHA";
      "UNIX";
      "GNU";
      "BSD";
      "MIT";
      "GPL";
      "ASCII";
      "UTF";
      "NFC";
      "NFKC";
    ]
  in
  let re = Re_compat.regexp {|\([A-Z][A-Z0-9]+\)|} in
  let is_alnum c =
    (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
  in
  let run s =
    let s_text = strip_math_segments s in
    let n_text = String.length s_text in
    (* Collect all acronym occurrences with their positions *)
    let first_use = Hashtbl.create 32 in
    let i = ref 0 in
    (try
       while true do
         let _mr, pos = Re_compat.search_forward re s_text !i in
         let acr = Re_compat.matched_group _mr 1 s_text in
         let match_end = Re_compat.match_end _mr in
         (* Manual word-boundary check *)
         let before_ok = pos = 0 || not (is_alnum s_text.[pos - 1]) in
         let after_ok =
           match_end >= n_text || not (is_alnum s_text.[match_end])
         in
         if before_ok && after_ok then
           if not (Hashtbl.mem first_use acr) then Hashtbl.add first_use acr pos;
         i := match_end
       done
     with Not_found -> ());
    (* For each first-use acronym, check if it's well-known or has a nearby
       parenthetical definition *)
    let cnt = ref 0 in
    Hashtbl.iter
      (fun acr pos ->
        if not (List.mem acr well_known) then
          (* Look for "(ACR)" or "ACR (" within 200 chars before/after *)
          let window_start = max 0 (pos - 200) in
          let window_end =
            min (String.length s_text) (pos + String.length acr + 200)
          in
          let window =
            String.sub s_text window_start (window_end - window_start)
          in
          let has_paren_def =
            (* "(ACR)" pattern *)
            let pat1 = "(" ^ acr ^ ")" in
            (* "ACR (" pattern — definition after acronym *)
            let pat2 = acr ^ " (" in
            count_substring window pat1 > 0 || count_substring window pat2 > 0
          in
          if not has_paren_def then incr cnt)
      first_use;
    if !cnt > 0 then
      Some
        (mk_result ~id:"TYPO-044" ~severity:Info
           ~message:"Acronym not defined on first use" ~count:!cnt)
    else None
  in
  { id = "TYPO-044"; run; languages = [] }

(* En-dash used as minus sign in text *)
let r_typo_048 : rule =
  let run s =
    let cnt =
      (fun s ->
        let s = strip_math_segments s in
        Unicode.count_en_dash s)
        s
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-048" ~severity:Info
           ~message:"En‑dash used as minus sign in text" ~count:cnt)
    else None
  in
  { id = "TYPO-048"; run; languages = [] }

(* Figure space U+2009 used instead of \thinspace macro *)
let r_typo_051 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x80\x89" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-051" ~severity:Warning
           ~message:{|Figure space U+2009 used instead of \thinspace macro|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-051"; run; languages = [] }

(* Unescaped < or > in text *)
let r_typo_052 : rule =
  let run s =
    let cnt =
      (fun s ->
        let s = strip_math_segments s in
        count_char s '<' + count_char s '>')
        s
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-052" ~severity:Warning
           ~message:"Unescaped < or > in text; use \\textless / \\textgreater"
           ~count:cnt)
    else None
  in
  { id = "TYPO-052"; run; languages = [] }

(* Unicode leader dots U+22EF forbidden *)
let r_typo_053 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x8b\xaf" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-053" ~severity:Warning
           ~message:{|Unicode ⋯ (U+22EF) leader forbidden; use \dots instead|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-053"; run; languages = [] }

(* Hair-space required after en-dash in word-word ranges *)
let r_typo_054 : rule =
  let re = Re_compat.regexp "[a-zA-Z]\xe2\x80\x93[a-zA-Z]" in
  let run s =
    let rec loop i acc =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        ignore _mr;
        loop (Re_compat.match_end _mr) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-054" ~severity:Info
           ~message:"Hair‑space required after en‑dash in word–word ranges"
           ~count:cnt)
    else None
  in
  { id = "TYPO-054"; run; languages = [] }

(* Consecutive thin-spaces prohibited *)
let r_typo_055 : rule =
  let run s =
    let cnt = count_substring s "\\,\\," in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-055" ~severity:Info
           ~message:{|Consecutive thin‑spaces (\,\,) prohibited; collapse|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-055"; run; languages = [] }

(* Missing thin-space before degree symbol *)
let r_typo_057 : rule =
  let re = Re_compat.regexp "[0-9]\xc2\xb0" in
  let run s =
    let rec loop i acc =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        ignore _mr;
        loop (Re_compat.match_end _mr) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-057" ~severity:Info
           ~message:{|Missing thin‑space before °C/°F or \si{\celsius}|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-057"; run; languages = [] }

(* Unicode multiplication sign in text *)
let r_typo_061 : rule =
  let run s =
    let s = strip_math_segments s in
    let cnt = count_substring s "\xc3\x97" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-061" ~severity:Info
           ~message:{|Unicode × (U+00D7) in text; prefer \times via math mode|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-061"; run; languages = [] }

(* Non-breaking hyphen U+2011 found *)
let r_typo_063 : rule =
  let run s =
    let cnt = count_substring s "\xe2\x80\x91" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-063" ~severity:Info
           ~message:"Non‑breaking hyphen U+2011 found inside URL" ~count:cnt)
    else None
  in
  { id = "TYPO-063"; run; languages = [] }

(* URL split across lines without \url{} *)
let r_typo_039 : rule =
  let re = Re_compat.regexp "https?://[^ \t\n}]+" in
  let run s =
    let rec loop i acc =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        ignore _mr;
        loop (Re_compat.match_end _mr) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-039" ~severity:Info
           ~message:"URL split across lines without \\url{}" ~count:cnt)
    else None
  in
  { id = "TYPO-039"; run; languages = [] }

(* Inline math $...$ exceeds 80 characters *)
let r_typo_040 : rule =
  let re = Re_compat.regexp "\\$\\([^$]+\\)\\$" in
  let run s =
    let rec loop i acc =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        ignore _mr;
        let inner = Re_compat.matched_group _mr 1 s in
        let acc' = if String.length inner > 80 then acc + 1 else acc in
        loop (Re_compat.match_end _mr) acc'
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-040" ~severity:Info
           ~message:"Math in text mode $…$ exceeds 80 characters" ~count:cnt)
    else None
  in
  { id = "TYPO-040"; run; languages = [] }

(* Non-ASCII punctuation in math mode *)
let r_typo_045 : rule =
  let run s =
    let cnt =
      (fun s ->
        let n = String.length s in
        let rec scan i inside acc =
          if i >= n then acc
          else
            let c = Char.code s.[i] in
            if c = 0x24 then scan (i + 1) (not inside) acc
            else if inside && c >= 0x80 then scan (i + 1) inside (acc + 1)
            else scan (i + 1) inside acc
        in
        scan 0 false 0)
        s
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-045" ~severity:Warning
           ~message:"Non‑ASCII punctuation in math mode (‘ ’ “ ”)" ~count:cnt)
    else None
  in
  { id = "TYPO-045"; run; languages = [] }

(* Use of \begin{math} instead of $...$ *)
let r_typo_046 : rule =
  let run s =
    let cnt =
      count_substring s "\\begin{math}" + count_substring s "\\end{math}"
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-046" ~severity:Info
           ~message:"Use of $begin:math:text$ … $end:math:text$ instead of $…$"
           ~count:cnt)
    else None
  in
  { id = "TYPO-046"; run; languages = [] }

(* Starred \section* used where numbered section expected *)
let r_typo_047 : rule =
  let run s =
    let cnt = count_substring s "\\section*" in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-047" ~severity:Info
           ~message:"Starred \\section* used where numbered section expected"
           ~count:cnt)
    else None
  in
  { id = "TYPO-047"; run; languages = [] }

(* Space after opening quote *)
let r_typo_049 : rule =
  let run s =
    let cnt =
      count_substring s "\xe2\x80\x9c " + count_substring s "\xe2\x80\x98 "
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-049" ~severity:Info
           ~message:"Space after opening quote" ~count:cnt)
    else None
  in
  { id = "TYPO-049"; run; languages = [] }

(* Legacy TeX accent command found *)
let r_typo_056 : rule =
  let re = Re_compat.regexp "\\\\['^`\"~=.][{][a-zA-Z][}]" in
  let run s =
    let rec loop i acc =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        ignore _mr;
        loop (Re_compat.match_end _mr) (acc + 1)
      with Not_found -> acc
    in
    let cnt = loop 0 0 in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-056" ~severity:Warning
           ~message:"Legacy TeX accents present despite UTF‑8 input" ~count:cnt)
    else None
  in
  { id = "TYPO-056"; run; languages = [] }

(* Greek homograph letter found in Latin text *)
let r_typo_058 : rule =
  let run s =
    let cnt =
      count_substring s "\xce\xb1"
      + count_substring s "\xce\xb5"
      + count_substring s "\xce\xb9"
      + count_substring s "\xce\xbf"
      + count_substring s "\xcf\x81"
      + count_substring s "\xcf\x82"
      + count_substring s "\xcf\x85"
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-058" ~severity:Warning
           ~message:"Greek homograph letters used in Latin words (ϲ,ɑ,ᴦ…)"
           ~count:cnt)
    else None
  in
  { id = "TYPO-058"; run; languages = [] }

(* TYPO-060: Smart quotes inside lstlisting/verbatim environments *)
let r_typo_060 : rule =
  let _re_begin_lst = Re_compat.regexp_string "\\begin{lstlisting}" in
  let _re_end_lst = Re_compat.regexp_string "\\end{lstlisting}" in
  let _re_begin_verb = Re_compat.regexp_string "\\begin{verbatim}" in
  let _re_end_verb = Re_compat.regexp_string "\\end{verbatim}" in
  let run s =
    (* Extract content within \begin{lstlisting}...\end{lstlisting} and
       \begin{verbatim}...\end{verbatim}, then scan for curly quotes *)
    let curly_in_env open_re close_re olen clen =
      let rec loop i acc =
        match
          try
            let _mr, _p = Re_compat.search_forward open_re s i in
            Some _p
          with Not_found -> None
        with
        | None -> acc
        | Some start -> (
            let content_start = start + olen in
            match
              try
                let _mr, _p =
                  Re_compat.search_forward close_re s content_start
                in
                Some _p
              with Not_found -> None
            with
            | None -> acc
            | Some end_pos ->
                let block =
                  String.sub s content_start (end_pos - content_start)
                in
                let cnt =
                  count_substring block "\xe2\x80\x9c"
                  + count_substring block "\xe2\x80\x9d"
                  + count_substring block "\xe2\x80\x98"
                  + count_substring block "\xe2\x80\x99"
                in
                loop (end_pos + clen) (acc + cnt))
      in
      loop 0 0
    in
    let cnt =
      curly_in_env _re_begin_lst _re_end_lst 18 16
      + curly_in_env _re_begin_verb _re_end_verb 16 14
    in
    if cnt > 0 then
      Some
        (mk_result ~id:"TYPO-060" ~severity:Warning
           ~message:
             {|Smart quotes present inside \lstlisting / verbatim environments|}
           ~count:cnt)
    else None
  in
  { id = "TYPO-060"; run; languages = [] }

let rules_vpd_gen : rule list =
  [
    r_typo_034;
    r_typo_035;
    r_typo_036;
    r_typo_037;
    r_typo_038;
    r_typo_039;
    r_typo_040;
    r_typo_041;
    r_typo_042;
    r_typo_043;
    r_typo_044;
    r_typo_045;
    r_typo_046;
    r_typo_047;
    r_typo_048;
    r_typo_049;
    r_typo_051;
    r_typo_052;
    r_typo_053;
    r_typo_054;
    r_typo_055;
    r_typo_056;
    r_typo_057;
    r_typo_058;
    r_typo_060;
    r_typo_061;
    r_typo_063;
  ]

(* END VPD-generated validators *)
