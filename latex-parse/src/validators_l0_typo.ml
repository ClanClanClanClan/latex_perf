open Validators_common

(* Pilot L0 rules (IDs aligned with rules_v3.yaml). Info-level mapped to
   Warning. *)

let r_typo_001 : rule =
  (* v27.0.8: math-aware fix producer for ASCII straight quote -> curly.
     Disambiguation strategy: index-based ALTERNATION across straight-quote
     occurrences outside math AND not preceded by an odd number of backslashes.
     Even-index -> U+201C (left/opening), odd-index -> U+201D (right/closing).

     CRITICAL (round-1 audit): skips backslash-escaped quotes because in LaTeX,
     backslash-doublequote-letter is the umlaut command (e.g. renders u-umlaut);
     auto-replacing would corrupt it. Count semantic preserved (count_char on
     strip_math_segments output, matches pre-v27.0.8 behaviour); fix-set is the
     corrective action and may be smaller than count when escapes/math are
     present. Message inlined per round-3 v27.0.6 pattern. *)
  let is_escaped_quote s i =
    let rec count back acc =
      if back < 0 then acc
      else if String.unsafe_get s back = '\\' then count (back - 1) (acc + 1)
      else acc
    in
    count (i - 1) 0 land 1 = 1
  in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let outside off = not (is_in_math_range math off) in
    let n = String.length s in
    let rec collect i acc =
      if i >= n then List.rev acc
      else if s.[i] = '"' && outside i && not (is_escaped_quote s i) then
        collect (i + 1) (i :: acc)
      else collect (i + 1) acc
    in
    let offsets = collect 0 [] in
    List.mapi
      (fun idx off ->
        let replacement =
          if idx mod 2 = 0 then "\xe2\x80\x9c" else "\xe2\x80\x9d"
        in
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 1) replacement)
      offsets
  in
  let run s =
    let stripped = strip_math_segments s in
    let cnt = count_char stripped '"' in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-001" ~severity:Error
             ~message:{|ASCII straight quotes (" … ") must be curly quotes|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-001" ~severity:Error
             ~message:{|ASCII straight quotes (" … ") must be curly quotes|}
             ~count:cnt ~fix)
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

(* ── P3 context-aware match collection (token-aware variants) ──────────────
   The pilot L0 rules are string-level and were context-blind, firing on
   deviations inside verbatim / comments / math / url targets (the reason they
   stayed `L0_VALIDATORS=pilot`-gated; see docs/archive/RULES_PILOT_TODO.md).
   [occurrences_in_text] returns the offsets of [needle] that lie in ordinary
   prose only, by filtering through a precomputed [exempt] = [find_exempt_ranges
   s]. A retrofitted rule computes [exempt] once and derives BOTH its count and
   its fix edits from the same filtered offsets, so they stay consistent and the
   rule no longer false-positives in protected regions — the post-pilot-gate
   prerequisite for graduating it to the default rule set. *)
let occurrences_in_text exempt (s : string) (needle : string) : int list =
  find_all_non_overlapping s needle
  |> List.filter (fun off -> not (is_in_exempt_range exempt off))

(* Overlapping count of [needle] in [s] outside exempt ranges. Preserves the
   diagnostic-count semantics of [count_substring] (which allows overlaps — e.g.
   "--" occurs twice in "---") while skipping protected regions. Using this for
   the COUNT (and [occurrences_in_text] for the non-overlapping FIX offsets)
   keeps a retrofitted rule's count identical to its string-level form on
   ordinary prose, so DAG conflict resolution (which tie-breaks on count) and
   the lint output are unchanged outside protected regions. *)
let count_in_text exempt (s : string) (needle : string) : int =
  let n = String.length s and m = String.length needle in
  if m = 0 || n < m then 0
  else
    let rec loop i acc =
      if i > n - m then acc
      else if String.sub s i m = needle && not (is_in_exempt_range exempt i)
      then loop (i + 1) (acc + 1)
      else loop (i + 1) acc
    in
    loop 0 0

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

(** [mk_replace_edits_exempt exempt s needle replacement] — context-aware
    counterpart of [mk_replace_edits]: emits a non-overlapping [needle] →
    [replacement] replace for every occurrence OUTSIDE the [exempt] ranges
    (verbatim / comments / math / url), via [occurrences_in_text]. Use in a
    retrofitted rule so its fix never touches a protected region. *)
let mk_replace_edits_exempt exempt (s : string) (needle : string)
    (replacement : string) : Cst_edit.t list =
  let nlen = String.length needle in
  List.map
    (fun off ->
      Cst_edit.replace ~start_offset:off ~end_offset:(off + nlen) replacement)
    (occurrences_in_text exempt s needle)

let r_typo_002 : rule =
  let message = "Double hyphen -- should be en‑dash –" in
  (* P3 context-aware (token-aware variant): count + fix derive from the same
     exempt-filtered offsets, so `--` inside verbatim / comments / math / url is
     ignored (it is literal there), not just inside plain prose. This replaces
     the former string-level `count_substring` default branch and the incomplete
     `L0_TOKEN_AWARE` Tokenizer_lite branch (Tokenizer_lite has no
     comment/verbatim kinds, so it could not skip those regions).

     Fix-set delegation (oscillation fix): numeric/page ranges (digit`--`digit)
     are left as `--`, the canonical LaTeX source form and TYPO-026's domain, so
     TYPO-002 (`--`→`–`) and TYPO-026 do not oscillate under --apply-fixes
     (check_apply_fixes_safety.py). The count still tallies every prose `--`;
     only the fix is withheld at range offsets. *)
  let run s =
    let exempt = find_exempt_ranges s in
    (* Count keeps [count_substring]'s overlapping semantics (so "--" tallies 2
       in "---" and the TYPO-002⇄TYPO-003 conflict tie-break is unchanged); the
       fix uses non-overlapping offsets. Both skip exempt regions. *)
    let cnt = count_in_text exempt s "--" in
    if cnt > 0 then
      let n = String.length s in
      let is_digit c = c >= '0' && c <= '9' in
      let is_numeric_range off =
        off > 0 && is_digit s.[off - 1] && off + 2 < n && is_digit s.[off + 2]
      in
      let fix =
        List.filter_map
          (fun off ->
            if is_numeric_range off then None
            else
              Some
                (Cst_edit.replace ~start_offset:off ~end_offset:(off + 2) "–"))
          (occurrences_in_text exempt s "--")
      in
      if fix = [] then
        Some (mk_result ~id:"TYPO-002" ~severity:Warning ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-002" ~severity:Warning ~message
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-002"; run; languages = [] }

let r_typo_003 : rule =
  let message = "Triple hyphen --- should be em‑dash —" in
  (* P3 context-aware (token-aware variant): count + fix both derive from the
     same exempt-filtered offsets, so `---` inside verbatim / comments / math /
     url is ignored (literal there), not flagged. Replaces the former
     string-level `count_substring` default branch and the incomplete
     `L0_TOKEN_AWARE` Tokenizer_lite branch (Tokenizer_lite has no
     comment/verbatim kinds, so it could not skip those regions). Count keeps
     [count_substring]'s overlapping semantics on prose, preserving the
     TYPO-002⇄TYPO-003 conflict tie-break (which compares counts). *)
  let run s =
    let exempt = find_exempt_ranges s in
    let cnt = count_in_text exempt s "---" in
    if cnt > 0 then
      let fix =
        List.map
          (fun off ->
            Cst_edit.replace ~start_offset:off ~end_offset:(off + 3) "—")
          (occurrences_in_text exempt s "---")
      in
      if fix = [] then
        Some (mk_result ~id:"TYPO-003" ~severity:Warning ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-003" ~severity:Warning ~message
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-003"; run; languages = [] }

let r_typo_004 : rule =
  (* v27.0.6: math-aware fix producer. Counts both `` and '' everywhere
     (preserves existing rule-firing semantics; the count is a severity
     indicator); FILTERS fix-edit offsets to only those outside math segments,
     so `''` inside `$f''(x)$` is reported but not auto-fixed. Unblocked by
     [find_math_ranges] / [is_in_math_range] helpers added to
     validators_common.ml in this cycle.

     Message is inlined in mk_result/mk_result_with_fix calls below — NOT
     extracted to a [let message = ...] binding, because the
     scripts/validate_messages.sh extractor doesn't follow let-bindings and the
     `messages` CI gate would mis-pair TYPO-003 with TYPO-004's message string
     (per feedback_silent_gate_failures memo). *)
  (* P3 context-aware (token-aware variant): both count and fix now skip the
     full exempt set (verbatim / comments / math / url) via [find_exempt_ranges],
     superseding the v27.0.6 math-only [find_math_ranges] filter. Counting only
     non-exempt occurrences makes the rule fully SILENT in protected regions —
     the post-pilot-gate property for promotion — rather than the former
     "fires count, no fix" behaviour that still surfaced a Warning inside math.
     `` and '' inside math/verbatim are literal (e.g. `$f''(x)$` double-prime),
     so they are neither reported nor fixed. *)
  let mk_fix_edits exempt s =
    let bt_offsets = occurrences_in_text exempt s "``" in
    let ap_offsets = occurrences_in_text exempt s "''" in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 2) "\xe2\x80\x9c")
      bt_offsets
    @ List.map
        (fun off ->
          Cst_edit.replace ~start_offset:off ~end_offset:(off + 2)
            "\xe2\x80\x9d")
        ap_offsets
  in
  let run s =
    let exempt = find_exempt_ranges s in
    let cnt = count_in_text exempt s "``" + count_in_text exempt s "''" in
    if cnt > 0 then
      let fix = mk_fix_edits exempt s in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-004" ~severity:Warning
             ~message:
               "TeX double back‑tick ``…'' not allowed; use opening curly \
                quotes"
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-004" ~severity:Warning
             ~message:
               "TeX double back‑tick ``…'' not allowed; use opening curly \
                quotes"
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-004"; run; languages = [] }

let r_typo_005 : rule =
  (* v27.0.7: math-aware fix producer for `...` → `\dots`. Pre-v27.0.7 the
     validator counted occurrences in the math-stripped buffer (so `...` inside
     `$1, 2, ..., n$` ellipsis idiom didn't fire). v27.0.7 keeps that count
     semantic but emits fix edits at original-string offsets, filtered by
     find_math_ranges.

     Note divergence from TYPO-004 pattern: count uses [count_substring
     (strip_math_segments s) "..."] (overlapping count for severity), fix uses
     [find_all_non_overlapping s "..." |> filter (not in math)] (non-overlapping
     for non-conflicting edits). Counts can differ on pathological inputs like
     `....` (count = 2 with overlap, fix = 1 non-overlapping). Acceptable per
     the TYPO-002/003 documented pattern.

     Message inlined per round-3 v27.0.6 pattern (validate_messages.sh extractor
     doesn't follow let-bindings). *)
  (* P3 context-aware (token-aware variant): the count, formerly taken on the
     math-stripped buffer ([count_substring (strip_math_segments s) "..."]), now
     uses [count_in_text exempt s "..."] — equivalent on math (still skips `...`
     inside `$1,2,...,n$`) and additionally skips verbatim / comments / url. Fix
     offsets come from the same exempt set. *)
  let mk_fix_edits exempt s =
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 3) "\\dots")
      (occurrences_in_text exempt s "...")
  in
  let run s =
    let exempt = find_exempt_ranges s in
    let cnt = count_in_text exempt s "..." in
    if cnt > 0 then
      let fix = mk_fix_edits exempt s in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-005" ~severity:Warning
             ~message:"Ellipsis typed as three periods ...; use \\dots"
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-005" ~severity:Warning
             ~message:"Ellipsis typed as three periods ...; use \\dots"
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-005"; run; languages = [] }

let r_typo_006 : rule =
  let run s =
    let cnt = count_char s '\t' in
    if cnt > 0 then (
      let n = String.length s in
      let edits = ref [] in
      for i = n - 1 downto 0 do
        if s.[i] = '\t' then
          edits :=
            Cst_edit.replace ~start_offset:i ~end_offset:(i + 1) "    "
            :: !edits
      done;
      let fix = !edits in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-006" ~severity:Error
             ~message:"Tab character U+0009 forbidden" ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-006" ~severity:Error
             ~message:"Tab character U+0009 forbidden" ~count:cnt ~fix))
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
        if matched > 0 then (
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
                &&
                let c = s.[!trim_start - 1] in
                c = ' ' || c = '\t' || c = '\r'
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
            &&
            let c = s.[!trim_start - 1] in
            c = ' ' || c = '\t' || c = '\r'
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
                 ~message:"Trailing spaces at end of line" ~count:matched ~fix))
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
      Some
        (mk_result ~id:"TYPO-008" ~severity:Info
           ~message:"Multiple consecutive blank lines (> 2) in source"
           ~count:cnt)
    else
      Some
        (mk_result_with_fix ~id:"TYPO-008" ~severity:Info
           ~message:"Multiple consecutive blank lines (> 2) in source"
           ~count:cnt ~fix)
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
    if cnt > 0 then (
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
        Some
          (mk_result ~id:"TYPO-009" ~severity:Warning
             ~message:"Non‑breaking space ~ used incorrectly at line start"
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-009" ~severity:Warning
             ~message:"Non‑breaking space ~ used incorrectly at line start"
             ~count:cnt ~fix))
    else None
  in
  { id = "TYPO-009"; run; languages = [] }

let r_typo_010 : rule =
  let message = "Space before punctuation , . ; : ? !" in
  (* Fix: for each `<space><punct>` pair, drop the leading space. We emit a
     2-byte → 1-byte replace (start..start+2 → punct). Operate on the
     non-tokenized substring view because the byte offsets are needed for
     [Cst_edit.replace]; the token-aware count loop above is a stricter gate on
     what counts as a "space" but its offsets aren't directly accessible. In
     practice the underlying byte patterns coincide for the ASCII-only
     space-before-punct case targeted by this rule.

     v27.0.60: filter `;` and `:` from the fix-set, delegating those positions
     to SPC-016 (space-before-semicolon) and SPC-021 (space-before-colon), both
     Warning severity. Same cross-rule pattern as v27.0.56 (SPC-035/TYPO-051
     leading-run filter): TYPO-010 still counts all 6 punct chars (count
     semantic preserved); only the fix-set shrinks at `;`/`:` offsets, where
     SPC-016/021's 1-byte delete emits instead of TYPO-010's 2-byte→1-byte
     replace. *)
  (* P3 context-aware (token-aware variant): count + fix both skip the exempt
     set (verbatim / comments / math / url) via [find_exempt_ranges], replacing
     the former string-level `count_substring` default branch and the
     `L0_TOKEN_AWARE` Tokenizer_lite branch (which had no comment/verbatim
     kinds). Count still tallies all 6 punct chars (` ,` ` .` ` ;` ` :` ` ?`
     ` !`); the fix-set still excludes `;`/`:` (delegated to SPC-016/SPC-021,
     v27.0.60), and now additionally skips any space-before-punct inside a
     protected region. *)
  let punct_chars = [ ','; '.'; '?'; '!' ] in
  let mk_fix_edits exempt s =
    let n = String.length s in
    let edits = ref [] in
    let i = ref 0 in
    while !i < n - 1 do
      if
        s.[!i] = ' '
        && List.mem s.[!i + 1] punct_chars
        && not (is_in_exempt_range exempt !i)
      then (
        edits :=
          Cst_edit.replace ~start_offset:!i ~end_offset:(!i + 2)
            (String.make 1 s.[!i + 1])
          :: !edits;
        i := !i + 2)
      else incr i
    done;
    List.rev !edits
  in
  let run s =
    let exempt = find_exempt_ranges s in
    let combos = [ " ,"; " ."; " ;"; " :"; " ?"; " !" ] in
    let cnt =
      List.fold_left (fun acc sub -> acc + count_in_text exempt s sub) 0 combos
    in
    if cnt > 0 then
      let fix = mk_fix_edits exempt s in
      if fix = [] then
        Some (mk_result ~id:"TYPO-010" ~severity:Info ~message ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-010" ~severity:Info ~message ~count:cnt
             ~fix)
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

(* TYPO-012: Straight apostrophe used for minutes/feet/prime. v27.0.21:
   math-aware fix producer. Inside math (`$...$`), `5'` denotes prime notation
   (5^\prime); outside math it could legitimately be possessive (the 1980s) or
   feet/minutes (5 ft 2 in), so the fix applies ONLY inside math. Pattern: digit
   + apostrophe (2 bytes). The apostrophe sits at offset+1; replace it with
   `^\prime` (7 bytes). The count semantic is preserved (rule fires anywhere
   `[0-9]'` appears, not just in math) for 0-differential vs v27.0.20. The math
   filter is POSITIVE (`is_in_math_range pos`) here, the OPPOSITE of the
   v27.0.6+ pattern (`not (is_in_math_range pos)`), because `'` after digit only
   unambiguously means prime inside math. *)
let r_typo_012 : rule =
  let re = Re_compat.regexp {|[0-9]'|} in
  let collect_offsets s =
    let rec loop i acc =
      try
        let mr, pos = Re_compat.search_forward re s i in
        loop (Re_compat.match_end mr) (pos :: acc)
      with Not_found -> List.rev acc
    in
    loop 0 []
  in
  let fix_offsets s =
    let math = find_math_ranges s in
    List.filter (fun pos -> is_in_math_range math pos) (collect_offsets s)
  in
  let mk_fix_edits offsets =
    List.map
      (fun pos ->
        let prime_off = pos + 1 in
        Cst_edit.replace ~start_offset:prime_off ~end_offset:(prime_off + 1)
          "^\\prime")
      offsets
  in
  let run s =
    let cnt = List.length (collect_offsets s) in
    if cnt > 0 then
      let fix = mk_fix_edits (fix_offsets s) in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-012" ~severity:Warning
             ~message:
               {|Straight apostrophe ' used for minutes/feet; use ^\prime or ′|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-012" ~severity:Warning
             ~message:
               {|Straight apostrophe ' used for minutes/feet; use ^\prime or ′|}
             ~count:cnt ~fix)
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
        Some
          (mk_result ~id:"TYPO-013" ~severity:Warning
             ~message:"ASCII back‑tick ` used as opening quote" ~count:!cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-013" ~severity:Warning
             ~message:"ASCII back‑tick ` used as opening quote" ~count:!cnt ~fix)
    else None
  in
  { id = "TYPO-013"; run; languages = [] }

(* TYPO-014: Space before percent sign — relocated from old TYPO-028 *)
let r_typo_014 : rule =
  let run s =
    let cnt = count_substring s " %" in
    if cnt > 0 then
      let fix = mk_replace_edits s " %" "%" in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-014" ~severity:Info
             ~message:{|Space before percent sign \%|} ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-014" ~severity:Info
             ~message:{|Space before percent sign \%|} ~count:cnt ~fix)
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
        Some
          (mk_result ~id:"TYPO-015" ~severity:Warning
             ~message:{|Double \% in source; likely stray percent|} ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-015" ~severity:Warning
             ~message:{|Double \% in source; likely stray percent|} ~count:cnt
             ~fix)
    else None
  in
  { id = "TYPO-015"; run; languages = [] }

(* TYPO-016: Non-breaking space ~ missing before \cite / \ref *)
let r_typo_016 : rule =
  let re = Re_compat.regexp {| \\\(cite\|ref\)[^a-zA-Z]|} in
  let run s =
    let cnt = ref 0 in
    let edits = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _mr, _ = Re_compat.search_forward re s !i in
         let mb = Re_compat.match_beginning _mr in
         (* Match shape: " \cite[^a-zA-Z]" or " \ref[^a-zA-Z]". The leading
            space is at offset mb. Replace the space with `~`. *)
         edits :=
           Cst_edit.replace ~start_offset:mb ~end_offset:(mb + 1) "~" :: !edits;
         incr cnt;
         i := Re_compat.match_end _mr
       done
     with Not_found -> ());
    let cnt = !cnt in
    if cnt > 0 then
      let fix = List.rev !edits in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-016" ~severity:Info
             ~message:{|Non‑breaking space ~ missing before \cite / \ref|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-016" ~severity:Info
             ~message:{|Non‑breaking space ~ missing before \cite / \ref|}
             ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-016"; run; languages = [] }

(* TYPO-017: TeX accent commands in text. v27.0.18: math-aware fix producer.
   Pattern \\<accent>{<letter>} (6 bytes) -> \\<accent><letter> (3 bytes) --
   braces-removal is semantically identical in LaTeX and avoids the UTF-8
   inputenc dependency that the alternative full UTF-8 conversion would require
   (works on legacy docs without `\usepackage[utf8]{inputenc}`). Math-aware on
   fix offsets only; the count uses the full regex match (preserves pre-v27.0.18
   semantic for 0-differential vs v27.0.17). The accent character class is
   text-mode only (apostrophe, caret, doublequote, tilde, equals, period,
   backtick), so math accents like \hat{} are not in scope by construction. *)
let r_typo_017 : rule =
  let re = Re_compat.regexp {|\\['^`"~=.][{][a-zA-Z][}]|} in
  let collect_offsets s =
    let rec loop i acc =
      try
        let mr, pos = Re_compat.search_forward re s i in
        loop (Re_compat.match_end mr) (pos :: acc)
      with Not_found -> List.rev acc
    in
    loop 0 []
  in
  let fix_offsets s =
    let math = find_math_ranges s in
    List.filter (fun pos -> not (is_in_math_range math pos)) (collect_offsets s)
  in
  let mk_fix_edits s offsets =
    List.map
      (fun pos ->
        let accent = s.[pos + 1] in
        let letter = s.[pos + 3] in
        Cst_edit.replace ~start_offset:pos ~end_offset:(pos + 5)
          (Printf.sprintf "\\%c%c" accent letter))
      offsets
  in
  let run s =
    let cnt = List.length (collect_offsets s) in
    if cnt > 0 then
      let fix = mk_fix_edits s (fix_offsets s) in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-017" ~severity:Info
             ~message:{|TeX accent commands (\'{e}) in text; prefer UTF‑8 é|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-017" ~severity:Info
             ~message:{|TeX accent commands (\'{e}) in text; prefer UTF‑8 é|}
             ~count:cnt ~fix)
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

(* TYPO-021: Capital letter after ellipsis without space. v26.4 §1.3: fix
   inserts a single space between the ellipsis and the capital letter. Both
   `...A` and `…A` (Unicode ellipsis U+2026) get the same insertion. *)
let r_typo_021 : rule =
  let re = Re_compat.regexp {|\(\.\.\.\|…\)[A-Z]|} in
  let run s =
    let cnt = ref 0 in
    let edits = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _mr, _ = Re_compat.search_forward re s !i in
         let me = Re_compat.match_end _mr in
         (* Insert a space immediately before the capital letter at me-1. *)
         edits :=
           Cst_edit.replace ~start_offset:(me - 1) ~end_offset:(me - 1) " "
           :: !edits;
         incr cnt;
         i := me
       done
     with Not_found -> ());
    if !cnt > 0 then
      let fix = List.rev !edits in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-021" ~severity:Info
             ~message:"Capital letter after ellipsis without space" ~count:!cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-021" ~severity:Info
             ~message:"Capital letter after ellipsis without space" ~count:!cnt
             ~fix)
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

(* TYPO-025: Space before en-dash in number range. v26.4 §1.3: fix deletes the
   space-run between the leading digit and the en-dash. *)
let r_typo_025 : rule =
  let re = Re_compat.regexp {|[0-9] +\(–\|--\)[0-9]|} in
  let run s =
    let cnt = ref 0 in
    let edits = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _mr, _ = Re_compat.search_forward re s !i in
         let mb = Re_compat.match_beginning _mr in
         let me = Re_compat.match_end _mr in
         (* Match shape: [0-9] [SPACE]+ (–|--) [0-9]. The leading digit is at
            mb; spaces start at mb+1; spaces end at the dash. Walk until the
            first non-space byte (the dash). *)
         let space_start = mb + 1 in
         let space_end = ref space_start in
         while !space_end < me && s.[!space_end] = ' ' do
           incr space_end
         done;
         if !space_end > space_start then
           edits :=
             Cst_edit.replace ~start_offset:space_start ~end_offset:!space_end
               ""
             :: !edits;
         incr cnt;
         i := me
       done
     with Not_found -> ());
    if !cnt > 0 then
      let fix = List.rev !edits in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-025" ~severity:Warning
             ~message:{|Space before en‑dash in number range|} ~count:!cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-025" ~severity:Warning
             ~message:{|Space before en‑dash in number range|} ~count:!cnt ~fix)
    else None
  in
  { id = "TYPO-025"; run; languages = [] }

(* TYPO-026: Wrong dash in page range — should use -- *)
let r_typo_026 : rule =
  let re = Re_compat.regexp {|[0-9]–[0-9]|} in
  let run s =
    let cnt = ref 0 in
    let edits = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _mr, _ = Re_compat.search_forward re s !i in
         let mb = Re_compat.match_beginning _mr in
         (* The en-dash (U+2013) is 3 UTF-8 bytes (E2 80 93). It sits at offset
            mb+1, between the two digits. Replace those 3 bytes with the LaTeX
            double-hyphen `--`. *)
         edits :=
           Cst_edit.replace ~start_offset:(mb + 1) ~end_offset:(mb + 4) "--"
           :: !edits;
         incr cnt;
         i := Re_compat.match_end _mr
       done
     with Not_found -> ());
    if !cnt > 0 then
      let fix = List.rev !edits in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-026" ~severity:Warning
             ~message:{|Wrong dash in page range – should use --|} ~count:!cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-026" ~severity:Warning
             ~message:{|Wrong dash in page range – should use --|} ~count:!cnt
             ~fix)
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

(* TYPO-028: Use of $$ display math delimiter. v27.0.20: fix producer that
   replaces each pair of unescaped `$$` with `\[…\]` (the LaTeX 2e idiomatic
   display-math form). Pairs are formed greedily from non-overlapping `$$` match
   offsets: the first becomes `\[`, the second becomes `\]`, and any leftover
   unpaired delimiter is left in place (rule still warns).

   Round-1 audit guards: 1. Odd-prior-backslash escape skip (matches v27.0.19
   TYPO-046 + v27.0.14 TYPO-032 + v27.0.8 TYPO-001): `\$$` parses as `\$`
   (escaped dollar) followed by `$` (open inline math), NOT a display-math
   delimiter. 2. Count semantic preserved from pre-v27.0.20 via `count_substring
   s "$$" / 2` so the differential output vs v27.0.19 is unchanged. The fix uses
   the more precise non-overlapping offsets, which can diverge on consecutive
   runs like `$$$` (3 chars: pre-v27.0.20 counted 1 pair via overlap;
   non-overlap gives 1 offset → no pair → no fix). For `$$$$` (4 chars) both
   views agree on 1 pair. *)
let r_typo_028 : rule =
  let needle = "$$" in
  let nlen = 2 in
  let is_escaped s pos =
    let n = ref 0 in
    let i = ref (pos - 1) in
    while !i >= 0 && s.[!i] = '\\' do
      incr n;
      decr i
    done;
    !n mod 2 = 1
  in
  let unescaped_offsets s =
    List.filter
      (fun off -> not (is_escaped s off))
      (find_all_non_overlapping s needle)
  in
  let rec pairs = function a :: b :: rest -> (a, b) :: pairs rest | _ -> [] in
  let run s =
    let cnt = count_substring s needle / 2 in
    if cnt > 0 then
      let pair_offsets = pairs (unescaped_offsets s) in
      let fix =
        List.concat_map
          (fun (open_off, close_off) ->
            [
              Cst_edit.replace ~start_offset:open_off
                ~end_offset:(open_off + nlen) "\\[";
              Cst_edit.replace ~start_offset:close_off
                ~end_offset:(close_off + nlen) "\\]";
            ])
          pair_offsets
      in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-028" ~severity:Error
             ~message:{|Use of ``$$'' display math delimiter|} ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-028" ~severity:Error
             ~message:{|Use of ``$$'' display math delimiter|} ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-028"; run; languages = [] }

(* TYPO-029: Non-breaking space after \ref missing *)
let r_typo_029 : rule =
  (* v27.0.12: math-aware fix producer. Pattern `\ref{X} y` (regular space
     between `}` and a letter) is rewritten to `\ref{X}~y`. Match shape (regex):
     `\ref{[^}]*} [a-zA-Z]`. The space sits at match_end - 2 (one byte before
     the trailing letter). Math-aware via find_math_ranges (defensive: \ref in
     math is unusual but skip). Message inlined per round-3 v27.0.6 pattern. *)
  let re = Re_compat.regexp {|\\ref{[^}]*} [a-zA-Z]|} in
  let collect_match_ends s =
    let rec loop i acc =
      try
        let mr, _ = Re_compat.search_forward re s i in
        let mend = Re_compat.match_end mr in
        loop mend (mend :: acc)
      with Not_found -> List.rev acc
    in
    loop 0 []
  in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let outside off = not (is_in_math_range math off) in
    List.filter_map
      (fun mend ->
        let space_off = mend - 2 in
        if outside space_off then
          Some
            (Cst_edit.replace ~start_offset:space_off
               ~end_offset:(space_off + 1) "~")
        else None)
      (collect_match_ends s)
  in
  let run s =
    let cnt = List.length (collect_match_ends s) in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-029" ~severity:Info
             ~message:{|Non‑breaking space after \ref missing|} ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-029" ~severity:Info
             ~message:{|Non‑breaking space after \ref missing|} ~count:cnt ~fix)
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

(* TYPO-032: Comma before \cite. v27.0.14: math-aware fix producer. Pattern `,[
   ]*\cite` (comma + zero-or-more spaces + \cite) matches a typographic
   anti-pattern; the fix deletes the comma (single-byte delete at match start)
   and preserves the spaces and \cite.

   Round-1 audit guard: skip matches where the comma is part of a `\,` thin-
   space control symbol — deleting the comma in `\,\cite` would corrupt it into
   `\\cite` (a line break followed by literal `cite` text). The check counts
   consecutive backslashes immediately before the comma; an odd count means the
   comma belongs to a `\,` control symbol and the match must be skipped from
   BOTH the count and fix offsets (otherwise the count would over-report and the
   audit's 0-differential invariant would fail).

   Math-aware via `find_math_ranges` on the fix offsets only; the count
   preserves the pre-v27.0.14 semantic for non-`\,` matches (no math filter on
   count) so the differential output vs v27.0.13 is unchanged for genuine
   anti-patterns. *)
let r_typo_032 : rule =
  let re = Re_compat.regexp {|,[ ]*\\cite|} in
  let is_thin_space_comma s pos =
    (* True iff `s.[pos]` is a comma that is part of `\,` — i.e. preceded by an
       odd number of backslashes (so the most recent backslash is unescaped and
       pairs with the comma). *)
    let n = ref 0 in
    let i = ref (pos - 1) in
    while !i >= 0 && s.[!i] = '\\' do
      incr n;
      decr i
    done;
    !n mod 2 = 1
  in
  let collect_offsets s =
    let rec loop i acc =
      try
        let mr, pos = Re_compat.search_forward re s i in
        let mend = Re_compat.match_end mr in
        let acc = if is_thin_space_comma s pos then acc else pos :: acc in
        loop mend acc
      with Not_found -> List.rev acc
    in
    loop 0 []
  in
  let fix_offsets s =
    let math = find_math_ranges s in
    List.filter (fun pos -> not (is_in_math_range math pos)) (collect_offsets s)
  in
  let mk_fix_edits offsets =
    List.map
      (fun pos -> Cst_edit.replace ~start_offset:pos ~end_offset:(pos + 1) "")
      offsets
  in
  let run s =
    let cnt = List.length (collect_offsets s) in
    if cnt > 0 then
      let fix = mk_fix_edits (fix_offsets s) in
      Some
        (mk_result_with_fix ~id:"TYPO-032" ~severity:Warning
           ~message:"Comma before \\cite" ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-032"; run; languages = [] }

(* TYPO-033: Abbreviation et.al without space. v26.3 §3 item E: fix replaces
   "et.al" with "et al.". *)
let r_typo_033 : rule =
  let message = "Abbreviation et.al without space" in
  (* P3 context-aware (token-aware variant): count + fix skip the exempt set
     (verbatim / comments / math / url) so `et.al` inside a code listing or
     comment is not flagged. *)
  let run s =
    let exempt = find_exempt_ranges s in
    let cnt = count_in_text exempt s "et.al" in
    if cnt > 0 then
      let fix = mk_replace_edits_exempt exempt s "et.al" "et al." in
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
  (* v27.0.11: math-aware fix producer. Each ` \footnote` occurrence outside
     math has the leading space deleted. Convention: footnote marks should
     attach directly to the preceding word with no space. Math-aware via
     find_math_ranges (footnote in math is unusual but skip defensively).
     Message inlined per round-3 v27.0.6 pattern. *)
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let outside off = not (is_in_math_range math off) in
    let offsets = find_all_non_overlapping s " \\footnote" in
    List.filter_map
      (fun off ->
        if outside off then
          Some (Cst_edit.replace ~start_offset:off ~end_offset:(off + 1) "")
        else None)
      offsets
  in
  let run s =
    let cnt = count_substring s " \\footnote" in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-034" ~severity:Info
             ~message:{|Spurious space before footnote command \footnote|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-034" ~severity:Info
             ~message:{|Spurious space before footnote command \footnote|}
             ~count:cnt ~fix)
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
  (* P3 context-aware (token-aware variant): count + fix skip the exempt set
     (verbatim / comments / math / url). Same `<space>,` target as TYPO-010's
     comma branch; both made context-aware together this batch. *)
  let run s =
    let exempt = find_exempt_ranges s in
    let cnt = count_in_text exempt s " ," in
    if cnt > 0 then
      let fix = mk_replace_edits_exempt exempt s " ," "," in
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
  (* v27.0.9: math-aware fix producer. Wraps each non-math email match with
     backslash-href-mailto-EMAIL-EMAIL. Uses find_math_ranges to skip math
     segments (emails in math are unusual but possible). Message inlined per
     round-3 v27.0.6 pattern. *)
  let re = Re_compat.regexp "[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]+" in
  let collect_matches s =
    let rec loop i acc =
      try
        let mr, pos = Re_compat.search_forward re s i in
        let mend = Re_compat.match_end mr in
        let email = String.sub s pos (mend - pos) in
        loop mend ((pos, mend, email) :: acc)
      with Not_found -> List.rev acc
    in
    loop 0 []
  in
  (* v27.0.10 round-1 audit refinement: replace prefix-byte check with proper
     \href{mailto:...}{...} range detection. The pre-v27.0.10 check used literal
     `mailto:` and `}{` prefixes which yielded: - false-positive: "Use
     mailto:alice@x.com" (literal text) skipped - false-negative:
     \foo{bar}{alice@x.com} treated as wrapped Both are now correctly handled by
     find_href_mailto_ranges, which scans for the literal \href{mailto: opener
     and walks to the matching }{...} closer. Email matches whose start offset
     falls within any returned range are skipped — the only emails that register
     as "already wrapped" are ones genuinely inside a complete
     \href{mailto:...}{...} construct. *)
  let find_href_mailto_ranges s =
    let n = String.length s in
    let opener = "\\href{mailto:" in
    let opener_len = String.length opener in
    let ranges = ref [] in
    let i = ref 0 in
    while !i + opener_len <= n do
      if String.sub s !i opener_len = opener then (
        (* Walk to closing } of URL slot, then expect {, then walk to closing }
           of display slot. *)
        let j = ref (!i + opener_len) in
        while !j < n && s.[!j] <> '}' do
          incr j
        done;
        if !j < n - 1 && s.[!j + 1] = '{' then (
          let k = ref (!j + 2) in
          while !k < n && s.[!k] <> '}' do
            incr k
          done;
          if !k < n then (
            ranges := (!i, !k + 1) :: !ranges;
            i := !k + 1)
          else incr i)
        else incr i)
      else incr i
    done;
    List.rev !ranges
  in
  let in_href_range ranges off =
    List.exists (fun (a, b) -> a <= off && off < b) ranges
  in
  let unwrapped_matches s =
    let math = find_math_ranges s in
    let href_ranges = find_href_mailto_ranges s in
    let outside_math off = not (is_in_math_range math off) in
    let outside_href off = not (in_href_range href_ranges off) in
    let matches = collect_matches s in
    List.filter
      (fun (start_offset, _, _) ->
        outside_math start_offset && outside_href start_offset)
      matches
  in
  let mk_fix_edits s =
    List.map
      (fun (start_offset, end_offset, email) ->
        Cst_edit.replace ~start_offset ~end_offset
          ("\\href{mailto:" ^ email ^ "}{" ^ email ^ "}"))
      (unwrapped_matches s)
  in
  let run s =
    (* v27.0.9 semantic shift: count is based on UNWRAPPED non-math matches (the
       rule's intent is "emails NOT in href"). Pre-v27.0.9 counted all email
       patterns including pre-wrapped ones, which caused the rule to fire on
       already-correct documents. *)
    let cnt = List.length (unwrapped_matches s) in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      Some
        (mk_result_with_fix ~id:"TYPO-038" ~severity:Info
           ~message:{|E‑mail address not in \href|} ~count:cnt ~fix)
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

(* TYPO-042: Multiple consecutive question marks. v27.0.15: math-aware fix
   producer mirroring TYPO-027 (`!!!` -> `!`). Collapse each maximal run of
   `??...?` to a single `?` via `find_consecutive_runs s '?' ~min_len:2`.
   Math-aware on fix offsets only; the count uses `count_substring s "??"`
   (overlapping semantics) so the differential output vs v27.0.14 is unchanged
   for non-math input. *)
let r_typo_042 : rule =
  let run s =
    let cnt = count_substring s "??" in
    if cnt > 0 then
      let math = find_math_ranges s in
      let runs = find_consecutive_runs s '?' ~min_len:2 in
      let fix_runs =
        List.filter
          (fun (start_offset, _) -> not (is_in_math_range math start_offset))
          runs
      in
      let fix =
        List.map
          (fun (start_offset, end_offset) ->
            Cst_edit.replace ~start_offset ~end_offset "?")
          fix_runs
      in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-042" ~severity:Info
             ~message:"Multiple consecutive question marks ??" ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-042" ~severity:Info
             ~message:"Multiple consecutive question marks ??" ~count:cnt ~fix)
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

(* TYPO-051: Figure space U+2009. v27.0.16: math-aware fix producer. Replace
   each U+2009 (3 bytes UTF-8: e2 80 89) outside math with `\thinspace{}` (12
   bytes ASCII; the trailing `{}` is an empty group that ensures unambiguous
   macro tokenization regardless of the byte that follows U+2009 — most commonly
   a letter, e.g. `5 m`, where bare `\thinspace` would parse as the undefined
   command `\thinspacem`).

   Math-aware on fix offsets only; the count uses count_substring of the UTF-8
   sequence (overlapping not relevant — needle is 3 bytes, no possible
   self-overlap with 1 occurrence) so the differential output vs v27.0.15 is
   unchanged for non-math input. *)
let r_typo_051 : rule =
  let needle = "\xe2\x80\x89" in
  let nlen = 3 in
  (* v27.0.56: leading-run filter — skip U+2009 positions that belong to a
     line-start leading run, delegating them to SPC-035 (which deletes the
     leading run rather than wrapping it). A `\thinspace{}` at line start would
     render as an opening thin-space which is not the author's intent; the
     delete is the correct fix. Count semantic unchanged (still counts every
     U+2009); only the fix-set shrinks at line-start positions. *)
  let in_leading_u2009_run s off =
    let i = ref off in
    while
      !i >= 3
      && Char.code s.[!i - 3] = 0xE2
      && Char.code s.[!i - 2] = 0x80
      && Char.code s.[!i - 1] = 0x89
    do
      i := !i - 3
    done;
    !i = 0 || (!i > 0 && s.[!i - 1] = '\n')
  in
  let run s =
    let cnt = count_substring s needle in
    if cnt > 0 then
      let math = find_math_ranges s in
      let offsets = find_all_non_overlapping s needle in
      let fix_offsets =
        List.filter
          (fun off ->
            (not (is_in_math_range math off))
            && not (in_leading_u2009_run s off))
          offsets
      in
      let fix =
        List.map
          (fun off ->
            Cst_edit.replace ~start_offset:off ~end_offset:(off + nlen)
              "\\thinspace{}")
          fix_offsets
      in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-051" ~severity:Warning
             ~message:{|Figure space U+2009 used instead of \thinspace macro|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-051" ~severity:Warning
             ~message:{|Figure space U+2009 used instead of \thinspace macro|}
             ~count:cnt ~fix)
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

(* Unicode leader dots U+22EF forbidden. v27.0.44: math-aware fix producer that
   replaces each U+22EF (`\xe2\x8b\xaf`, 3 bytes) with the macro `\dots` (5
   bytes ASCII) when the occurrence is OUTSIDE math context.

   In math, U+22EF is the Unicode name `MIDLINE HORIZONTAL ELLIPSIS` and could
   be deliberately typed as a Unicode-input-encoded equivalent of `\cdots`.
   Replacing it inside math with `\dots` would change the typographic intent
   (low dots vs centered dots), so the fix skips math regions via
   `find_math_ranges` (same shape as v27.0.7 TYPO-005).

   Count preserves the pre-v27.0.44 semantic: count every occurrence regardless
   of math context (the original rule didn't strip math). Fix offsets diverge:
   only non-math matches are rewritten. This mirrors the documented TYPO-002/003
   divergence pattern. Severity Warning preserved. *)
let r_typo_053 : rule =
  let needle = "\xe2\x8b\xaf" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let outside off = not (is_in_math_range math off) in
    let offsets = List.filter outside (find_all_non_overlapping s needle) in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 3) "\\dots")
      offsets
  in
  let run s =
    let cnt = count_substring s needle in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-053" ~severity:Warning
             ~message:{|Unicode ⋯ (U+22EF) leader forbidden; use \dots instead|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-053" ~severity:Warning
             ~message:{|Unicode ⋯ (U+22EF) leader forbidden; use \dots instead|}
             ~count:cnt ~fix)
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

(* Consecutive thin-spaces prohibited. v27.0.43: fix producer that collapses
   each `\,\,` (4 bytes) to a single `\,` (2 bytes). A double thin-space is
   always a typo — there is no LaTeX construct where the literal four-character
   sequence `\,\,` is the intended output (the standard spacing macros `\!`,
   `\,`, `\:`, `\;`, `\ `, `\quad`, `\qquad` are the tools for tunable spacing).
   Pure non-overlapping replace; no math filter needed (the issue is the same in
   math and text); no escape detection needed (`\,\,` as a token cannot itself
   be preceded by an odd backslash — `\\,\,` parses as `\\` + `,` + `\,`, which
   does not contain `\,\,` as a contiguous substring).

   Mirrors the v26.3 §3 TYPO-027 (`!!!` collapse) and TYPO-042 (`???` collapse)
   shape: detect contiguous runs, replace with the non-duplicated form. Here the
   run unit is the 2-byte `\,` token, so we use `count_substring` to count
   overlapping pairs (preserving the pre-v27.0.43 fire-rate semantic) and
   `find_all_non_overlapping` to emit non-overlapping replace edits at offsets
   that share no bytes. *)
let r_typo_055 : rule =
  let needle = "\\,\\," in
  let run s =
    let cnt = count_substring s needle in
    if cnt > 0 then
      let offsets = find_all_non_overlapping s needle in
      let fix =
        List.map
          (fun off ->
            Cst_edit.replace ~start_offset:off ~end_offset:(off + 4) "\\,")
          offsets
      in
      Some
        (mk_result_with_fix ~id:"TYPO-055" ~severity:Info
           ~message:{|Consecutive thin‑spaces (\,\,) prohibited; collapse|}
           ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-055"; run; languages = [] }

(* Missing thin-space before degree symbol *)
(* TYPO-057: Missing thin-space before °C/°F (or \si{\celsius}).

   v27.0.72: fix producer. Detects a digit immediately followed by the degree
   sign U+00B0 (`[0-9]°`, no separating space) and inserts a thin space `\,`
   between them, e.g. `5°C` → `5\,°C`. The fix is purely ADDITIVE (a single `\,`
   insertion), so it cannot delete or corrupt surrounding content; `\,` is valid
   in both text and math mode, so no math gating is needed. The count semantic
   is unchanged (same regex scan), so lint output is identical and the fix is
   purely additive. The degree sign begins at [match_beginning + 1] (the byte
   after the matched digit), so the thin space is inserted there. *)
let r_typo_057 : rule =
  let re = Re_compat.regexp "[0-9]\xc2\xb0" in
  let run s =
    let rec loop i cnt offs =
      try
        let _mr, _ = Re_compat.search_forward re s i in
        let mbeg = Re_compat.match_beginning _mr in
        loop (Re_compat.match_end _mr) (cnt + 1) (mbeg :: offs)
      with Not_found -> (cnt, List.rev offs)
    in
    let cnt, offs = loop 0 0 [] in
    if cnt > 0 then
      let fix =
        List.map (fun mbeg -> Cst_edit.insert ~at:(mbeg + 1) "\\,") offs
      in
      Some
        (mk_result_with_fix ~id:"TYPO-057" ~severity:Info
           ~message:{|Missing thin‑space before °C/°F or \si{\celsius}|}
           ~count:cnt ~fix)
    else None
  in
  { id = "TYPO-057"; run; languages = [] }

(* Unicode multiplication sign in text.

   v27.0.52: math-aware fix producer that replaces each U+00D7 (`\xc3\x97`, 2
   bytes UTF-8) OUTSIDE math with `$\times$` (8 bytes ASCII), wrapping the
   character in inline math per the spec's "prefer \times via math mode"
   guidance. Same text-only negative-filter shape as v27.0.44 CHAR-019 / v27.0.7
   TYPO-005 — count semantic preserved via [strip_math_segments]; fix-set is the
   corrective action and may be smaller than count when pathological
   math-stripper / range-finder edge cases diverge.

   Severity Info preserved. *)
let r_typo_061 : rule =
  let needle = "\xc3\x97" in
  let mk_fix_edits s =
    let math = find_math_ranges s in
    let outside off = not (is_in_math_range math off) in
    let offsets = List.filter outside (find_all_non_overlapping s needle) in
    List.map
      (fun off ->
        Cst_edit.replace ~start_offset:off ~end_offset:(off + 2) "$\\times$")
      offsets
  in
  let run s =
    let stripped = strip_math_segments s in
    let cnt = count_substring stripped needle in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-061" ~severity:Info
             ~message:
               {|Unicode × (U+00D7) in text; prefer \times via math mode|}
             ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-061" ~severity:Info
             ~message:
               {|Unicode × (U+00D7) in text; prefer \times via math mode|}
             ~count:cnt ~fix)
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
  (* v27.0.13: math-aware fix producer. Wraps each unwrapped non-math URL match
     with \url{URL}. Skip URLs already inside \url{} or the URL slot of \href{}.
     Math-aware via find_math_ranges (URLs in math are extremely unusual but
     skip defensively). Message inlined per round-3 v27.0.6 pattern. *)
  let re = Re_compat.regexp "https?://[^ \t\n}]+" in
  let collect_matches s =
    let rec loop i acc =
      try
        let mr, pos = Re_compat.search_forward re s i in
        let mend = Re_compat.match_end mr in
        let url = String.sub s pos (mend - pos) in
        loop mend ((pos, mend, url) :: acc)
      with Not_found -> List.rev acc
    in
    loop 0 []
  in
  let already_wrapped s start_offset =
    let url_prefix = "\\url{" in
    let up_len = String.length url_prefix in
    let href_prefix = "\\href{" in
    let hp_len = String.length href_prefix in
    start_offset >= up_len
    && String.sub s (start_offset - up_len) up_len = url_prefix
    || start_offset >= hp_len
       && String.sub s (start_offset - hp_len) hp_len = href_prefix
  in
  let unwrapped_matches s =
    let math = find_math_ranges s in
    let outside_math off = not (is_in_math_range math off) in
    List.filter
      (fun (start_offset, _, _) ->
        outside_math start_offset && not (already_wrapped s start_offset))
      (collect_matches s)
  in
  (* Round-2 audit fix: the URL regex `https?://[^ \t\n}]+` is permissive on
     trailing punctuation (period, comma, semicolon, colon, bang, right-paren),
     so a URL followed by a sentence-ending mark would have the punctuation
     absorbed into the wrap (e.g. `Visit https://x.com.` would become `Visit
     \url{https://x.com.}` with the period as part of the URL). Trim trailing
     punctuation from the fix span; `?` is intentionally NOT trimmed because it
     commonly starts a URL query string. *)
  let trim_trailing_punct s start_offset end_offset =
    let punct = [ ','; '.'; ';'; ':'; '!'; ')' ] in
    let e = ref end_offset in
    while !e > start_offset && List.mem s.[!e - 1] punct do
      decr e
    done;
    !e
  in
  let mk_fix_edits s =
    List.map
      (fun (start_offset, end_offset, _url) ->
        let trimmed_end = trim_trailing_punct s start_offset end_offset in
        let trimmed_url =
          String.sub s start_offset (trimmed_end - start_offset)
        in
        Cst_edit.replace ~start_offset ~end_offset:trimmed_end
          ("\\url{" ^ trimmed_url ^ "}"))
      (unwrapped_matches s)
  in
  let run s =
    let cnt = List.length (unwrapped_matches s) in
    if cnt > 0 then
      let fix = mk_fix_edits s in
      Some
        (mk_result_with_fix ~id:"TYPO-039" ~severity:Info
           ~message:"URL split across lines without \\url{}" ~count:cnt ~fix)
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

(* TYPO-046: Use of \begin{math}…\end{math} instead of $…$. v27.0.19: fix
   producer that replaces the verbose math environment delimiters with the
   compact dollar form. Each `\begin{math}` (12 bytes) becomes `$` (1 byte);
   each `\end{math}` (10 bytes) becomes `$` (1 byte) — the rewrite engine sorts
   edits before applying, so emit order is irrelevant.

   Round-1 audit guard: skip matches where the leading `\` is preceded by an odd
   number of backslashes — `\\begin{math}` parses as line-break (\\) followed by
   literal `begin{math}` text, NOT a math environment, and the naive fix would
   corrupt this into `\$` (escaped dollar). Same gotcha as v27.0.14 TYPO-032
   thin-space comma + v27.0.8 TYPO-001 umlaut command. The check counts
   consecutive backslashes immediately before the match start; an odd count
   means the match is skipped from BOTH count AND fix offsets to keep behaviour
   internally consistent. *)
let r_typo_046 : rule =
  let begin_needle = "\\begin{math}" in
  let end_needle = "\\end{math}" in
  let blen = String.length begin_needle in
  let elen = String.length end_needle in
  let is_escaped_command s pos =
    let n = ref 0 in
    let i = ref (pos - 1) in
    while !i >= 0 && s.[!i] = '\\' do
      incr n;
      decr i
    done;
    !n mod 2 = 1
  in
  let collect_unescaped s needle =
    List.filter
      (fun off -> not (is_escaped_command s off))
      (find_all_non_overlapping s needle)
  in
  let run s =
    let begin_offsets = collect_unescaped s begin_needle in
    let end_offsets = collect_unescaped s end_needle in
    let cnt = List.length begin_offsets + List.length end_offsets in
    if cnt > 0 then (
      (* Round-1 ultrathink audit: detect adjacent begin/end pairs (empty math
         env, no content between the delimiters). Naive replacement of each
         delimiter with `$` would yield `$$` — the display-math delimiter that
         TYPO-028 warns against, AND it would consume following source as math
         content until the next `$$`, CORRUPTING the document. Emit a single
         delete edit covering both delimiters instead; an empty math env renders
         to nothing in LaTeX, so deletion is semantically equivalent. Only the
         exact `\begin{math}\end{math}` (no whitespace between) hits this case —
         `\begin{math} \end{math}` (single space content) falls through to the
         normal lone-replacement path and yields a valid (if pointless) `$ $`
         math env. *)
      (* v27.0.32: Hashtbl-based pair detection — O(B+E) instead of O(B×E). The
         pre-v27.0.32 implementation used `List.mem (b+blen) end_offsets` per
         begin (O(E) each) plus `List.mem e paired_end_set` per end (O(P) each),
         giving O(B×E + E×P) ≈ O(B×E) total. Hashtbl lookups are O(1), so the
         rewrite is O(B+E) total — protects live-editing performance on
         documents with many math envs. Mirror of the v27.0.31 ENC-018
         forward-pass perf fix philosophy. *)
      let end_set = Hashtbl.create (List.length end_offsets) in
      List.iter (fun e -> Hashtbl.replace end_set e ()) end_offsets;
      let is_paired_begin b = Hashtbl.mem end_set (b + blen) in
      let paired_begins = List.filter is_paired_begin begin_offsets in
      let paired_end_set = Hashtbl.create (List.length paired_begins) in
      List.iter
        (fun b -> Hashtbl.replace paired_end_set (b + blen) ())
        paired_begins;
      let lone_begins =
        List.filter (fun b -> not (is_paired_begin b)) begin_offsets
      in
      let lone_ends =
        List.filter (fun e -> not (Hashtbl.mem paired_end_set e)) end_offsets
      in
      let fix =
        List.map
          (fun b ->
            Cst_edit.replace ~start_offset:b ~end_offset:(b + blen + elen) "")
          paired_begins
        @ List.map
            (fun off ->
              Cst_edit.replace ~start_offset:off ~end_offset:(off + blen) "$")
            lone_begins
        @ List.map
            (fun off ->
              Cst_edit.replace ~start_offset:off ~end_offset:(off + elen) "$")
            lone_ends
      in
      Some
        (mk_result_with_fix ~id:"TYPO-046" ~severity:Info
           ~message:"Use of $begin:math:text$ … $end:math:text$ instead of $…$"
           ~count:cnt ~fix))
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

(* TYPO-049: Space after opening quote. v27.0.17: math-aware fix producer.
   Pattern U+201C+space (4 bytes: e2 80 9c 20) or U+2018+space (4 bytes: e2 80
   98 20) → delete the trailing ASCII space (1-byte delete at match_offset+3);
   the opening quote itself is preserved.

   Math-aware on fix offsets only; the count uses the same dual
   `count_substring` sum as pre-v27.0.17 so the differential output vs v27.0.16
   is unchanged. Multiple-spaces case (`“ abc`) only deletes the FIRST space —
   TYPO-018 handles double-space collapse on what remains. *)
let r_typo_049 : rule =
  let ldquo_sp = "\xe2\x80\x9c " in
  let lsquo_sp = "\xe2\x80\x98 " in
  let run s =
    let cnt = count_substring s ldquo_sp + count_substring s lsquo_sp in
    if cnt > 0 then
      let math = find_math_ranges s in
      let offsets =
        find_all_non_overlapping s ldquo_sp
        @ find_all_non_overlapping s lsquo_sp
      in
      let fix_offsets =
        List.filter (fun off -> not (is_in_math_range math off)) offsets
      in
      (* The space byte to delete sits at offset+3 (after the 3-byte quote). *)
      let fix =
        List.map
          (fun off ->
            let space_off = off + 3 in
            Cst_edit.replace ~start_offset:space_off ~end_offset:(space_off + 1)
              "")
          fix_offsets
      in
      if fix = [] then
        Some
          (mk_result ~id:"TYPO-049" ~severity:Info
             ~message:"Space after opening quote" ~count:cnt)
      else
        Some
          (mk_result_with_fix ~id:"TYPO-049" ~severity:Info
             ~message:"Space after opening quote" ~count:cnt ~fix)
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
