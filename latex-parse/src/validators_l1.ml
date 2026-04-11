open Validators_common

(* L1 modernization and expansion checks (using post-commands heuristics) *)
include Validators_l1_math

let l1_mod_001_rule : rule =
  let run s =
    (* MOD-001: Legacy font commands present; prefer modern commands *)
    let names = extract_command_names s in
    let legacy = [ "bf"; "it"; "tt"; "rm"; "sl"; "sf" ] in
    let cnt =
      List.fold_left
        (fun acc n -> if List.exists (( = ) n) legacy then acc + 1 else acc)
        0 names
    in
    if cnt > 0 then
      Some
        {
          id = "MOD-001";
          severity = Warning;
          message =
            "Legacy font commands (\\bf/\\it/...) present; prefer \
             \\textbf/\\emph";
          count = cnt;
        }
    else None
  in
  { id = "MOD-001"; run; languages = [] }

let l1_exp_001_rule : rule =
  let run s =
    (* EXP-001: Incomplete expansion — strip targets still present
       post-expansion *)
    let names = extract_command_names s in
    let targets = [ "textbf"; "emph"; "section" ] in
    let cnt =
      List.fold_left
        (fun acc n -> if List.exists (( = ) n) targets then acc + 1 else acc)
        0 names
    in
    if cnt > 0 then
      Some
        {
          id = "EXP-001";
          severity = Info;
          message =
            "Incomplete expansion: catalogue commands remain post-expansion";
          count = cnt;
        }
    else None
  in
  { id = "EXP-001"; run; languages = [] }

let l1_mod_002_rule : rule =
  let run s =
    (* MOD-002: Mixed legacy and modern bold commands in same paragraph *)
    let legacy = [ "bf" ] and modern = [ "textbf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-002";
          severity = Warning;
          message = "Mixed legacy and modern bold commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-002"; run; languages = [] }

let l1_mod_003_rule : rule =
  let run s =
    (* MOD-003: Mixed legacy and modern italic commands in same paragraph *)
    let legacy = [ "it" ] and modern = [ "emph"; "textit" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-003";
          severity = Warning;
          message = "Mixed legacy and modern italic commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-003"; run; languages = [] }

let l1_mod_004_rule : rule =
  let run s =
    (* MOD-004: Mixed legacy and modern roman family commands in same
       paragraph *)
    let legacy = [ "rm" ] and modern = [ "textrm" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-004";
          severity = Warning;
          message = "Mixed legacy and modern roman commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-004"; run; languages = [] }

let l1_mod_005_rule : rule =
  let run s =
    (* MOD-005: Mixed legacy and modern typewriter commands in same paragraph *)
    let legacy = [ "tt" ] and modern = [ "texttt" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-005";
          severity = Warning;
          message =
            "Mixed legacy and modern typewriter commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-005"; run; languages = [] }

let l1_mod_006_rule : rule =
  let run s =
    (* MOD-006: Mixed legacy and modern sans-serif commands in same paragraph *)
    let legacy = [ "sf" ] and modern = [ "textsf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-006";
          severity = Warning;
          message =
            "Mixed legacy and modern sans-serif commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-006"; run; languages = [] }

let l1_mod_007_rule : rule =
  let run s =
    (* MOD-007: Mixed legacy and modern small-caps commands in same paragraph *)
    let legacy = [ "sc" ] and modern = [ "textsc" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-007";
          severity = Warning;
          message =
            "Mixed legacy and modern small-caps commands in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-007"; run; languages = [] }

let l1_mod_008_rule : rule =
  let run s =
    (* MOD-008: Mixed NFSS series switch vs inline macro in same paragraph
       (bfseries vs textbf) *)
    let legacy = [ "bfseries" ] and modern = [ "textbf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-008";
          severity = Warning;
          message = "Mixed NFSS bfseries and inline \\textbf in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-008"; run; languages = [] }

let l1_mod_009_rule : rule =
  let run s =
    (* MOD-009: Mixed NFSS shape switch vs inline macro in same paragraph
       (itshape vs textit/emph) *)
    let legacy = [ "itshape" ] and modern = [ "textit"; "emph" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-009";
          severity = Warning;
          message =
            "Mixed NFSS itshape and inline \\textit/\\emph in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-009"; run; languages = [] }

let l1_mod_010_rule : rule =
  let run s =
    (* MOD-010: Mixed NFSS family switch vs inline macro (sffamily vs textsf) *)
    let legacy = [ "sffamily" ] and modern = [ "textsf" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-010";
          severity = Warning;
          message = "Mixed NFSS sffamily and inline \\textsf in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-010"; run; languages = [] }

let l1_mod_011_rule : rule =
  let run s =
    (* MOD-011: Mixed NFSS family switch vs inline macro (ttfamily vs texttt) *)
    let legacy = [ "ttfamily" ] and modern = [ "texttt" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-011";
          severity = Warning;
          message = "Mixed NFSS ttfamily and inline \\texttt in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-011"; run; languages = [] }

let l1_mod_012_rule : rule =
  let run s =
    (* MOD-012: Mixed NFSS family switch vs inline macro (rmfamily vs textrm) *)
    let legacy = [ "rmfamily" ] and modern = [ "textrm" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-012";
          severity = Warning;
          message = "Mixed NFSS rmfamily and inline \\textrm in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-012"; run; languages = [] }

let l1_mod_013_rule : rule =
  let run s =
    (* MOD-013: Mixed NFSS shape switch vs inline macro (scshape vs textsc) *)
    let legacy = [ "scshape" ] and modern = [ "textsc" ] in
    if has_mixed_in_paragraphs s ~legacy ~modern then
      Some
        {
          id = "MOD-013";
          severity = Warning;
          message = "Mixed NFSS scshape and inline \\textsc in same paragraph";
          count = 1;
        }
    else None
  in
  { id = "MOD-013"; run; languages = [] }

let l1_mod_020_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "bfseries" ] [ "textbf" ] then
      Some
        {
          id = "MOD-020";
          severity = Info;
          message =
            "Global mix: NFSS bfseries and inline \\textbf appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-020"; run; languages = [] }

let l1_mod_021_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "itshape" ] [ "textit"; "emph" ] then
      Some
        {
          id = "MOD-021";
          severity = Info;
          message =
            "Global mix: NFSS itshape and inline \\textit/\\emph appear in \
             different paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-021"; run; languages = [] }

let l1_mod_022_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "rmfamily" ] [ "textrm" ] then
      Some
        {
          id = "MOD-022";
          severity = Info;
          message =
            "Global mix: NFSS rmfamily and inline \\textrm appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-022"; run; languages = [] }

let l1_mod_023_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "sffamily" ] [ "textsf" ] then
      Some
        {
          id = "MOD-023";
          severity = Info;
          message =
            "Global mix: NFSS sffamily and inline \\textsf appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-023"; run; languages = [] }

let l1_mod_024_rule : rule =
  let run _s =
    let names = extract_command_names _s in
    if has_global_mixing names [ "ttfamily" ] [ "texttt" ] then
      Some
        {
          id = "MOD-024";
          severity = Info;
          message =
            "Global mix: NFSS ttfamily and inline \\texttt appear in different \
             paragraphs";
          count = 1;
        }
    else None
  in
  { id = "MOD-024"; run; languages = [] }

(* ── DELIM rules: delimiter matching (L1 — operate on expanded text) ── *)

(* DELIM-001: Unmatched delimiters { } after expansion. Count opening vs closing
   braces, ignoring escaped \{ and \}. *)
let l1_delim_001_rule : rule =
  let run s =
    let n = String.length s in
    let opens = ref 0 in
    let closes = ref 0 in
    let i = ref 0 in
    while !i < n do
      let c = s.[!i] in
      if c = '\\' && !i + 1 < n then (* skip escaped characters *)
        i := !i + 2
      else if c = '{' then (
        incr opens;
        incr i)
      else if c = '}' then (
        incr closes;
        incr i)
      else incr i
    done;
    let imbalance = abs (!opens - !closes) in
    if imbalance > 0 then
      Some
        {
          id = "DELIM-001";
          severity = Error;
          message = "Unmatched delimiters { … } after macro expansion";
          count = imbalance;
        }
    else None
  in
  { id = "DELIM-001"; run; languages = [] }

(* DELIM-002: Extra closing } detected. Scan left-to-right tracking brace depth;
   if depth ever goes negative, count those positions. *)
let l1_delim_002_rule : rule =
  let run s =
    let n = String.length s in
    let depth = ref 0 in
    let cnt = ref 0 in
    let i = ref 0 in
    while !i < n do
      let c = s.[!i] in
      if c = '\\' && !i + 1 < n then i := !i + 2
      else if c = '{' then (
        incr depth;
        incr i)
      else if c = '}' then (
        decr depth;
        if !depth < 0 then (
          incr cnt;
          depth := 0);
        incr i)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-002";
          severity = Error;
          message = "Extra closing } detected";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-002"; run; languages = [] }

(* DELIM-003: Unmatched \left without \right in math mode *)
let l1_delim_003_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let lefts = count_substring seg "\\left" in
        let rights = count_substring seg "\\right" in
        if lefts > rights then cnt := !cnt + (lefts - rights))
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-003";
          severity = Error;
          message = "Unmatched \\left without \\right";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-003"; run; languages = [] }

(* DELIM-004: Unmatched \right without \left in math mode *)
let l1_delim_004_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let lefts = count_substring seg "\\left" in
        let rights = count_substring seg "\\right" in
        if rights > lefts then cnt := !cnt + (rights - lefts))
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-004";
          severity = Error;
          message = "Unmatched \\right without \\left";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-004"; run; languages = [] }

(* DELIM-005: Mismatched parenthesis sizing (\big vs \Bigg) — detect \bigl/\bigr
   paired with \Biggl/\Biggr or similar size mismatches. *)
let l1_delim_005_rule : rule =
  let size_of s =
    if count_substring s "\\Bigg" > 0 then 4
    else if count_substring s "\\bigg" > 0 then 3
    else if count_substring s "\\Big" > 0 then 2
    else if count_substring s "\\big" > 0 then 1
    else 0
  in
  let re_left = Str.regexp {|\\left|} in
  let re_right = Str.regexp {|\\right|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Look for \left...\right pairs and check if sizing commands within
           differ *)
        let lefts = ref [] and rights = ref [] in
        let i = ref 0 in
        (try
           while true do
             let p = Str.search_forward re_left seg !i in
             lefts := p :: !lefts;
             i := p + 5
           done
         with Not_found -> ());
        i := 0;
        (try
           while true do
             let p = Str.search_forward re_right seg !i in
             rights := p :: !rights;
             i := p + 6
           done
         with Not_found -> ());
        (* For each left-right pair, check sizing around them *)
        let left_list = List.rev !lefts and right_list = List.rev !rights in
        let pairs = min (List.length left_list) (List.length right_list) in
        let ll = Array.of_list left_list and rl = Array.of_list right_list in
        for k = 0 to pairs - 1 do
          let lp = ll.(k) and rp = rl.(k) in
          (* Check context around each delimiter for sizing commands *)
          let l_ctx = String.sub seg (max 0 (lp - 10)) (min 10 (max 0 lp)) in
          let r_ctx = String.sub seg (max 0 (rp - 10)) (min 10 (max 0 rp)) in
          let l_size = size_of l_ctx and r_size = size_of r_ctx in
          if l_size > 0 && r_size > 0 && l_size <> r_size then incr cnt
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-005";
          severity = Info;
          message = {|Mismatched parenthesis sizing (\big vs \Bigg)|};
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-005"; run; languages = [] }

(* DELIM-006: \big delimiters used outside display math — detect \big, \bigl,
   \bigr etc. in inline math ($...$, \(...\)) rather than display math. *)
let l1_delim_006_rule : rule =
  let re_big =
    Str.regexp {|\\[Bb]ig[lrmg]?[^a-zA-Z]\|\\[Bb]igg[lrmg]?[^a-zA-Z]|}
  in
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    (* Scan for inline math contexts and look for \big within them *)
    let starts_with prefix idx =
      let plen = String.length prefix in
      idx + plen <= len && String.sub s idx plen = prefix
    in
    let is_escaped idx = idx > 0 && s.[idx - 1] = '\\' in
    let i = ref 0 in
    while !i < len do
      (* Inline math: $...$ (not $$) *)
      if
        (not (is_escaped !i))
        && s.[!i] = '$'
        && (!i + 1 >= len || s.[!i + 1] <> '$')
      then (
        let start = !i + 1 in
        let j = ref start in
        while
          !j < len
          && not
               ((not (is_escaped !j))
               && s.[!j] = '$'
               && (!j + 1 >= len || s.[!j + 1] <> '$'))
        do
          incr j
        done;
        if !j < len then (
          let inline_seg = String.sub s start (!j - start) in
          let k = ref 0 in
          (try
             while true do
               let _ = Str.search_forward re_big inline_seg !k in
               incr cnt;
               k := Str.match_end ()
             done
           with Not_found -> ());
          i := !j + 1)
        else i := !i + 1)
      else if (not (is_escaped !i)) && starts_with "\\(" !i then (
        let start = !i + 2 in
        let j = ref start in
        while
          !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\)" !j)
        do
          incr j
        done;
        if !j < len - 1 then (
          let inline_seg = String.sub s start (!j - start) in
          let k = ref 0 in
          (try
             while true do
               let _ = Str.search_forward re_big inline_seg !k in
               incr cnt;
               k := Str.match_end ()
             done
           with Not_found -> ());
          i := !j + 2)
        else i := !i + 1)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-006";
          severity = Info;
          message = {|\big delimiters used outside display math|};
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-006"; run; languages = [] }

(* DELIM-007: Angle bracket \langle without matching \rangle in math *)
let l1_delim_007_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let langles = count_substring seg "\\langle" in
        let rangles = count_substring seg "\\rangle" in
        let diff = abs (langles - rangles) in
        if diff > 0 then cnt := !cnt + diff)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-007";
          severity = Error;
          message = {|Angle bracket \langle without matching \rangle|};
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-007"; run; languages = [] }

(* DELIM-008: Empty \left. ... \right. pair — redundant invisible delimiters *)
let l1_delim_008_rule : rule =
  let re = Str.regexp "\\\\left\\.[ \t\n]*\\\\right\\." in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _ = Str.search_forward re seg !i in
            incr cnt;
            i := Str.match_end ()
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-008";
          severity = Info;
          message = {|Empty \left. … \right. pair — redundant|};
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-008"; run; languages = [] }

(* DELIM-009: Nested delimiter type mismatch — e.g. { ... ( ... ) ... } where
   brace group contains parenthesized expression or vice versa in math *)
let l1_delim_009_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let stack = Stack.create () in
        let i = ref 0 in
        while !i < n do
          let c = seg.[!i] in
          if c = '\\' && !i + 1 < n then i := !i + 2
          else if c = '{' || c = '(' || c = '[' then (
            Stack.push c stack;
            incr i)
          else if c = '}' || c = ')' || c = ']' then (
            let expected = match c with '}' -> '{' | ')' -> '(' | _ -> '[' in
            if (not (Stack.is_empty stack)) && Stack.top stack <> expected then
              incr cnt;
            if not (Stack.is_empty stack) then ignore (Stack.pop stack);
            incr i)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-009";
          severity = Warning;
          message = "Nested delimiters: { … ( … ) … }";
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-009"; run; languages = [] }

(* DELIM-010: Display math uses \big instead of \Big — in display math contexts,
   convention is to use capital sizing commands *)
let l1_delim_010_rule : rule =
  let re_small_big = Str.regexp {|\\big[lrmg]?[^a-zA-Z]|} in
  let run s =
    let len = String.length s in
    let cnt = ref 0 in
    let starts_with prefix idx =
      let plen = String.length prefix in
      idx + plen <= len && String.sub s idx plen = prefix
    in
    let is_escaped idx = idx > 0 && s.[idx - 1] = '\\' in
    let math_envs =
      [
        "equation";
        "equation*";
        "align";
        "align*";
        "gather";
        "gather*";
        "multline";
        "multline*";
        "eqnarray";
        "displaymath";
      ]
    in
    (* Check \[...\] display math *)
    let i = ref 0 in
    while !i < len do
      if (not (is_escaped !i)) && starts_with "\\[" !i then (
        let start = !i + 2 in
        let j = ref start in
        while
          !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\]" !j)
        do
          incr j
        done;
        if !j < len - 1 then (
          let seg = String.sub s start (!j - start) in
          let k = ref 0 in
          (try
             while true do
               let _ = Str.search_forward re_small_big seg !k in
               incr cnt;
               k := Str.match_end ()
             done
           with Not_found -> ());
          i := !j + 2)
        else i := !i + 1)
      else incr i
    done;
    (* Check display math environments *)
    List.iter
      (fun env ->
        let blocks = extract_env_blocks env s in
        List.iter
          (fun blk ->
            let k = ref 0 in
            try
              while true do
                let _ = Str.search_forward re_small_big blk !k in
                incr cnt;
                k := Str.match_end ()
              done
            with Not_found -> ())
          blocks)
      math_envs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-010";
          severity = Info;
          message = {|Display math uses \big instead of \Big|};
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-010"; run; languages = [] }

(* DELIM-011: \middle delimiter used without \left...\right pair *)
let l1_delim_011_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let middles = count_substring seg "\\middle" in
        if middles > 0 then
          (* Check if there are sufficient \left..\right pairs *)
          let lefts = count_substring seg "\\left" in
          let rights = count_substring seg "\\right" in
          let pairs = min lefts rights in
          if middles > 0 && pairs = 0 then cnt := !cnt + middles)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "DELIM-011";
          severity = Warning;
          message = {|\middle delimiter used without symmetric pair|};
          count = !cnt;
        }
    else None
  in
  { id = "DELIM-011"; run; languages = [] }

(* ═══════════════════════════════════════════════════════════════════════════
   SCRIPT family — L1 subscript / superscript validators SCRIPT-001 through
   SCRIPT-022
   ═══════════════════════════════════════════════════════════════════════════ *)

(* SCRIPT-001: Multi-char subscript without braces — e.g. _ab where the
   subscript has 2+ chars without { } *)
let l1_script_001_rule : rule =
  (* Match _X where X is 2+ alphanumeric chars not wrapped in braces *)
  let re = Str.regexp {|_\([A-Za-z0-9][A-Za-z0-9]+\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            (* Make sure it's not _{ ... } — check char before match group *)
            if pos + 1 < n && seg.[pos + 1] <> '{' then incr cnt;
            i := Str.match_end ()
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-001";
          severity = Warning;
          message = "Multi‑char subscript without braces";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-001"; run; languages = [] }

(* SCRIPT-002: Superscript dash typed as unicode non-breaking hyphen U+2011
   instead of \textsuperscript{--} *)
let l1_script_002_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          (* Check for ^ followed by U+2011 (non-breaking hyphen: \xe2\x80\x91)
             or U+2010 (hyphen: \xe2\x80\x90) *)
          if
            seg.[!i] = '^'
            && !i + 3 < n
            && seg.[!i + 1] = '\xe2'
            && seg.[!i + 2] = '\x80'
            && (seg.[!i + 3] = '\x91' || seg.[!i + 3] = '\x90')
          then (
            incr cnt;
            i := !i + 4)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-002";
          severity = Info;
          message = {|Superscript dash typed ‘‑’ not \textsuperscript{--}|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-002"; run; languages = [] }

(* SCRIPT-003: Comma-separated superscripts lack braces — e.g. ^a,b instead of
   ^{a,b} *)
let l1_script_003_rule : rule =
  let re = Str.regexp {|\^\([A-Za-z0-9],[A-Za-z0-9,]+\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-003";
          severity = Warning;
          message = "Comma‑separated superscripts lack braces";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-003"; run; languages = [] }

(* SCRIPT-004: Subscript after prime notation mis-ordered — e.g. f'_i instead of
   f_i' *)
let l1_script_004_rule : rule =
  let re = Str.regexp {|''+_\|'_|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-004";
          severity = Info;
          message = "Subscript after prime notation mis‑ordered";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-004"; run; languages = [] }

(* SCRIPT-005: Superscript uses letter l instead of \ell *)
let l1_script_005_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i < n do
          if seg.[!i] = '^' then
            let j = !i + 1 in
            if j < n then
              if seg.[j] = 'l' then (
                (* Make sure next char is not alphanumeric (standalone l) *)
                let after = j + 1 in
                let is_end =
                  after >= n
                  ||
                  let c = seg.[after] in
                  not
                    ((c >= 'a' && c <= 'z')
                    || (c >= 'A' && c <= 'Z')
                    || (c >= '0' && c <= '9'))
                in
                if is_end then incr cnt;
                i := after)
              else if seg.[j] = '{' then (
                (* check for ^{l} *)
                if j + 2 < n && seg.[j + 1] = 'l' && seg.[j + 2] = '}' then
                  incr cnt;
                i := j + 1)
              else i := j + 1
            else i := j + 1
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-005";
          severity = Info;
          message = {|Superscript uses letter l instead of \ell|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-005"; run; languages = [] }

(* SCRIPT-006: Degree symbol typed ° (U+00B0) instead of ^\circ in math *)
let l1_script_006_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* U+00B0 = \xc2\xb0 in UTF-8 *)
        cnt := !cnt + count_substring seg "\xc2\xb0")
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-006";
          severity = Info;
          message = {|Degree symbol typed ° instead of ^\circ|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-006"; run; languages = [] }

(* SCRIPT-007: Subscript text not wrapped in \text{} — e.g. x_{max} where "max"
   is a word (3+ alpha chars) without \text *)
let l1_script_007_rule : rule =
  let re = Str.regexp {|_{\([A-Za-z][A-Za-z][A-Za-z][A-Za-z]*\)}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            let matched = Str.matched_group 1 seg in
            let next_i = Str.match_end () in
            (* Exclude common math abbreviations *)
            let is_operator =
              List.mem matched
                [
                  "min";
                  "max";
                  "lim";
                  "inf";
                  "sup";
                  "det";
                  "dim";
                  "ker";
                  "log";
                  "exp";
                  "sin";
                  "cos";
                  "tan";
                  "arg";
                  "deg";
                  "gcd";
                  "hom";
                  "mod";
                  "Pr";
                ]
            in
            (if not is_operator then
               (* Check prefix for \text{, \mathrm{, \operatorname{ using string
                  operations (not Str) to avoid clobbering global match state *)
               let prefix_start = max 0 (pos - 16) in
               let prefix =
                 String.sub seg prefix_start (pos - prefix_start + 2)
               in
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
          id = "SCRIPT-007";
          severity = Warning;
          message = {|Subscript text not wrapped in \text{}|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-007"; run; languages = [] }

(* SCRIPT-008: Chemical formula lacks \mathrm{} in subscript — e.g. $H_2O$ vs
   $\mathrm{H}_2\mathrm{O}$ — detects element+subscript digit pattern outside
   \mathrm{} or \ce{} *)
let l1_script_008_rule : rule =
  (* Pattern: uppercase letter optionally followed by lowercase, then _digit
     e.g. H_2, Na_2, O_2 — these look like chemical formulas *)
  let re = Str.regexp {|\([A-Z][a-z]?\)_\([0-9]+\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Skip if inside \ce{} or \mathrm{} context *)
        if
          count_substring seg "\\ce{" = 0 && count_substring seg "\\mathrm{" = 0
        then cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-008";
          severity = Info;
          message = {|Chemical formula lacks \mathrm{} in subscript|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-008"; run; languages = [] }

(* SCRIPT-009: Isotope superscript mass number missing — e.g. ^{}_{Z}X or just
   _ZX without a mass number superscript *)
let l1_script_009_rule : rule =
  (* Detect: ^{}_ or ^{ }_ pattern indicating empty mass number *)
  let re = Str.regexp {|\^{[ ]*}_{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-009";
          severity = Info;
          message = "Isotope superscript mass number missing";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-009"; run; languages = [] }

(* SCRIPT-010: Use of \limits on inline operator — \limits in inline math
   ($...$, \(...\)) forces display-style limits *)
let l1_script_010_rule : rule =
  let re_limits = Str.regexp {|\\limits|} in
  let run s =
    let inline_segs = extract_inline_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_re_matches re_limits seg)
      inline_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-010";
          severity = Info;
          message = {|Use of \limits on inline operator|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-010"; run; languages = [] }

(* SCRIPT-011: Nested superscript three levels deep — e.g. x^{a^{b^{c}}} *)
let l1_script_011_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let depth = ref 0 in
        let max_depth = ref 0 in
        let i = ref 0 in
        while !i < n do
          if seg.[!i] = '\\' then i := !i + 2
          else if seg.[!i] = '^' then (
            incr depth;
            if !depth > !max_depth then max_depth := !depth;
            incr i)
          else if seg.[!i] = '}' then (
            if !depth > 0 then decr depth;
            incr i)
          else incr i
        done;
        if !max_depth >= 3 then incr cnt)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-011";
          severity = Warning;
          message = "Nested superscript three levels deep";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-011"; run; languages = [] }

(* SCRIPT-012: Prime notation f''' (> 3 primes) — prefer ^{(n)} *)
let l1_script_012_rule : rule =
  let re = Str.regexp {|''''|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-012";
          severity = Info;
          message = "Prime notation f''' (> 3) – prefer ^{(n)}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-012"; run; languages = [] }

(* SCRIPT-013: Plus/minus typed directly in subscript — e.g. x_{+} or x_{-}
   where \pm or \mp would be more appropriate *)
let l1_script_013_rule : rule =
  let re = Str.regexp {|_{\([+-]\)}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-013";
          severity = Info;
          message = "Plus/minus typed in subscript";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-013"; run; languages = [] }

(* SCRIPT-014: Logarithm base subscript italic — \log_x where x is a bare italic
   letter, should be \log_{x} or upright *)
let l1_script_014_rule : rule =
  (* Match \log_ followed by a single letter NOT in braces *)
  let re = Str.regexp {|\\log_\([A-Za-z]\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            (* Check it's not \log_{...} — the char after \log_ should not be
               { *)
            let after_underscore = pos + 5 in
            if
              after_underscore < String.length seg
              && seg.[after_underscore] <> '{'
            then incr cnt;
            i := Str.match_end ()
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-014";
          severity = Info;
          message = "Logarithm base subscript italic";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-014"; run; languages = [] }

(* SCRIPT-015: Time derivative dot mis-aligned — \dot or \ddot used in
   subscript/superscript context *)
let l1_script_015_rule : rule =
  let re = Str.regexp {|[_^]{\\d?dot{|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-015";
          severity = Info;
          message = "Time derivative dot mis‑aligned";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-015"; run; languages = [] }

(* SCRIPT-016: Prime on Greek letter typed '' not ^\prime — e.g. \alpha''
   instead of \alpha^{\prime\prime} *)
let l1_script_016_rule : rule =
  let greeks =
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
      "\\Upsilon";
      "\\Phi";
      "\\Psi";
      "\\Omega";
      "\\varepsilon";
      "\\vartheta";
      "\\varpi";
      "\\varrho";
      "\\varsigma";
      "\\varphi";
    ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun g ->
            let pat = g ^ "''" in
            cnt := !cnt + count_substring seg pat)
          greeks)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-016";
          severity = Info;
          message = {|Prime on Greek letter typed '' not ^\prime|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-016"; run; languages = [] }

(* SCRIPT-017: Inconsistent order of sub/superscripts — detects when some atoms
   use x_a^b and others use x^b_a in the same document *)
let l1_script_017_rule : rule =
  let re_sub_sup =
    Str.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)\^\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let re_sup_sub =
    Str.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|}
  in
  let run s =
    let math_segs = extract_math_segments s in
    let sub_sup_count = ref 0 in
    let sup_sub_count = ref 0 in
    List.iter
      (fun seg ->
        sub_sup_count := !sub_sup_count + count_re_matches re_sub_sup seg;
        sup_sub_count := !sup_sub_count + count_re_matches re_sup_sub seg)
      math_segs;
    (* Fire only if both orderings are used *)
    if !sub_sup_count > 0 && !sup_sub_count > 0 then
      Some
        {
          id = "SCRIPT-017";
          severity = Info;
          message = "Inconsistent order of sub/superscripts";
          count = min !sub_sup_count !sup_sub_count;
        }
    else None
  in
  { id = "SCRIPT-017"; run; languages = [] }

(* SCRIPT-018: Degree symbol in superscript without braces — e.g. ^\circ without
   braces: should be ^{\circ} *)
let l1_script_018_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Match ^\\circ not preceded by ^{ *)
        let n = String.length seg in
        let target = "^\\circ" in
        let tlen = String.length target in
        let i = ref 0 in
        while !i + tlen <= n do
          if String.sub seg !i tlen = target then (
            (* Check it's not ^{\circ} *)
            if !i + 1 < n && seg.[!i + 1] <> '{' then incr cnt;
            i := !i + tlen)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-018";
          severity = Warning;
          message = "Degree symbol in superscript without braces";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-018"; run; languages = [] }

(* SCRIPT-019: Double prime '' instead of ^{\prime\prime} *)
let l1_script_019_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let n = String.length seg in
        let i = ref 0 in
        while !i + 1 < n do
          if seg.[!i] = '\'' && seg.[!i + 1] = '\'' then
            if
              (* Skip triple+ primes — those are handled by SCRIPT-012/022 *)
              !i + 2 < n && seg.[!i + 2] = '\''
            then
              (* skip the run of primes *)
              while !i < n && seg.[!i] = '\'' do
                incr i
              done
            else (
              incr cnt;
              i := !i + 2)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-019";
          severity = Info;
          message = {|Double prime '' instead of ^{\prime\prime}|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-019"; run; languages = [] }

(* SCRIPT-020: Subscript text italic instead of \mathrm — e.g. $T_{eff}$ where
   the subscript is a multi-char word rendered in italic by default, should use
   \mathrm{eff} *)
let l1_script_020_rule : rule =
  (* Reuses the same detection as SCRIPT-007 but focuses specifically on
     subscripts that are abbreviation-like 2-3 char lowercase words *)
  let re = Str.regexp {|_{\([a-z][a-z]+\)}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
            let matched = Str.matched_group 1 seg in
            let next_i = Str.match_end () in
            (* Exclude single-letter and known math operators *)
            let is_operator =
              List.mem matched
                [
                  "min";
                  "max";
                  "lim";
                  "inf";
                  "sup";
                  "det";
                  "dim";
                  "ker";
                  "log";
                  "exp";
                  "sin";
                  "cos";
                  "tan";
                  "arg";
                  "deg";
                  "gcd";
                  "hom";
                  "mod";
                ]
            in
            (if (not is_operator) && String.length matched >= 2 then
               (* Check not already wrapped in \mathrm or \text *)
               let prefix_start = max 0 (pos - 9) in
               let prefix =
                 String.sub seg prefix_start (pos - prefix_start + 2)
               in
               if
                 count_substring prefix "\\mathrm{" = 0
                 && count_substring prefix "\\text{" = 0
               then incr cnt);
            i := next_i
          done
        with Not_found -> ())
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-020";
          severity = Info;
          message = {|Subscript text italic instead of \mathrm|};
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-020"; run; languages = [] }

(* SCRIPT-021: Sub-sup order not canonical — a_{b}^{c} vs a^{c}_{b} — flag when
   a_{...}^{...} is used (canonical is a^{...}_{...} per convention) *)
let l1_script_021_rule : rule =
  let re = Str.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)\^\({[^}]*}\|[A-Za-z0-9]\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-021";
          severity = Warning;
          message = "Sub‑sup order not canonical (a_{b}^{c} vs a^{c}_{b})";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-021"; run; languages = [] }

(* SCRIPT-022: Superscript prime stacked > 3 — prefer ^{(n)} — similar to
   SCRIPT-012 but specifically for ^{'''...} notation *)
let l1_script_022_rule : rule =
  let re = Str.regexp {|\^{''''|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "SCRIPT-022";
          severity = Info;
          message = "Superscript prime stacked > 3 – prefer ^{(n)}";
          count = !cnt;
        }
    else None
  in
  { id = "SCRIPT-022"; run; languages = [] }

(* ═══════════════════════════════════════════════════════════════════════ REF
   validators: cross-referencing and label hygiene
   ═══════════════════════════════════════════════════════════════════════ *)

(* REF-001: Undefined \ref/\eqref label after expansion Uses
   Semantic_state.get_state() if available, falls back to regex. *)
let l1_ref_001_rule : rule =
  let run s =
    let cnt =
      match Semantic_state.get_state () with
      | Some st -> List.length st.Semantic_state.undefined_refs
      | None ->
          (* Fallback: regex-based *)
          let labels = extract_labels s in
          let refs = extract_refs s in
          let c = ref 0 in
          List.iter (fun r -> if not (List.mem r labels) then incr c) refs;
          !c
    in
    if cnt > 0 then
      Some
        {
          id = "REF-001";
          severity = Error;
          message = {|Undefined \ref / \eqref label after expansion|};
          count = cnt;
        }
    else None
  in
  { id = "REF-001"; run; languages = [] }

(* REF-002: Duplicate label name Uses Semantic_state.get_state() if available,
   falls back to regex. *)
let l1_ref_002_rule : rule =
  let run s =
    let cnt =
      match Semantic_state.get_state () with
      | Some st ->
          (* Count extra occurrences: for each dup key, count how many times it
             appears beyond the first *)
          let label_keys =
            List.map
              (fun (l : Semantic_state.label_entry) -> l.Semantic_state.key)
              st.Semantic_state.labels
          in
          List.fold_left
            (fun acc dup_key ->
              let total =
                List.length (List.filter (fun k -> k = dup_key) label_keys)
              in
              acc + total - 1)
            0 st.Semantic_state.duplicate_labels
      | None ->
          let labels = extract_labels s in
          let seen = Hashtbl.create 16 in
          let c = ref 0 in
          List.iter
            (fun lbl ->
              if Hashtbl.mem seen lbl then incr c else Hashtbl.add seen lbl true)
            labels;
          !c
    in
    if cnt > 0 then
      Some
        {
          id = "REF-002";
          severity = Error;
          message = "Duplicate label name";
          count = cnt;
        }
    else None
  in
  { id = "REF-002"; run; languages = [] }

(* REF-003: Label contains spaces *)
let l1_ref_003_rule : rule =
  let run s =
    let labels = extract_labels s in
    let cnt = ref 0 in
    List.iter (fun lbl -> if String.contains lbl ' ' then incr cnt) labels;
    if !cnt > 0 then
      Some
        {
          id = "REF-003";
          severity = Warning;
          message = "Label contains spaces";
          count = !cnt;
        }
    else None
  in
  { id = "REF-003"; run; languages = [] }

(* REF-004: Label contains uppercase letters *)
let l1_ref_004_rule : rule =
  let has_upper s =
    let n = String.length s in
    let rec loop i =
      if i >= n then false
      else if s.[i] >= 'A' && s.[i] <= 'Z' then true
      else loop (i + 1)
    in
    loop 0
  in
  let run s =
    let labels = extract_labels s in
    let cnt = ref 0 in
    List.iter (fun lbl -> if has_upper lbl then incr cnt) labels;
    if !cnt > 0 then
      Some
        {
          id = "REF-004";
          severity = Info;
          message = "Label contains uppercase letters";
          count = !cnt;
        }
    else None
  in
  { id = "REF-004"; run; languages = [] }

(* REF-005: Label not prefixed with fig:/tab:/eq:/sec: *)
let l1_ref_005_rule : rule =
  let prefixes =
    [
      "fig:";
      "tab:";
      "eq:";
      "sec:";
      "ch:";
      "app:";
      "lst:";
      "thm:";
      "lem:";
      "def:";
      "prop:";
      "cor:";
      "rem:";
      "ex:";
      "alg:";
    ]
  in
  let has_prefix lbl =
    List.exists
      (fun p ->
        let plen = String.length p in
        String.length lbl >= plen && String.sub lbl 0 plen = p)
      prefixes
  in
  let run s =
    let labels = extract_labels s in
    let cnt = ref 0 in
    List.iter (fun lbl -> if not (has_prefix lbl) then incr cnt) labels;
    if !cnt > 0 then
      Some
        {
          id = "REF-005";
          severity = Info;
          message = "Label not prefixed fig:/tab:/eq:/sec:";
          count = !cnt;
        }
    else None
  in
  { id = "REF-005"; run; languages = [] }

(* REF-006: Page reference uses \ref not \pageref — detects "page \ref{...}" *)
let l1_ref_006_rule : rule =
  let re = Str.regexp {|[Pp]age[ ~]*\\ref{|} in
  let run s =
    let cnt = count_re_matches re s in
    if cnt > 0 then
      Some
        {
          id = "REF-006";
          severity = Info;
          message = {|Page reference uses \ref not \pageref|};
          count = cnt;
        }
    else None
  in
  { id = "REF-006"; run; languages = [] }

(* REF-007: Cite key contains whitespace *)
let l1_ref_007_rule : rule =
  let re = Str.regexp "\\\\cite\\([^{]*\\){[^}]*[ \t][^}]*}" in
  let run s =
    let cnt = count_re_matches re s in
    if cnt > 0 then
      Some
        {
          id = "REF-007";
          severity = Error;
          message = "Cite key contains whitespace";
          count = cnt;
        }
    else None
  in
  { id = "REF-007"; run; languages = [] }

(* REF-009: Reference appears before label definition (forward ref) Uses
   Semantic_state.get_state() if available, falls back to regex. *)
let l1_ref_009_rule : rule =
  let re_label = Str.regexp {|\\label{[^}]*}|} in
  let re_ref = Str.regexp {|\\eqref{[^}]*}\|\\ref{[^}]*}|} in
  let run s =
    let cnt =
      match Semantic_state.get_state () with
      | Some st -> List.length st.Semantic_state.forward_refs
      | None ->
          let n = String.length s in
          let label_positions = Hashtbl.create 16 in
          let i = ref 0 in
          (try
             while true do
               let pos = Str.search_forward re_label s !i in
               let m = Str.matched_string s in
               let next = Str.match_end () in
               let inner = String.sub m 7 (String.length m - 8) in
               if not (Hashtbl.mem label_positions inner) then
                 Hashtbl.add label_positions inner pos;
               i := next
             done
           with Not_found -> ());
          ignore n;
          let c = ref 0 in
          i := 0;
          (try
             while true do
               let pos = Str.search_forward re_ref s !i in
               let m = Str.matched_string s in
               let next = Str.match_end () in
               let brace_pos = String.index m '{' in
               let inner =
                 String.sub m (brace_pos + 1) (String.length m - brace_pos - 2)
               in
               (match Hashtbl.find_opt label_positions inner with
               | Some label_pos -> if pos < label_pos then incr c
               | None -> ());
               i := next
             done
           with Not_found -> ());
          !c
    in
    if cnt > 0 then
      Some
        {
          id = "REF-009";
          severity = Info;
          message = "Reference appears before label definition (forward ref)";
          count = cnt;
        }
    else None
  in
  { id = "REF-009"; run; languages = [] }

(* ═══════════════════════════════════════════════════════════════════════ CHEM
   validators: chemistry notation
   ═══════════════════════════════════════════════════════════════════════ *)

(* CHEM-001: Missing \ce{} wrapper for chemical formula — detects patterns like
   H_2O, CO_2, NaCl in math mode without \ce{} *)
let l1_chem_001_rule : rule =
  let re = Str.regexp {|[A-Z][a-z]?_\({[0-9]+}\|[0-9]\)|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        if count_substring seg "\\ce{" = 0 then
          cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-001";
          severity = Warning;
          message = {|Missing \ce{} wrapper for chemical formula|};
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-001"; run; languages = [] }

(* CHEM-002: Oxidation-state superscript missing braces — e.g. Fe^2+ should be
   Fe^{2+} *)
let l1_chem_002_rule : rule =
  let re = Str.regexp {|[A-Z][a-z]?\^[0-9][+-]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-002";
          severity = Warning;
          message = "Oxidation‑state superscript missing braces";
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-002"; run; languages = [] }

(* CHEM-003: Isotope mass number subscripted not superscripted — e.g. _14C
   should be ^{14}C *)
let l1_chem_003_rule : rule =
  let re = Str.regexp {|_\({[0-9]+}\|[0-9]+\)[A-Z]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        if count_substring seg "\\ce{" = 0 then
          cnt := !cnt + count_re_matches re seg)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-003";
          severity = Warning;
          message = "Isotope mass number subscripted, not superscripted";
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-003"; run; languages = [] }

(* CHEM-004: Charge written ^- instead of ^{-} *)
let l1_chem_004_rule : rule =
  let re = Str.regexp {|[A-Z][a-z]?\^[+-][^}]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-004";
          severity = Info;
          message = "Charge written ^- instead of ^{-}";
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-004"; run; languages = [] }

(* CHEM-005: Chemical arrow typed '->' not \rightarrow — detects -> in math that
   is not part of \rightarrow *)
let l1_chem_005_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let total = count_substring seg "->" in
        let proper = count_substring seg "\\rightarrow" in
        let longarrow = count_substring seg "\\longrightarrow" in
        let bare = total - proper - longarrow in
        if bare > 0 then cnt := !cnt + bare)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-005";
          severity = Info;
          message = {|Chemical arrow typed '->' not \rightarrow|};
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-005"; run; languages = [] }

(* CHEM-006: Stoichiometry coefficient inside \ce missing — detects \ce{H2O}
   without a leading number when multiple molecules are implied *)
let l1_chem_006_rule : rule =
  let ce_prefix = "\\ce{" in
  let ce_plen = String.length ce_prefix in
  let run s =
    (* Only flag if there are \ce{} with + (reactions) where some lack
       coefficients *)
    let cnt = ref 0 in
    let n = String.length s in
    let i = ref 0 in
    while !i <= n - ce_plen do
      (* Manual scan for \ce{ *)
      if String.sub s !i ce_plen = ce_prefix then (
        let start = !i + ce_plen in
        (* Find matching } *)
        let brace_level = ref 1 in
        let j = ref start in
        while !j < n && !brace_level > 0 do
          if s.[!j] = '{' then incr brace_level
          else if s.[!j] = '}' then decr brace_level;
          incr j
        done;
        if !brace_level = 0 then (
          let ce_content = String.sub s start (!j - start - 1) in
          (* Check if this \ce has a + (reaction) *)
          (if count_substring ce_content " + " > 0 then
             (* Check if any reactant/product lacks a coefficient *)
             let parts = String.split_on_char '+' ce_content in
             List.iter
               (fun part ->
                 let trimmed = String.trim part in
                 if
                   String.length trimmed > 0
                   && trimmed.[0] >= 'A'
                   && trimmed.[0] <= 'Z'
                 then incr cnt)
               parts);
          i := !j)
        else i := !i + 1)
      else i := !i + 1
    done;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-006";
          severity = Warning;
          message = {|Stoichiometry coefficient inside \ce missing|};
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-006"; run; languages = [] }

(* CHEM-007: Reaction conditions not in \text above arrow — detects
   ->[conditions] or ->[\text{...}] patterns *)
let l1_chem_007_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        (* Look for -> followed by [...] without \text inside *)
        let n = String.length seg in
        let i = ref 0 in
        while !i < n - 3 do
          if
            seg.[!i] = '-'
            && seg.[!i + 1] = '>'
            && !i + 2 < n
            && seg.[!i + 2] = '['
          then (
            (* Found ->[, scan for closing ] *)
            let j = ref (!i + 3) in
            while !j < n && seg.[!j] <> ']' do
              incr j
            done;
            (if !j < n then
               let bracket_content = String.sub seg (!i + 3) (!j - !i - 3) in
               if
                 count_substring bracket_content "\\text{" = 0
                 && String.length bracket_content > 0
               then incr cnt);
            i := !j + 1)
          else incr i
        done)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-007";
          severity = Info;
          message = {|Reaction conditions not in \text above arrow|};
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-007"; run; languages = [] }

(* CHEM-008: State symbols (aq), (s), (l), (g) not wrapped in \text *)
let l1_chem_008_rule : rule =
  let state_syms = [ "(aq)"; "(s)"; "(l)"; "(g)" ] in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun sym ->
            let total = count_substring seg sym in
            let wrapped = count_substring seg ("\\text{" ^ sym ^ "}") in
            let bare = total - wrapped in
            if bare > 0 then cnt := !cnt + bare)
          state_syms)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-008";
          severity = Info;
          message = {|State symbols (aq) not wrapped in \text|};
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-008"; run; languages = [] }

(* CHEM-009: Equilibrium arrow typed as <> or <-> — should use
   \rightleftharpoons *)
let l1_chem_009_rule : rule =
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let cnt1 = count_substring seg "<->" in
        let cnt2 = count_substring seg "<=>" in
        cnt := !cnt + cnt1 + cnt2)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CHEM-009";
          severity = Warning;
          message = "Equilibrium arrow typed as '<>'";
          count = !cnt;
        }
    else None
  in
  { id = "CHEM-009"; run; languages = [] }

(* CMD-007: Optional argument declared but not used in definition body *)
let l1_cmd_007_rule : rule =
  let re_newcmd =
    Str.regexp
      {|\\\(newcommand\|renewcommand\|providecommand\){\\[a-zA-Z]+}\[[0-9]+\]|}
  in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    let n = String.length s in
    (try
       while true do
         let _ = Str.search_forward re_newcmd s !i in
         let mstart = Str.match_beginning () in
         let mend = Str.match_end () in
         (* Extract the arity from [N] *)
         let bracket_start = ref (mend - 2) in
         while !bracket_start > mstart && s.[!bracket_start] <> '[' do
           decr bracket_start
         done;
         let arity_str =
           String.sub s (!bracket_start + 1) (mend - 2 - !bracket_start)
         in
         let arity = try int_of_string arity_str with Failure _ -> 0 in
         (* Find the definition body in the next brace block *)
         if mend < n && s.[mend] = '{' then (
           let depth = ref 1 in
           let j = ref (mend + 1) in
           while !j < n && !depth > 0 do
             if s.[!j] = '{' then incr depth
             else if s.[!j] = '}' then decr depth;
             incr j
           done;
           if !depth = 0 then (
             let body = String.sub s (mend + 1) (!j - mend - 2) in
             (* Check each #k appears in body *)
             let unused = ref false in
             for k = 1 to arity do
               let param = Printf.sprintf "#%d" k in
               if count_substring body param = 0 then unused := true
             done;
             if !unused then incr cnt);
           i := !j)
         else i := mend
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "CMD-007";
          severity = Info;
          message = "Optional argument not used inside definition body";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-007"; run; languages = [] }

(* CMD-010: More than three successive macro renewals *)
let l1_cmd_010_rule : rule =
  let run s =
    let lines = String.split_on_char '\n' s in
    let cnt = ref 0 in
    let consecutive = ref 0 in
    List.iter
      (fun line ->
        let trimmed = String.trim line in
        let prefix = "\\renewcommand" in
        let plen = String.length prefix in
        if String.length trimmed >= plen && String.sub trimmed 0 plen = prefix
        then (
          incr consecutive;
          if !consecutive > 3 then incr cnt)
        else consecutive := 0)
      lines;
    if !cnt > 0 then
      Some
        {
          id = "CMD-010";
          severity = Info;
          message = "More than three successive macro renewals";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-010"; run; languages = [] }

(* FONT-001: Small-caps applied to all-caps word (ineffective) *)
let l1_font_001_rule : rule =
  let textsc_prefix = "\\textsc{" in
  let textsc_plen = String.length textsc_prefix in
  let run s =
    let cnt = ref 0 in
    let n = String.length s in
    let i = ref 0 in
    while !i <= n - textsc_plen do
      if String.sub s !i textsc_plen = textsc_prefix then (
        let start = !i + textsc_plen in
        let depth = ref 1 in
        let j = ref start in
        while !j < n && !depth > 0 do
          if s.[!j] = '{' then incr depth else if s.[!j] = '}' then decr depth;
          incr j
        done;
        if !depth = 0 then (
          let content = String.sub s start (!j - start - 1) in
          (* Check if content is all uppercase letters and spaces *)
          let all_upper = ref true in
          let has_alpha = ref false in
          String.iter
            (fun c ->
              if c >= 'A' && c <= 'Z' then has_alpha := true
              else if c = ' ' then ()
              else all_upper := false)
            content;
          if !all_upper && !has_alpha then incr cnt);
        i := !j)
      else incr i
    done;
    if !cnt > 0 then
      Some
        {
          id = "FONT-001";
          severity = Info;
          message = "Small‑caps applied to all‑caps word (ineffective)";
          count = !cnt;
        }
    else None
  in
  { id = "FONT-001"; run; languages = [] }

(* FONT-004: Font change inside math via \textit not \mathit *)
let l1_font_004_rule : rule =
  let text_font_cmds =
    [ "\\textit{"; "\\textbf{"; "\\textrm{"; "\\textsf{"; "\\texttt{" ]
  in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun cmd -> cnt := !cnt + count_substring seg cmd)
          text_font_cmds)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "FONT-004";
          severity = Info;
          message = {|Font change inside math via \textit not \mathit|};
          count = !cnt;
        }
    else None
  in
  { id = "FONT-004"; run; languages = [] }

(* RTL-003: Unbalanced \beginR / \endR primitives *)
let l1_rtl_003_rule : rule =
  let run s =
    let opens = count_substring s "\\beginR" in
    let closes = count_substring s "\\endR" in
    if opens <> closes && (opens > 0 || closes > 0) then
      Some
        {
          id = "RTL-003";
          severity = Error;
          message = {|Unbalanced \beginR / \endR primitives|};
          count = abs (opens - closes);
        }
    else None
  in
  { id = "RTL-003"; run; languages = [ "ar"; "he" ] }

(* RTL-004: RTL punctuation not mirrored in math *)
let l1_rtl_004_rule : rule =
  (* Hebrew maqaf U+05BE, Arabic comma U+060C, Hebrew geresh U+05F3 *)
  let rtl_puncts = [ "\xd6\xbe"; "\xd8\x8c"; "\xd7\x83" ] in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        List.iter
          (fun punct -> cnt := !cnt + count_substring seg punct)
          rtl_puncts)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "RTL-004";
          severity = Warning;
          message = "RTL punctuation not mirrored in math";
          count = !cnt;
        }
    else None
  in
  { id = "RTL-004"; run; languages = [ "ar"; "he" ] }

(* CJK-008: Full-width space U+3000 inside math mode *)
let l1_cjk_008_rule : rule =
  let fullwidth_space = "\xe3\x80\x80" in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg fullwidth_space)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CJK-008";
          severity = Warning;
          message = "Full‑width space U+3000 inside math mode";
          count = !cnt;
        }
    else None
  in
  { id = "CJK-008"; run; languages = [ "zh"; "ja"; "ko" ] }

(* CJK-015: Chinese comma U+3001 (ideographic comma) inside math mode *)
let l1_cjk_015_rule : rule =
  let ideographic_comma = "\xe3\x80\x81" in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg -> cnt := !cnt + count_substring seg ideographic_comma)
      math_segs;
    if !cnt > 0 then
      Some
        {
          id = "CJK-015";
          severity = Warning;
          message = "Chinese comma U+3001 inside math mode";
          count = !cnt;
        }
    else None
  in
  { id = "CJK-015"; run; languages = [ "zh"; "ja"; "ko" ] }

(* TYPO-059: Punctuation inside math adjacent to operators — e.g. ,= or ;+ *)
let l1_typo_059_rule : rule =
  let re = Str.regexp {|[,;.][ ]*[=<>+\-]|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter (fun seg -> cnt := !cnt + count_re_matches re seg) math_segs;
    if !cnt > 0 then
      Some
        {
          id = "TYPO-059";
          severity = Info;
          message = "Punctuation inside math must be typed with spacing macros";
          count = !cnt;
        }
    else None
  in
  { id = "TYPO-059"; run; languages = [] }

(* PT-002: pt-BR decimal comma and thousand dot enforcement *)
let l1_pt_002_rule : rule =
  (* Detect 1.234 or 3.14 patterns that should use comma as decimal separator in
     pt-BR. Only fire if document uses brazilian/portuges. *)
  let re_num = Str.regexp {|[0-9]+\.[0-9]+|} in
  let re_br =
    Str.regexp
      {|\\\(usepackage\|documentclass\).*\(brazilian\|brazil\|portuges\)|}
  in
  let run s =
    (* Only fire if the document uses pt-BR *)
    let has_br =
      try
        let _ = Str.search_forward re_br s 0 in
        true
      with Not_found -> false
    in
    if has_br then (
      let math_segs = extract_math_segments s in
      let cnt = ref 0 in
      List.iter (fun seg -> cnt := !cnt + count_re_matches re_num seg) math_segs;
      if !cnt > 0 then
        Some
          {
            id = "PT-002";
            severity = Info;
            message = "pt‑BR: decimal comma and thousand dot enforcement";
            count = !cnt;
          }
      else None)
    else None
  in
  { id = "PT-002"; run; languages = [ "pt" ] }

(* ══════════════════════════════════════════════════════════════════════ L3-*
   rules — LaTeX3 / expl3 style validators (L1_Expanded precondition)
   ══════════════════════════════════════════════════════════════════════ *)

(* L3-001: LaTeX3 \tl_new:N in preamble mixed with 2e macros *)
let l1_l3_001_rule : rule =
  let re_expl3 =
    Str.regexp
      {|\\[a-z]+_[a-z_]+:[a-zA-Z]+\|\\tl_new:N\|\\int_new:N\|\\bool_new:N|}
  in
  let re_2e =
    Str.regexp
      {|\\newcommand\|\\renewcommand\|\\newenvironment\|\\renewenvironment|}
  in
  let re_begin_doc = Str.regexp_string {|\begin{document}|} in
  let run s =
    let preamble =
      try
        let idx = Str.search_forward re_begin_doc s 0 in
        String.sub s 0 idx
      with Not_found -> s
    in
    let has_expl3 =
      try
        ignore (Str.search_forward re_expl3 preamble 0);
        true
      with Not_found -> false
    in
    let has_2e =
      try
        ignore (Str.search_forward re_2e preamble 0);
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

(* L3-002: Expl3 variable declared after \begin{document} *)
let l1_l3_002_rule : rule =
  let re_expl3_decl =
    Str.regexp {|\\[a-z]+_new:N\|\\[a-z]+_const:Nn\|\\[a-z]+_gset:Nn|}
  in
  let re_begin_doc2 = Str.regexp_string {|\begin{document}|} in
  let run s =
    let body =
      try
        let idx = Str.search_forward re_begin_doc2 s 0 in
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
  { id = "L3-002"; run; languages = [] }

(* L3-003: Expl3 and etoolbox patch macros combined *)
let l1_l3_003_rule : rule =
  let re_expl3 = Str.regexp {|\\ExplSyntaxOn\|\\[a-z]+_[a-z_]+:[a-zA-Z]|} in
  let re_etoolbox =
    Str.regexp
      {|\\patchcmd\|\\apptocmd\|\\pretocmd\|\\robustify\|\\AtBeginEnvironment|}
  in
  let run s =
    let has_expl3 =
      try
        ignore (Str.search_forward re_expl3 s 0);
        true
      with Not_found -> false
    in
    let has_etoolbox =
      try
        ignore (Str.search_forward re_etoolbox s 0);
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

(* L3-004: Undocumented \__module_internal:N used *)
let l1_l3_004_rule : rule =
  let re = Str.regexp {|\\__[a-z_]+:[a-zA-Z]*|} in
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
  { id = "L3-004"; run; languages = [] }

(* L3-005: Missing \ExplSyntaxOn guard around expl3 code *)
let l1_l3_005_rule : rule =
  let re_expl3_func = Str.regexp {|\\[a-z]+_[a-z_]+:[nNoVvxfeTFpw]+|} in
  let re_syntax_on = Str.regexp_string {|\ExplSyntaxOn|} in
  let run s =
    let has_expl3 =
      try
        ignore (Str.search_forward re_expl3_func s 0);
        true
      with Not_found -> false
    in
    if not has_expl3 then None
    else
      let has_guard =
        try
          ignore (Str.search_forward re_syntax_on s 0);
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
  { id = "L3-005"; run; languages = [] }

(* L3-006: Expl3 variable clobbers package macro name *)
let l1_l3_006_rule : rule =
  let re_pkg = Str.regexp {|\\usepackage\(\[[^]]*\]\)?{\([^}]+\)}|} in
  let re_var = Str.regexp {|\\[lg]_\([a-z]+\)_[a-z_]+:[a-zA-Z]*|} in
  let run s =
    let pkgs = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward re_pkg s !i in
         let pkg_list = Str.matched_group 2 s in
         List.iter
           (fun p ->
             let p = String.trim p in
             if String.length p > 0 then pkgs := p :: !pkgs)
           (String.split_on_char ',' pkg_list);
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !pkgs = [] then None
    else
      let cnt = ref 0 in
      let j = ref 0 in
      (try
         while true do
           let _ = Str.search_forward re_var s !j in
           let var_prefix = Str.matched_group 1 s in
           if List.mem var_prefix !pkgs then incr cnt;
           j := Str.match_end ()
         done
       with Not_found -> ());
      if !cnt > 0 then
        Some
          {
            id = "L3-006";
            severity = Warning;
            message = "Expl3 variable clobbers package macro name";
            count = !cnt;
          }
      else None
  in
  { id = "L3-006"; run; languages = [] }

(* L3-007: Mix of camelCase and snake_case in expl3 names *)
let l1_l3_007_rule : rule =
  let re_camel = Str.regexp {|\\[a-z]+[A-Z][a-zA-Z]*_[a-z_]+:[a-zA-Z]*|} in
  let re_syntax_on = Str.regexp_string {|\ExplSyntaxOn|} in
  let run s =
    let has_expl3 =
      try
        ignore (Str.search_forward re_syntax_on s 0);
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
  { id = "L3-007"; run; languages = [] }

(* L3-009: LaTeX3 function deprecated _n: variant used *)
let l1_l3_009_rule : rule =
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
  { id = "L3-009"; run; languages = [] }

(* L3-011: Engine-branch uses pdfTeX primitive in LuaTeX or XeTeX path *)
let l1_l3_011_rule : rule =
  let re_luatex_branch =
    Str.regexp {|\\sys_if_engine_luatex:T\|\\ifluatex\|\\ifLuaTeX|}
  in
  let re_xetex_branch =
    Str.regexp {|\\sys_if_engine_xetex:T\|\\ifxetex\|\\ifXeTeX|}
  in
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
        ignore (Str.search_forward re_luatex_branch s 0);
        true
      with Not_found -> false
    in
    let has_xe =
      try
        ignore (Str.search_forward re_xetex_branch s 0);
        true
      with Not_found -> false
    in
    if not (has_lua || has_xe) then None
    else
      let cnt =
        List.fold_left (fun acc p -> acc + count_substring s p) 0 pdftex_prims
      in
      if cnt > 0 then
        Some
          {
            id = "L3-011";
            severity = Warning;
            message = "Engine‑branch uses pdfTeX primitive in Lua/XeTeX path";
            count = cnt;
          }
      else None
  in
  { id = "L3-011"; run; languages = [] }

(* CMD-001: Command \newcommand defined but never used *)
let l1_cmd_001_rule : rule =
  let def_re =
    Str.regexp
      "\\\\\\(newcommand\\|renewcommand\\)[ \t\n]*{?\\\\\\([a-zA-Z]+\\)}?"
  in
  let find_substring s pat from =
    let n = String.length s and m = String.length pat in
    if m = 0 || n < m then raise Not_found
    else
      let rec loop i =
        if i > n - m then raise Not_found
        else if String.sub s i m = pat then i
        else loop (i + 1)
      in
      loop from
  in
  let def_ctx_re = Str.regexp {|\\newcommand\|\\renewcommand|} in
  let run s =
    (* Collect all defined command names *)
    let defs = ref [] in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward def_re s !i in
         let name = Str.matched_group 2 s in
         defs := name :: !defs;
         i := Str.match_end ()
       done
     with Not_found -> ());
    (* Check each defined name for usage elsewhere *)
    let len = String.length s in
    let cnt =
      List.fold_left
        (fun acc name ->
          let pat = "\\" ^ name in
          let pat_len = String.length pat in
          let uses = ref 0 in
          let j = ref 0 in
          (try
             while true do
               let pos = find_substring s pat !j in
               (* Check character after match is not a letter (word boundary) *)
               let after_ok =
                 pos + pat_len >= len
                 ||
                 let c = s.[pos + pat_len] in
                 not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))
               in
               (if after_ok then
                  (* Check this isn't the definition itself *)
                  let is_def =
                    pos >= 11
                    &&
                    let start = max 0 (pos - 15) in
                    let ctx = String.sub s start (pos - start) in
                    try
                      let _ = Str.search_forward def_ctx_re ctx 0 in
                      true
                    with Not_found -> false
                  in
                  if not is_def then incr uses);
               j := pos + 1
             done
           with Not_found -> ());
          if !uses = 0 then acc + 1 else acc)
        0 !defs
    in
    if cnt > 0 then
      Some
        {
          id = "CMD-001";
          severity = Info;
          message = {|Command \newcommand defined but never used|};
          count = cnt;
        }
    else None
  in
  { id = "CMD-001"; run; languages = [] }

(* CMD-003: User macro name clashes with package macro *)
let l1_cmd_003_rule : rule =
  let known_macros =
    [
      "textbf";
      "textit";
      "emph";
      "href";
      "cite";
      "ref";
      "label";
      "caption";
      "footnote";
      "section";
      "subsection";
      "subsubsection";
      "paragraph";
      "includegraphics";
      "begin";
      "end";
      "item";
      "maketitle";
      "tableofcontents";
      "bibliography";
      "usepackage";
      "documentclass";
      "title";
      "author";
      "date";
      "centering";
      "hspace";
      "vspace";
      "frac";
      "sqrt";
      "text";
    ]
  in
  let def_re =
    Str.regexp
      "\\\\\\(newcommand\\|renewcommand\\)[ \t\n]*{?\\\\\\([a-zA-Z]+\\)}?"
  in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    (try
       while true do
         let _ = Str.search_forward def_re s !i in
         let name = Str.matched_group 2 s in
         if List.mem name known_macros then incr cnt;
         i := Str.match_end ()
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "CMD-003";
          severity = Warning;
          message = "User macro name clashes with package macro";
          count = !cnt;
        }
    else None
  in
  { id = "CMD-003"; run; languages = [] }

let rules_l1 : rule list =
  [
    l1_cmd_001_rule;
    l1_cmd_003_rule;
    l1_mod_001_rule;
    l1_exp_001_rule;
    l1_mod_002_rule;
    l1_mod_003_rule;
    l1_mod_004_rule;
    l1_mod_005_rule;
    l1_mod_006_rule;
    l1_mod_007_rule;
    l1_mod_008_rule;
    l1_mod_009_rule;
    l1_mod_010_rule;
    l1_mod_011_rule;
    l1_mod_012_rule;
    l1_mod_013_rule;
    l1_mod_020_rule;
    l1_mod_021_rule;
    l1_mod_022_rule;
    l1_mod_023_rule;
    l1_mod_024_rule;
    l1_delim_001_rule;
    l1_delim_002_rule;
    l1_delim_003_rule;
    l1_delim_004_rule;
    l1_delim_005_rule;
    l1_delim_006_rule;
    l1_delim_007_rule;
    l1_delim_008_rule;
    l1_delim_009_rule;
    l1_delim_010_rule;
    l1_delim_011_rule;
    l1_script_001_rule;
    l1_script_002_rule;
    l1_script_003_rule;
    l1_script_004_rule;
    l1_script_005_rule;
    l1_script_006_rule;
    l1_script_007_rule;
    l1_script_008_rule;
    l1_script_009_rule;
    l1_script_010_rule;
    l1_script_011_rule;
    l1_script_012_rule;
    l1_script_013_rule;
    l1_script_014_rule;
    l1_script_015_rule;
    l1_script_016_rule;
    l1_script_017_rule;
    l1_script_018_rule;
    l1_script_019_rule;
    l1_script_020_rule;
    l1_script_021_rule;
    l1_script_022_rule;
    l1_math_009_rule;
    l1_math_010_rule;
    l1_math_011_rule;
    l1_math_012_rule;
    l1_math_013_rule;
    l1_math_014_rule;
    l1_math_015_rule;
    l1_math_016_rule;
    l1_math_017_rule;
    l1_math_018_rule;
    l1_math_019_rule;
    l1_math_020_rule;
    l1_math_021_rule;
    l1_math_022_rule;
    l1_math_025_rule;
    l1_math_028_rule;
    l1_math_029_rule;
    l1_math_030_rule;
    l1_math_031_rule;
    l1_math_033_rule;
    l1_math_034_rule;
    l1_math_035_rule;
    l1_math_036_rule;
    l1_math_037_rule;
    l1_math_038_rule;
    l1_math_039_rule;
    l1_math_040_rule;
    l1_math_041_rule;
    l1_math_042_rule;
    l1_math_043_rule;
    l1_math_044_rule;
    l1_math_045_rule;
    l1_math_046_rule;
    l1_math_047_rule;
    l1_math_048_rule;
    l1_math_049_rule;
    l1_math_050_rule;
    l1_math_051_rule;
    l1_math_052_rule;
    l1_math_053_rule;
    l1_math_055_rule;
    l1_math_057_rule;
    l1_math_058_rule;
    l1_math_065_rule;
    l1_math_066_rule;
    l1_math_068_rule;
    l1_math_069_rule;
    l1_math_071_rule;
    l1_math_078_rule;
    l1_math_079_rule;
    l1_math_082_rule;
    l1_math_085_rule;
    l1_math_094_rule;
    l1_math_105_rule;
    l1_math_056_rule;
    l1_math_059_rule;
    l1_math_060_rule;
    l1_math_061_rule;
    l1_math_067_rule;
    l1_math_070_rule;
    l1_math_073_rule;
    l1_math_077_rule;
    l1_math_081_rule;
    l1_math_084_rule;
    l1_math_086_rule;
    l1_math_090_rule;
    l1_math_093_rule;
    l1_math_098_rule;
    l1_math_072_rule;
    l1_math_074_rule;
    l1_math_087_rule;
    l1_math_088_rule;
    l1_math_091_rule;
    l1_math_092_rule;
    l1_math_095_rule;
    l1_math_096_rule;
    l1_math_097_rule;
    l1_math_099_rule;
    l1_math_101_rule;
    l1_math_104_rule;
    l1_math_106_rule;
    l1_math_108_rule;
    l1_ref_001_rule;
    l1_ref_002_rule;
    l1_ref_003_rule;
    l1_ref_004_rule;
    l1_ref_005_rule;
    l1_ref_006_rule;
    l1_ref_007_rule;
    l1_ref_009_rule;
    l1_chem_001_rule;
    l1_chem_002_rule;
    l1_chem_003_rule;
    l1_chem_004_rule;
    l1_chem_005_rule;
    l1_chem_006_rule;
    l1_chem_007_rule;
    l1_chem_008_rule;
    l1_chem_009_rule;
    l1_cmd_007_rule;
    l1_cmd_010_rule;
    l1_font_001_rule;
    l1_font_004_rule;
    l1_rtl_003_rule;
    l1_rtl_004_rule;
    l1_cjk_008_rule;
    l1_cjk_015_rule;
    l1_typo_059_rule;
    l1_pt_002_rule;
    l1_l3_006_rule;
    (* L3-001..005,007,009,011 moved to Validators_l1_expl3 *)
  ]
