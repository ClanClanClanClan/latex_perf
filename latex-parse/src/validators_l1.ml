open Validators_common

(* L1 modernization and expansion checks (using post-commands heuristics) *)
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
  { id = "MOD-001"; run }

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
  { id = "EXP-001"; run }

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
  { id = "MOD-002"; run }

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
  { id = "MOD-003"; run }

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
  { id = "MOD-004"; run }

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
  { id = "MOD-005"; run }

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
  { id = "MOD-006"; run }

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
  { id = "MOD-007"; run }

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
  { id = "MOD-008"; run }

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
  { id = "MOD-009"; run }

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
  { id = "MOD-010"; run }

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
  { id = "MOD-011"; run }

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
  { id = "MOD-012"; run }

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
  { id = "MOD-013"; run }

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
  { id = "MOD-020"; run }

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
  { id = "MOD-021"; run }

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
  { id = "MOD-022"; run }

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
  { id = "MOD-023"; run }

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
  { id = "MOD-024"; run }

(* ── DELIM rules: delimiter matching (L1 — operate on expanded text) ── *)

(* Helper: extract math segment contents from source. Returns a list of strings,
   each being the content inside a math environment ($...$, \(...\), \[...\], or
   math-class \begin{env}...\end{env}). Unlike strip_math_segments which removes
   math, this returns only the math parts. *)
let extract_math_segments (s : string) : string list =
  let len = String.length s in
  let segments = ref [] in
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
      "math";
      "displaymath";
    ]
  in
  let math_env_tbl = Hashtbl.create 32 in
  List.iter (fun e -> Hashtbl.replace math_env_tbl e ()) math_envs;
  let is_math_env name = Hashtbl.mem math_env_tbl name in
  let starts_with prefix idx =
    let plen = String.length prefix in
    idx + plen <= len && String.sub s idx plen = prefix
  in
  let is_escaped idx =
    let rec count back acc =
      if back < 0 then acc
      else if String.unsafe_get s back = '\\' then count (back - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let parse_begin idx =
    if not (starts_with "\\begin{" idx) then None
    else
      let name_start = idx + 7 in
      let j = ref name_start in
      while !j < len && String.unsafe_get s !j <> '}' do
        incr j
      done;
      if !j >= len then None
      else Some (String.sub s name_start (!j - name_start), !j + 1)
  in
  let rec skip_env_end name idx =
    let end_prefix = "\\end{" ^ name ^ "}" in
    let end_len = String.length end_prefix in
    if idx >= len then len
    else if (not (is_escaped idx)) && starts_with end_prefix idx then
      idx + end_len
    else skip_env_end name (idx + 1)
  in
  let in_dollar = ref false in
  let dollar_start = ref 0 in
  let rec loop i =
    if i >= len then ()
    else if !in_dollar then
      if (not (is_escaped i)) && s.[i] = '$' then (
        segments := String.sub s !dollar_start (i - !dollar_start) :: !segments;
        in_dollar := false;
        loop (i + 1))
      else loop (i + 1)
    else if (not (is_escaped i)) && s.[i] = '$' then (
      in_dollar := true;
      dollar_start := i + 1;
      loop (i + 1))
    else if (not (is_escaped i)) && starts_with "\\(" i then (
      let start = i + 2 in
      let j = ref start in
      while
        !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\)" !j)
      do
        incr j
      done;
      if !j < len - 1 then (
        segments := String.sub s start (!j - start) :: !segments;
        loop (!j + 2))
      else loop (i + 1))
    else if (not (is_escaped i)) && starts_with "\\[" i then (
      let start = i + 2 in
      let j = ref start in
      while
        !j < len - 1 && not ((not (is_escaped !j)) && starts_with "\\]" !j)
      do
        incr j
      done;
      if !j < len - 1 then (
        segments := String.sub s start (!j - start) :: !segments;
        loop (!j + 2))
      else loop (i + 1))
    else if (not (is_escaped i)) && starts_with "\\begin{" i then
      match parse_begin i with
      | Some (name, after_begin) when is_math_env name ->
          let end_pos = skip_env_end name after_begin in
          let end_tag = "\\end{" ^ name ^ "}" in
          let content_end = end_pos - String.length end_tag in
          if content_end > after_begin then
            segments :=
              String.sub s after_begin (content_end - after_begin) :: !segments;
          loop end_pos
      | _ -> loop (i + 1)
    else loop (i + 1)
  in
  loop 0;
  List.rev !segments

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
  { id = "DELIM-001"; run }

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
  { id = "DELIM-002"; run }

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
  { id = "DELIM-003"; run }

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
  { id = "DELIM-004"; run }

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
  { id = "DELIM-005"; run }

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
  { id = "DELIM-006"; run }

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
  { id = "DELIM-007"; run }

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
  { id = "DELIM-008"; run }

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
  { id = "DELIM-009"; run }

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
  { id = "DELIM-010"; run }

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
  { id = "DELIM-011"; run }

(* ═══════════════════════════════════════════════════════════════════════════
   SCRIPT family — L1 subscript / superscript validators SCRIPT-001 through
   SCRIPT-022
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Helper: extract inline math segments only ($...$ and \(...\)) *)
let extract_inline_math_segments (s : string) : string list =
  let len = String.length s in
  let segments = ref [] in
  let starts_with prefix idx =
    let plen = String.length prefix in
    idx + plen <= len && String.sub s idx plen = prefix
  in
  let is_escaped idx =
    let rec count back acc =
      if back < 0 then acc
      else if String.unsafe_get s back = '\\' then count (back - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let i = ref 0 in
  while !i < len do
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
        segments := String.sub s start (!j - start) :: !segments;
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
        segments := String.sub s start (!j - start) :: !segments;
        i := !j + 2)
      else i := !i + 1)
    else incr i
  done;
  List.rev !segments

(* Helper: count regex matches in a string *)
let count_re_matches (re : Str.regexp) (s : string) : int =
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
  { id = "SCRIPT-001"; run }

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
  { id = "SCRIPT-002"; run }

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
  { id = "SCRIPT-003"; run }

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
  { id = "SCRIPT-004"; run }

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
  { id = "SCRIPT-005"; run }

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
  { id = "SCRIPT-006"; run }

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
  { id = "SCRIPT-007"; run }

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
  { id = "SCRIPT-008"; run }

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
  { id = "SCRIPT-009"; run }

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
  { id = "SCRIPT-010"; run }

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
  { id = "SCRIPT-011"; run }

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
  { id = "SCRIPT-012"; run }

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
  { id = "SCRIPT-013"; run }

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
  { id = "SCRIPT-014"; run }

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
  { id = "SCRIPT-015"; run }

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
  { id = "SCRIPT-016"; run }

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
  { id = "SCRIPT-017"; run }

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
  { id = "SCRIPT-018"; run }

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
  { id = "SCRIPT-019"; run }

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
  { id = "SCRIPT-020"; run }

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
  { id = "SCRIPT-021"; run }

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
  { id = "SCRIPT-022"; run }

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
  { id = "MATH-009"; run }

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
  { id = "MATH-010"; run }

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
  { id = "MATH-011"; run }

(* MATH-012: Multi-letter function not in roman (\operatorname{}) — detects
   sequences of 2+ lowercase letters in math that look like function names but
   aren't standard operators *)
let l1_math_012_rule : rule =
  let re = Str.regexp {|\([a-z][a-z]+\)|} in
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
            let pos = Str.search_forward re seg !i in
            let matched = Str.matched_group 1 seg in
            let next_i = Str.match_end () in
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
  { id = "MATH-012"; run }

(* MATH-013: Differential d not typeset roman — detects bare 'd' before a
   variable in integrands, e.g. \int f(x) dx where d should be \mathrm{d} *)
let l1_math_013_rule : rule =
  let re = Str.regexp {| d\([A-Za-z]\)|} in
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
              let pos = Str.search_forward re seg !i in
              let next_i = Str.match_end () in
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
  { id = "MATH-013"; run }

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
  { id = "MATH-014"; run }

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
  { id = "MATH-015"; run }

(* MATH-016: Nested subscripts without braces — e.g. x_i_j instead of x_{i_j} or
   x_{i,j} *)
let l1_math_016_rule : rule =
  let re = Str.regexp {|_\([A-Za-z0-9]\)_|} in
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
  { id = "MATH-016"; run }

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
  { id = "MATH-017"; run }

(* MATH-018: π written numerically as 3.14... in math *)
let l1_math_018_rule : rule =
  let re = Str.regexp {|3\.14[0-9]*|} in
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
  { id = "MATH-018"; run }

(* MATH-019: Inline stacked ^_ order wrong — same concept as SCRIPT-021 but
   specifically for the pattern where _ immediately follows ^ without braces in
   inline math, e.g. $\sum^n_i$ instead of $\sum_{i}^{n}$ *)
let l1_math_019_rule : rule =
  let re = Str.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)_\({[^}]*}\|[A-Za-z0-9]\)|} in
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
  { id = "MATH-019"; run }

(* MATH-020: Missing \cdot between coefficient and vector — detects digit
   immediately followed by \vec or \mathbf without \cdot *)
let l1_math_020_rule : rule =
  let re = Str.regexp {|[0-9]\(\\vec{\|\\mathbf{\)|} in
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
  { id = "MATH-020"; run }

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
  { id = "MATH-021"; run }

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
  { id = "MATH-022"; run }

(* MATH-025: align environment with one column — use equation instead. Detects
   \begin{align}...\end{align} blocks with no & inside. *)
let l1_math_025_rule : rule =
  let re_begin = Str.regexp {|\\begin{align\*?}|} in
  let re_end = Str.regexp {|\\end{align\*?}|} in
  let run s =
    let cnt = ref 0 in
    let i = ref 0 in
    let n = String.length s in
    (try
       while !i < n do
         let pos = Str.search_forward re_begin s !i in
         let after_begin = pos + String.length (Str.matched_string s) in
         try
           let end_pos = Str.search_forward re_end s after_begin in
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
  { id = "MATH-025"; run }

(* MATH-028: Array environment inside math without column alignment spec.
   Detects \begin{array} without a brace argument following. *)
let l1_math_028_rule : rule =
  let re = Str.regexp {|\\begin{array}[^{]|} in
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
  { id = "MATH-028"; run }

(* MATH-029: Use of eqnarray / eqnarray* instead of align / align*. eqnarray is
   deprecated — spacing around = is wrong. *)
let l1_math_029_rule : rule =
  let re = Str.regexp {|\\begin{eqnarray\*?}|} in
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
          id = "MATH-029";
          severity = Warning;
          message = "Use of eqnarray* instead of align*";
          count = !cnt;
        }
    else None
  in
  { id = "MATH-029"; run }

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
  { id = "MATH-030"; run }

(* MATH-031: Operator spacing error — missing \; before \text in math *)
let l1_math_031_rule : rule =
  let re = Str.regexp {|[A-Za-z0-9}]\\text{|} in
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
  { id = "MATH-031"; run }

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
  { id = "MATH-033"; run }

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
  { id = "MATH-034"; run }

(* MATH-035: Multiple subscripts stacked vertically without braces — a_{i}_{j}
   pattern instead of a_{i,j} *)
let l1_math_035_rule : rule =
  let re = Str.regexp {|_\({[^}]*}\|[A-Za-z0-9]\)_|} in
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
  { id = "MATH-035"; run }

(* MATH-036: Superfluous \mathrm{} around single letter — \mathrm{x} is overkill
   for one letter *)
let l1_math_036_rule : rule =
  let re = Str.regexp {|\\mathrm{[A-Za-z]}|} in
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
  { id = "MATH-036"; run }

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
  { id = "MATH-037"; run }

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
  { id = "MATH-038"; run }

(* MATH-039: Stacked relational operators without \substack — detects patterns
   like \underset{x}{\overset{y}{=}} which should use \substack *)
let l1_math_039_rule : rule =
  let re = Str.regexp {|\\underset{[^}]*}{\\overset{|} in
  let re2 = Str.regexp {|\\overset{[^}]*}{\\underset{|} in
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
  { id = "MATH-039"; run }

(* MATH-040: Ellipsis \ldots used between operators on the center axis — should
   be \cdots for +, -, = etc. *)
let l1_math_040_rule : rule =
  let re = Str.regexp {|[+=<>-][ ]*\\ldots[ ]*[+=<>-]|} in
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
  { id = "MATH-040"; run }

(* MATH-041: Integral limits written inline in display — use \limits or
   \displaystyle \int for display integrals *)
let l1_math_041_rule : rule =
  let re = Str.regexp {|\\int_|} in
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
  { id = "MATH-041"; run }

(* MATH-042: Missing \, between number and unit in math — e.g. 5kg should be
   5\,\mathrm{kg} *)
let l1_math_042_rule : rule =
  let re = Str.regexp {|[0-9]\\mathrm{\|[0-9]\\text{\|[0-9]\\textrm{|} in
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
  { id = "MATH-042"; run }

(* MATH-043: Use of \text instead of \operatorname for function names in math —
   \text{Var} should be \operatorname{Var} *)
let l1_math_043_rule : rule =
  let re = Str.regexp {|\\text{[A-Z][a-z]+}|} in
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
  { id = "MATH-043"; run }

(* MATH-044: Binary relation typed as text char — e.g. < for \le, = for \equiv,
   etc., when text < > appear in math outside of delimiters *)
let l1_math_044_rule : rule =
  let re = Str.regexp {|[^\\]<=\|[^\\]>=|} in
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
  { id = "MATH-044"; run }

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
  { id = "MATH-045"; run }

(* MATH-046: Ellipsis \ldots on relation axis — prefer \cdots between commas, +
   etc. *)
let l1_math_046_rule : rule =
  let re = Str.regexp {|,[ ]*\\ldots[ ]*,|} in
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
  { id = "MATH-046"; run }

(* MATH-047: Double superscript without braces — a^b^c is a TeX error *)
let l1_math_047_rule : rule =
  let re = Str.regexp {|\^\({[^}]*}\|[A-Za-z0-9]\)\^|} in
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
  { id = "MATH-047"; run }

(* MATH-048: Boldface digits via \mathbf in math — \mathbf{1} etc. is typically
   unnecessary *)
let l1_math_048_rule : rule =
  let re = Str.regexp {|\\mathbf{[0-9]+}|} in
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
  { id = "MATH-048"; run }

(* MATH-049: Missing spacing around \times — detects a\times b without
   surrounding spaces *)
let l1_math_049_rule : rule =
  let re_no_space_before = Str.regexp {|[A-Za-z0-9}]\\times|} in
  let re_no_space_after = Str.regexp {|\\times[A-Za-z0-9{]|} in
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
  { id = "MATH-049"; run }

(* MATH-050: Circumflex accent \hat on multi-letter argument — \hat{abc} should
   typically be \widehat{abc} *)
let l1_math_050_rule : rule =
  let re = Str.regexp {|\\hat{[A-Za-z][A-Za-z]+}|} in
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
  { id = "MATH-050"; run }

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
  { id = "MATH-051"; run }

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
  { id = "MATH-052"; run }

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
  { id = "MATH-053"; run }

(* ═══════════════════════════════════════════════════════════════════════
   MATH-C validators: extended math checks (MATH-055..MATH-108)
   ═══════════════════════════════════════════════════════════════════════ *)

(* MATH-055: \mathcal for single character only — flag multi-char argument *)
let l1_math_055_rule : rule =
  let re = Str.regexp {|\\mathcal{[^}][^}]+}|} in
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
  { id = "MATH-055"; run }

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
  { id = "MATH-057"; run }

(* MATH-058: Nested \text inside \text *)
let l1_math_058_rule : rule =
  let re = Str.regexp {|\\text{[^}]*\\text{|} in
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
  { id = "MATH-058"; run }

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
  { id = "MATH-065"; run }

(* MATH-066: \phantom used; suggest \hphantom or \vphantom *)
let l1_math_066_rule : rule =
  let re = Str.regexp {|\\phantom{|} in
  let not_hv_re = Str.regexp {|\\[hv]phantom{|} in
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
  { id = "MATH-066"; run }

(* MATH-068: Spacing around \mid missing *)
let l1_math_068_rule : rule =
  let re = Str.regexp "[^ \t\n]\\\\mid\\|\\\\mid[^ \t\n]" in
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
  { id = "MATH-068"; run }

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
  { id = "MATH-069"; run }

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
  { id = "MATH-071"; run }

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
  { id = "MATH-078"; run }

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
  { id = "MATH-079"; run }

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
  { id = "MATH-082"; run }

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
  { id = "MATH-085"; run }

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
  { id = "MATH-094"; run }

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
  { id = "MATH-105"; run }

(* MATH-056: \operatorname duplicated for same function *)
let l1_math_056_rule : rule =
  let re = Str.regexp {|\\operatorname{[^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let names = ref [] in
        let i = ref 0 in
        try
          while true do
            let _ = Str.search_forward re seg !i in
            let m = Str.matched_string seg in
            if List.mem m !names then incr cnt else names := m :: !names;
            i := Str.match_end ()
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
  { id = "MATH-056"; run }

(* MATH-059: Math accent \bar on group expression needs braces *)
let l1_math_059_rule : rule =
  let re = Str.regexp {|\\bar{[^}]*[ +\-=][^}]*}|} in
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
  { id = "MATH-059"; run }

(* MATH-060: Differential d typeset italic — detect bare d in integral *)
let l1_math_060_rule : rule =
  let re = Str.regexp {|\\int[^$]*[^\\]d[xyzt ]|} in
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
  { id = "MATH-060"; run }

(* MATH-061: Log base missing braces \log_10x *)
let l1_math_061_rule : rule =
  let re = Str.regexp {|\\log_[0-9][0-9a-zA-Z]|} in
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
  { id = "MATH-061"; run }

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
  let re = Str.regexp {|\\limits|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let pos = Str.search_forward re seg !i in
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
            i := Str.match_end ()
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
  { id = "MATH-067"; run }

(* MATH-070: Multiline subscripts lack \substack *)
let l1_math_070_rule : rule =
  let re = Str.regexp {|_{[^}]*\\\\[^}]*}|} in
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
  { id = "MATH-070"; run }

(* MATH-073: \color used inside math *)
let l1_math_073_rule : rule =
  let re = Str.regexp {|\\color{|} in
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
  { id = "MATH-073"; run }

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
  { id = "MATH-077"; run }

(* MATH-081: Improper kerning f(x) — suggest f\!\left(x\right) *)
let l1_math_081_rule : rule =
  let re = Str.regexp {|[a-zA-Z]([^)]*)|} in
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
            let pos = Str.search_forward re seg !i in
            (* Check it's not preceded by \! and the letter is not part of a
               \cmd *)
            let has_kern =
              pos >= 2 && seg.[pos - 2] = '\\' && seg.[pos - 1] = '!'
            in
            if (not has_kern) && not (is_part_of_cmd seg pos) then incr cnt;
            i := Str.match_end ()
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
  { id = "MATH-081"; run }

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
  { id = "MATH-084"; run }

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
  { id = "MATH-086"; run }

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
  { id = "MATH-090"; run }

(* MATH-093: Multi-letter italic variable — suggest \mathit{} *)
let l1_math_093_rule : rule =
  let re = Str.regexp {|[^\\a-zA-Z{]\([a-zA-Z][a-zA-Z]+\)[^a-zA-Z}]|} in
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
            let _ = Str.search_forward re padded !i in
            let word = Str.matched_group 1 padded in
            if not (List.mem word known_funcs) then incr cnt;
            i := Str.match_end () - 1
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
  { id = "MATH-093"; run }

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
  { id = "MATH-098"; run }

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
  let re = Str.regexp {|\\operatorname{[^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _ = Str.search_forward re seg !i in
            let m = Str.matched_string seg in
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
            i := Str.match_end ()
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
  { id = "MATH-072"; run }

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
  { id = "MATH-074"; run }

(* MATH-087: Fake bold digits via \mathbf{0}...\mathbf{9} *)
let l1_math_087_rule : rule =
  let re = Str.regexp {|\\mathbf{[0-9]+}|} in
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
  { id = "MATH-087"; run }

(* MATH-088: Bare \partial lacks thin space *)
let l1_math_088_rule : rule =
  let re = Str.regexp "[^ \t,\\\\]\\\\partial\\|\\\\partial[^ \t{\\\\]" in
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
  { id = "MATH-088"; run }

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
  let re = Str.regexp {|\\operatorname{[^}]*}|} in
  let run s =
    let math_segs = extract_math_segments s in
    let cnt = ref 0 in
    List.iter
      (fun seg ->
        let i = ref 0 in
        try
          while true do
            let _ = Str.search_forward re seg !i in
            let m = Str.matched_string seg in
            let brace_start =
              (try String.index_from m 0 '{' with Not_found -> -1) + 1
            in
            let brace_end =
              try String.index_from m brace_start '}'
              with Not_found -> String.length m
            in
            let name = String.sub m brace_start (brace_end - brace_start) in
            if List.mem name known_ops then incr cnt;
            i := Str.match_end ()
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
  { id = "MATH-091"; run }

(* MATH-092: \sum with explicit limits in inline math *)
let l1_math_092_rule : rule =
  let re = Str.regexp "\\\\sum[ \t]*_" in
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
  { id = "MATH-092"; run }

(* MATH-095: Log base without braces — alias of MATH-061 logic *)
let l1_math_095_rule : rule =
  let re = Str.regexp {|\\log_[0-9][0-9a-zA-Z]|} in
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
  { id = "MATH-095"; run }

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
  { id = "MATH-096"; run }

(* MATH-097: Arrow => typed instead of \implies *)
let l1_math_097_rule : rule =
  let re = Str.regexp {|[^=!<>\\]=>|} in
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
  { id = "MATH-097"; run }

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
  { id = "MATH-099"; run }

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
  { id = "MATH-101"; run }

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
  { id = "MATH-104"; run }

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
  { id = "MATH-106"; run }

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
  { id = "MATH-108"; run }

(* ═══════════════════════════════════════════════════════════════════════ REF
   validators: cross-referencing and label hygiene
   ═══════════════════════════════════════════════════════════════════════ *)

(* Helper: extract all \label{...} values from source *)
let extract_labels (s : string) : string list =
  let re = Str.regexp {|\\label{[^}]*}|} in
  let labels = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _ = Str.search_forward re s !i in
       let m = Str.matched_string s in
       let next = Str.match_end () in
       (* extract content between { and } *)
       let inner = String.sub m 7 (String.length m - 8) in
       labels := inner :: !labels;
       i := next
     done
   with Not_found -> ());
  List.rev !labels

(* Helper: extract all \ref{...} and \eqref{...} label references *)
let extract_refs (s : string) : string list =
  let re = Str.regexp {|\\eqref{[^}]*}\|\\ref{[^}]*}|} in
  let refs = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _ = Str.search_forward re s !i in
       let m = Str.matched_string s in
       let next = Str.match_end () in
       (* Find the { and extract content *)
       let brace_pos = String.index m '{' in
       let inner =
         String.sub m (brace_pos + 1) (String.length m - brace_pos - 2)
       in
       refs := inner :: !refs;
       i := next
     done
   with Not_found -> ());
  List.rev !refs

(* REF-001: Undefined \ref/\eqref label after expansion *)
let l1_ref_001_rule : rule =
  let run s =
    let labels = extract_labels s in
    let refs = extract_refs s in
    let cnt = ref 0 in
    List.iter (fun r -> if not (List.mem r labels) then incr cnt) refs;
    if !cnt > 0 then
      Some
        {
          id = "REF-001";
          severity = Error;
          message = {|Undefined \ref / \eqref label after expansion|};
          count = !cnt;
        }
    else None
  in
  { id = "REF-001"; run }

(* REF-002: Duplicate label name *)
let l1_ref_002_rule : rule =
  let run s =
    let labels = extract_labels s in
    let seen = Hashtbl.create 16 in
    let cnt = ref 0 in
    List.iter
      (fun lbl ->
        if Hashtbl.mem seen lbl then incr cnt else Hashtbl.add seen lbl true)
      labels;
    if !cnt > 0 then
      Some
        {
          id = "REF-002";
          severity = Error;
          message = "Duplicate label name";
          count = !cnt;
        }
    else None
  in
  { id = "REF-002"; run }

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
  { id = "REF-003"; run }

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
  { id = "REF-004"; run }

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
  { id = "REF-005"; run }

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
  { id = "REF-006"; run }

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
  { id = "REF-007"; run }

(* REF-009: Reference appears before label definition (forward ref) *)
let l1_ref_009_rule : rule =
  let re_label = Str.regexp {|\\label{[^}]*}|} in
  let re_ref = Str.regexp {|\\eqref{[^}]*}\|\\ref{[^}]*}|} in
  let run s =
    let n = String.length s in
    (* Build map of first occurrence position for each label *)
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
    (* Check each ref — if it appears before its label, it's a forward ref *)
    let cnt = ref 0 in
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
         | Some label_pos -> if pos < label_pos then incr cnt
         | None -> () (* undefined ref — handled by REF-001 *));
         i := next
       done
     with Not_found -> ());
    if !cnt > 0 then
      Some
        {
          id = "REF-009";
          severity = Info;
          message = "Reference appears before label definition (forward ref)";
          count = !cnt;
        }
    else None
  in
  { id = "REF-009"; run }

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
  { id = "CHEM-001"; run }

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
  { id = "CHEM-002"; run }

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
  { id = "CHEM-003"; run }

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
  { id = "CHEM-004"; run }

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
  { id = "CHEM-005"; run }

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
  { id = "CHEM-006"; run }

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
  { id = "CHEM-007"; run }

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
  { id = "CHEM-008"; run }

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
  { id = "CHEM-009"; run }

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
  { id = "CMD-007"; run }

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
  { id = "CMD-010"; run }

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
  { id = "FONT-001"; run }

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
  { id = "FONT-004"; run }

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
  { id = "RTL-003"; run }

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
  { id = "RTL-004"; run }

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
  { id = "CJK-008"; run }

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
  { id = "CJK-015"; run }

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
  { id = "TYPO-059"; run }

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
  { id = "PT-002"; run }

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
  let run s =
    let preamble =
      try
        let idx =
          Str.search_forward (Str.regexp_string {|\begin{document}|}) s 0
        in
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
  { id = "L3-001"; run }

(* L3-002: Expl3 variable declared after \begin{document} *)
let l1_l3_002_rule : rule =
  let re_expl3_decl =
    Str.regexp {|\\[a-z]+_new:N\|\\[a-z]+_const:Nn\|\\[a-z]+_gset:Nn|}
  in
  let run s =
    let body =
      try
        let idx =
          Str.search_forward (Str.regexp_string {|\begin{document}|}) s 0
        in
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
  { id = "L3-002"; run }

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
  { id = "L3-003"; run }

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
  { id = "L3-004"; run }

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
  { id = "L3-005"; run }

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
  { id = "L3-006"; run }

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
  { id = "L3-007"; run }

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
  { id = "L3-009"; run }

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
  { id = "L3-011"; run }

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
  { id = "CMD-001"; run }

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
  { id = "CMD-003"; run }

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
    l1_l3_001_rule;
    l1_l3_002_rule;
    l1_l3_003_rule;
    l1_l3_004_rule;
    l1_l3_005_rule;
    l1_l3_006_rule;
    l1_l3_007_rule;
    l1_l3_009_rule;
    l1_l3_011_rule;
  ]
