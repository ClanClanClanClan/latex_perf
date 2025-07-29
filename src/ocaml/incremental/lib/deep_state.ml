(* deep_state.ml - Complete LaTeX state tracking for accurate incremental processing *)

type catcode = 
  | Escape      (* 0 - backslash *)
  | BeginGroup  (* 1 - { *)
  | EndGroup    (* 2 - } *)
  | MathShift   (* 3 - $ *)
  | Alignment   (* 4 - & *)
  | EndOfLine   (* 5 - ^^M *)
  | Parameter   (* 6 - # *)
  | Superscript (* 7 - ^ *)
  | Subscript   (* 8 - _ *)
  | Ignored     (* 9 *)
  | Space       (* 10 *)
  | Letter      (* 11 *)
  | Other       (* 12 *)
  | Active      (* 13 - ~ *)
  | Comment     (* 14 - % *)
  | Invalid     (* 15 *)

type math_mode =
  | NoMath
  | InlineMath    (* $...$ *)
  | DisplayMath   (* $$...$$ *)
  | EquationMath  (* \[...\] or \begin{equation} *)

type environment = {
  name : string;
  verbatim : bool;
  math : bool;
  start_line : int;
}

type conditional_state = {
  if_level : int;
  if_stack : bool list;
  else_seen : bool list;
}

type deep_lexer_state = {
  (* Position *)
  line_no : int;
  col_no : int;
  byte_offset : int;
  
  (* Character categories - full TeX catcode table *)
  catcodes : catcode array;  (* 256 entries *)
  
  (* Environment tracking *)
  env_stack : environment list;
  in_verbatim : bool;
  verbatim_end : string option;  (* e.g., "\end{verbatim}" *)
  
  (* Math mode tracking *)
  math_mode : math_mode;
  math_delim_stack : string list;  (* For nested math *)
  
  (* Comment state *)
  in_comment : bool;
  comment_char : char;  (* Usually % but can be changed *)
  
  (* Conditional processing *)
  conditionals : conditional_state;
  
  (* Special modes *)
  in_csname : bool;  (* After \csname *)
  escape_char : char;  (* Usually \ but can be changed *)
  
  (* Grouping *)
  group_level : int;
  group_catcode_stack : catcode array list;  (* Save catcodes per group *)
  
  (* Hash for fast comparison *)
  mutable state_hash : int64 option;
}

(* Initialize with standard LaTeX catcodes *)
let make_initial_catcodes () =
  let cats = Array.make 256 Other in
  (* Set standard catcodes *)
  cats.(Char.code '\\') <- Escape;
  cats.(Char.code '{') <- BeginGroup;
  cats.(Char.code '}') <- EndGroup;
  cats.(Char.code '$') <- MathShift;
  cats.(Char.code '&') <- Alignment;
  cats.(Char.code '\n') <- EndOfLine;
  cats.(Char.code '#') <- Parameter;
  cats.(Char.code '^') <- Superscript;
  cats.(Char.code '_') <- Subscript;
  cats.(Char.code ' ') <- Space;
  cats.(Char.code '\t') <- Space;
  cats.(Char.code '~') <- Active;
  cats.(Char.code '%') <- Comment;
  
  (* Letters *)
  for i = Char.code 'a' to Char.code 'z' do
    cats.(i) <- Letter
  done;
  for i = Char.code 'A' to Char.code 'Z' do
    cats.(i) <- Letter
  done;
  
  cats

let init_deep_state = {
  line_no = 0;
  col_no = 0;
  byte_offset = 0;
  catcodes = make_initial_catcodes ();
  env_stack = [];
  in_verbatim = false;
  verbatim_end = None;
  math_mode = NoMath;
  math_delim_stack = [];
  in_comment = false;
  comment_char = '%';
  conditionals = { if_level = 0; if_stack = []; else_seen = [] };
  in_csname = false;
  escape_char = '\\';
  group_level = 0;
  group_catcode_stack = [];
  state_hash = None;
}

(* Deep state comparison for convergence detection *)
let rec states_equal s1 s2 =
  s1.line_no = s2.line_no &&
  s1.col_no = s2.col_no &&
  s1.catcodes = s2.catcodes &&  (* Array physical equality if unchanged *)
  environments_equal s1.env_stack s2.env_stack &&
  s1.in_verbatim = s2.in_verbatim &&
  s1.verbatim_end = s2.verbatim_end &&
  s1.math_mode = s2.math_mode &&
  s1.math_delim_stack = s2.math_delim_stack &&
  s1.in_comment = s2.in_comment &&
  s1.conditionals.if_level = s2.conditionals.if_level &&
  s1.conditionals.if_stack = s2.conditionals.if_stack &&
  s1.in_csname = s2.in_csname &&
  s1.group_level = s2.group_level

and environments_equal env1 env2 =
  match env1, env2 with
  | [], [] -> true
  | e1::rest1, e2::rest2 ->
      e1.name = e2.name &&
      e1.verbatim = e2.verbatim &&
      e1.math = e2.math &&
      environments_equal rest1 rest2
  | _ -> false

(* Fast hash for quick comparison *)
let hash_deep_state state =
  match state.state_hash with
  | Some h -> h
  | None ->
      let h = ref 0L in
      (* Hash major state components *)
      h := Int64.(add (mul !h 31L) (of_int state.line_no));
      h := Int64.(add (mul !h 31L) (of_int state.col_no));
      h := Int64.(add (mul !h 31L) (of_int (if state.in_verbatim then 1 else 0)));
      h := Int64.(add (mul !h 31L) (of_int (Hashtbl.hash state.math_mode)));
      h := Int64.(add (mul !h 31L) (of_int state.group_level));
      h := Int64.(add (mul !h 31L) (of_int (List.length state.env_stack)));
      
      (* Hash catcode table (only non-default entries) *)
      let default_cats = make_initial_catcodes () in
      for i = 0 to 255 do
        if state.catcodes.(i) <> default_cats.(i) then
          h := Int64.(add (mul !h 31L) (of_int i));
      done;
      
      state.state_hash <- Some !h;
      !h

(* State transitions *)
let enter_group state =
  { state with
    group_level = state.group_level + 1;
    group_catcode_stack = Array.copy state.catcodes :: state.group_catcode_stack;
    state_hash = None;
  }

let exit_group state =
  match state.group_catcode_stack with
  | [] -> state  (* Error: unmatched } *)
  | saved_cats :: rest ->
      { state with
        group_level = state.group_level - 1;
        catcodes = saved_cats;
        group_catcode_stack = rest;
        state_hash = None;
      }

let enter_math_mode state mode delim =
  { state with
    math_mode = mode;
    math_delim_stack = delim :: state.math_delim_stack;
    state_hash = None;
  }

let exit_math_mode state =
  match state.math_delim_stack with
  | [] -> state  (* Error: unmatched math delimiter *)
  | _ :: rest ->
      let new_mode = 
        match rest with
        | [] -> NoMath
        | "$" :: _ -> InlineMath
        | "$$" :: _ -> DisplayMath
        | _ -> EquationMath
      in
      { state with
        math_mode = new_mode;
        math_delim_stack = rest;
        state_hash = None;
      }

let enter_environment state name =
  let env = {
    name = name;
    verbatim = List.mem name ["verbatim"; "lstlisting"; "minted"; "Verbatim"];
    math = List.mem name ["equation"; "equation*"; "align"; "align*"; 
                          "gather"; "gather*"; "multline"; "multline*"];
    start_line = state.line_no;
  } in
  let new_state = { state with 
    env_stack = env :: state.env_stack;
    state_hash = None;
  } in
  
  if env.verbatim then
    { new_state with 
      in_verbatim = true;
      verbatim_end = Some ("\\end{" ^ name ^ "}");
    }
  else if env.math then
    enter_math_mode new_state EquationMath ("\\begin{" ^ name ^ "}")
  else
    new_state

let exit_environment state name =
  match state.env_stack with
  | [] -> state  (* Error: unmatched \end *)
  | env :: rest when env.name = name ->
      let new_state = { state with 
        env_stack = rest;
        state_hash = None;
      } in
      
      if env.verbatim then
        { new_state with 
          in_verbatim = List.exists (fun e -> e.verbatim) rest;
          verbatim_end = 
            match List.find_opt (fun e -> e.verbatim) rest with
            | Some e -> Some ("\\end{" ^ e.name ^ "}")
            | None -> None
        }
      else if env.math then
        exit_math_mode new_state
      else
        new_state
  | _ -> state  (* Error: mismatched environment *)

let change_catcode state char new_cat =
  let new_cats = Array.copy state.catcodes in
  new_cats.(Char.code char) <- new_cat;
  { state with 
    catcodes = new_cats;
    state_hash = None;
  }

(* Check if state has stabilized enough to stop processing *)
let state_stabilized old_state new_state =
  (* Quick hash check first *)
  hash_deep_state old_state = hash_deep_state new_state ||
  (* Deep equality as fallback *)
  states_equal old_state new_state

(* Estimate reprocessing distance based on state change *)
let estimate_affected_distance state1 state2 =
  if state1.in_verbatim <> state2.in_verbatim then
    1000  (* Major change - process far *)
  else if state1.math_mode <> state2.math_mode then
    500   (* Math mode change - medium distance *)
  else if state1.group_level <> state2.group_level then
    200   (* Group change - small distance *)
  else if state1.env_stack <> state2.env_stack then
    300   (* Environment change *)
  else
    50    (* Minor change - process minimally *)