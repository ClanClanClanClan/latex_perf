(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the strict-tier kernel L_S0 (ADR-012, M2 phase 1):
   [decide] (proofs/Strict/Decide.v) and [render] (proofs/Strict/Syntax.v) with
   their dependencies. Regenerate with
   scripts/tools/regen_strict_kernel_extract.sh from proofs/Strict/Extract.v.

   [decide] is proved equal, in both directions, to the declarative semantics
   [Runs] (strict_decider_exact; Print Assumptions: Closed). Nothing in the
   product links this module: phase 1 runs it only in the generated differential
   (scripts/tools/strict_differential.py via strict_decide.exe).

   nat is extracted to OCaml int (ExtrOcamlNatInt): token positions,
   non-negative and bounded by the length of the token list, and TeX group
   counts (sums of small non-negative ints). *)

[@@@warning "-a"]

let negb = function true -> false | false -> true
let fst = function x, _ -> x

let length x =
  let rec length0 = function
    | [] -> 0
    | _ :: l' -> Stdlib.Int.succ (length0 l')
  in
  length0 x

let app x =
  let rec app0 l m = match l with [] -> m | a :: l1 -> a :: app0 l1 m in
  app0 x

type comparison = Eq | Lt | Gt

let pred n = Stdlib.max 0 (n - 1)
let rec add = ( + )

module Nat = struct
  let rec add n0 m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n0

  let rec mul n0 m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  let ltb n0 m = Stdlib.Int.succ n0 <= m

  let rec max n0 m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> m)
      (fun n' ->
        (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
          (fun _ -> n0)
          (fun m' -> Stdlib.Int.succ (max n' m'))
          m)
      n0
end

type positive = XI of positive | XO of positive | XH
type n = N0 | Npos of positive

module Pos = struct
  let rec succ = function XI p -> XO (succ p) | XO p -> XI p | XH -> XO XH

  let rec add x y =
    match x with
    | XI p -> (
        match y with
        | XI q -> XO (add_carry p q)
        | XO q -> XI (add p q)
        | XH -> XO (succ p))
    | XO p -> (
        match y with XI q -> XI (add p q) | XO q -> XO (add p q) | XH -> XI p)
    | XH -> ( match y with XI q -> XO (succ q) | XO q -> XI q | XH -> XO XH)

  and add_carry x y =
    match x with
    | XI p -> (
        match y with
        | XI q -> XI (add_carry p q)
        | XO q -> XO (add_carry p q)
        | XH -> XI (succ p))
    | XO p -> (
        match y with
        | XI q -> XO (add_carry p q)
        | XO q -> XI (add p q)
        | XH -> XO (succ p))
    | XH -> (
        match y with XI q -> XI (succ q) | XO q -> XO (succ q) | XH -> XI XH)

  let rec mul x y =
    match x with XI p -> add y (XO (mul p y)) | XO p -> XO (mul p y) | XH -> y

  let rec compare_cont r x y =
    match x with
    | XI p -> (
        match y with
        | XI q -> compare_cont r p q
        | XO q -> compare_cont Gt p q
        | XH -> Gt)
    | XO p -> (
        match y with
        | XI q -> compare_cont Lt p q
        | XO q -> compare_cont r p q
        | XH -> Gt)
    | XH -> ( match y with XI _ -> Lt | XO _ -> Lt | XH -> r)

  let compare = compare_cont Eq
end

module N = struct
  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> ( match m with N0 -> n0 | Npos q -> Npos (Pos.add p q))

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> ( match m with N0 -> N0 | Npos q -> Npos (Pos.mul p q))

  let compare n0 m =
    match n0 with
    | N0 -> ( match m with N0 -> Eq | Npos _ -> Lt)
    | Npos n' -> ( match m with N0 -> Gt | Npos m' -> Pos.compare n' m')
end

let hd_error = function [] -> None | x :: _ -> Some x

let map f =
  let rec map0 = function [] -> [] | a :: t -> f a :: map0 t in
  map0

let flat_map f =
  let rec flat_map0 = function [] -> [] | x :: t -> app (f x) (flat_map0 t) in
  flat_map0

let existsb f =
  let rec existsb0 = function [] -> false | a :: l0 -> f a || existsb0 l0 in
  existsb0

let forallb f =
  let rec forallb0 = function [] -> true | a :: l0 -> f a && forallb0 l0 in
  forallb0

let filter f =
  let rec filter0 = function
    | [] -> []
    | x :: l0 -> if f x then x :: filter0 l0 else filter0 l0
  in
  filter0

let compare0 c1 c2 =
  let cmp = Char.compare c1 c2 in
  if cmp < 0 then Lt else if cmp = 0 then Eq else Gt

let rec list_ascii_of_string = function
  | [] -> []
  | ch :: s0 -> ch :: list_ascii_of_string s0

type name = char list
type math_kind = MkDollar | MkDisplayDollar | MkParen | MkBracket

type node =
  | NText of char list
  | NSpace
  | NPar of bool
  | NGroup of node list
  | NStrayClose
  | NMath of math_kind * node list
  | NScript of bool * node
  | NCmd of name

type doc = { d_body : node list; d_has_end : bool }

type tok =
  | TChar of char
  | TSpace
  | TPar of bool
  | TOpen
  | TClose
  | TDollar
  | TMOpenInline
  | TMCloseInline
  | TMOpenDisplay
  | TMCloseDisplay
  | TScript of bool
  | TCs of name
  | TEnd

let rec flatten_node = function
  | NText w -> map (fun x -> TChar x) w
  | NSpace -> TSpace :: []
  | NPar e -> TPar e :: []
  | NGroup b -> TOpen :: app (flat_map flatten_node b) (TClose :: [])
  | NStrayClose -> TClose :: []
  | NMath (k, b) -> (
      match k with
      | MkDollar -> TDollar :: app (flat_map flatten_node b) (TDollar :: [])
      | MkDisplayDollar ->
          TDollar
          :: TDollar
          :: app (flat_map flatten_node b) [ TDollar; TDollar ]
      | MkParen ->
          TMOpenInline :: app (flat_map flatten_node b) (TMCloseInline :: [])
      | MkBracket ->
          TMOpenDisplay :: app (flat_map flatten_node b) (TMCloseDisplay :: []))
  | NScript (up, a) -> TScript up :: flatten_node a
  | NCmd n1 -> TCs n1 :: []

let flatten_nodes l = flat_map flatten_node l

let flatten_doc d =
  app (flatten_nodes d.d_body) (if d.d_has_end then TEnd :: [] else [])

let nl = '\n'
let bs = '\\'

let render_tok = function
  | TChar c -> [ c; nl ]
  | TSpace -> ' ' :: []
  | TPar explicit -> if explicit then [ bs; 'p'; 'a'; 'r'; nl ] else [ nl; nl ]
  | TOpen -> [ '{'; nl ]
  | TClose -> [ '}'; nl ]
  | TDollar -> '$' :: []
  | TMOpenInline -> [ bs; '('; nl ]
  | TMCloseInline -> [ bs; ')'; nl ]
  | TMOpenDisplay -> [ bs; '['; nl ]
  | TMCloseDisplay -> [ bs; ']'; nl ]
  | TScript up -> if up then [ '^'; nl ] else [ '_'; nl ]
  | TCs n0 -> bs :: app n0 (nl :: [])
  | TEnd ->
      app
        (list_ascii_of_string
           [
             '\\';
             'e';
             'n';
             'd';
             '{';
             'd';
             'o';
             'c';
             'u';
             'm';
             'e';
             'n';
             't';
             '}';
           ])
        (nl :: [])

let header =
  app
    (list_ascii_of_string
       [
         '\\';
         'd';
         'o';
         'c';
         'u';
         'm';
         'e';
         'n';
         't';
         'c';
         'l';
         'a';
         's';
         's';
         '{';
         'a';
         'r';
         't';
         'i';
         'c';
         'l';
         'e';
         '}';
       ])
    (app (nl :: [])
       (app
          (list_ascii_of_string
             [
               '\\';
               'b';
               'e';
               'g';
               'i';
               'n';
               '{';
               'd';
               'o';
               'c';
               'u';
               'm';
               'e';
               'n';
               't';
               '}';
             ])
          (nl :: [])))

let render_toks ts = flat_map render_tok ts
let render d = app header (render_toks (flatten_doc d))

type reason = E0 | E1 | E3 | E4 | E5 | E6
type text_beh = TxMaterial | TxNoop | TxFatal of reason
type math_beh = MxNoad | MxNoop | MxFatal of reason
type signature = { sig_text : text_beh; sig_math : math_beh }
type longness = LLong | LShortInner | LShortOuter
type pay = PText of bool | PMath

type arg_text =
  | TFatalNow of reason
  | TFatalAfter of reason
  | TRun of bool * pay * int

type arg_math =
  | MFatalNow of reason
  | MFatalAfter of reason
  | MRun of pay * int

type asig = {
  as_long : longness;
  as_text : arg_text;
  as_math : arg_math;
  as_copy : int;
}

type contract = {
  c_defined : name -> bool;
  c_sig : name -> signature option;
  c_arg : name -> asig option;
  c_cost : tok -> int;
}

type frame =
  | FSimple
  | FShift of bool * bool * bool
  | FMGroup of bool * bool * bool
  | FArg of longness * pay * int * bool * bool

type state = { s_frames : frame list; s_out : bool; s_pos : int }

let init = { s_frames = []; s_out = false; s_pos = 0 }

type outcome = Compiles | Fatal of reason * int

let in_math = function
  | [] -> false
  | f :: _ -> (
      match f with
      | FSimple -> false
      | FShift (_, _, _) -> true
      | FMGroup (_, _, _) -> true
      | FArg (_, p, _, _, _) -> (
          match p with PText _ -> false | PMath -> true))

let tail_has up = function
  | [] -> false
  | f :: _ -> (
      match f with
      | FSimple -> false
      | FShift (_, sp, sb) -> if up then sp else sb
      | FMGroup (_, sp, sb) -> if up then sp else sb
      | FArg (_, p, _, sp, sb) -> (
          match p with PText _ -> false | PMath -> if up then sp else sb))

let fresh_tail fs =
  match fs with
  | [] -> fs
  | f :: r -> (
      match f with
      | FSimple -> fs
      | FShift (d, _, _) -> FShift (d, false, false) :: r
      | FMGroup (g, _, _) -> FMGroup (g, false, false) :: r
      | FArg (l, p, g, _, _) -> FArg (l, p, g, false, false) :: r)

let mark_script up fs =
  match fs with
  | [] -> fs
  | f :: r -> (
      match f with
      | FSimple -> fs
      | FShift (d, sp, sb) ->
          FShift (d, (if up then true else sp), if up then sb else true) :: r
      | FMGroup (g, sp, sb) ->
          FMGroup (g, (if up then true else sp), if up then sb else true) :: r
      | FArg (l, p, g, sp, sb) ->
          FArg (l, p, g, (if up then true else sp), if up then sb else true)
          :: r)

let mgroup_head = function
  | [] -> false
  | f :: _ -> (
      match f with
      | FSimple -> false
      | FShift (_, _, _) -> false
      | FMGroup (_, _, _) -> true
      | FArg (_, p, _, _, _) -> (
          match p with PText _ -> false | PMath -> true))

let rec restricted = function
  | [] -> false
  | f :: r -> (
      match f with
      | FSimple -> restricted r
      | FShift (_, _, _) -> false
      | FMGroup (_, _, _) -> false
      | FArg (_, p, _, _, _) -> ( match p with PText b -> b | PMath -> false))

let is_arg_frame = function
  | FSimple -> false
  | FShift (_, _, _) -> false
  | FMGroup (_, _, _) -> false
  | FArg (_, _, _, _, _) -> true

let is_brace = function
  | FSimple -> true
  | FShift (_, _, _) -> false
  | FMGroup (_, _, _) -> true
  | FArg (_, _, _, _, _) -> true

let short_frame = function
  | FSimple -> false
  | FShift (_, _, _) -> false
  | FMGroup (_, _, _) -> false
  | FArg (l, _, _, _, _) -> (
      match l with LLong -> false | LShortInner -> true | LShortOuter -> true)

let in_arg fs = existsb is_arg_frame fs

let rec arg_depth = function
  | [] -> 0
  | f :: r ->
      if in_arg r then
        if is_brace f then Stdlib.Int.succ (arg_depth r) else arg_depth r
      else if is_arg_frame f then Stdlib.Int.succ 0
      else 0

let rec short_depth = function
  | [] -> 0
  | f :: r ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> if short_frame f then arg_depth (f :: r) else 0)
        (fun n0 -> Stdlib.Int.succ n0)
        (short_depth r)

let rec outer_short = function
  | [] -> false
  | f :: r -> (
      if in_arg r then outer_short r
      else
        match f with
        | FSimple -> false
        | FShift (_, _, _) -> false
        | FMGroup (_, _, _) -> false
        | FArg (l, _, _, _, _) -> (
            match l with
            | LLong -> false
            | LShortInner -> false
            | LShortOuter -> true))

type scan = { sc_r : reason; sc_k : int; sc_sh : int; sc_ou : bool }

let start_scan fs r =
  {
    sc_r = r;
    sc_k = arg_depth fs;
    sc_sh = short_depth fs;
    sc_ou = outer_short fs;
  }

let close_sh k sh = if Nat.ltb k sh then 0 else sh

let in_range lo hi c =
  match compare0 lo c with
  | Eq -> ( match compare0 c hi with Eq -> true | Lt -> true | Gt -> false)
  | Lt -> ( match compare0 c hi with Eq -> true | Lt -> true | Gt -> false)
  | Gt -> false

let letter c = in_range 'A' 'Z' c || in_range 'a' 'z' c

let safe_char c =
  (letter c || in_range '0' '9' c)
  || existsb (( = ) c)
       [ '.'; ','; ';'; ':'; '!'; '?'; '('; ')'; '/'; '+'; '-'; '=' ]

let name_ok n0 = match n0 with [] -> false | _ :: _ -> forallb letter n0
let is_some = function Some _ -> true | None -> false

let tok_ok c = function
  | TChar c0 -> safe_char c0
  | TSpace -> true
  | TPar _ -> true
  | TOpen -> true
  | TClose -> true
  | TDollar -> true
  | TMOpenInline -> true
  | TMCloseInline -> true
  | TMOpenDisplay -> true
  | TMCloseDisplay -> true
  | TScript _ -> true
  | TCs n0 ->
      name_ok n0
      && ((negb (c.c_defined n0) || is_some (c.c_sig n0))
         || is_some (c.c_arg n0))
  | TEnd -> true

let rec scripts_ok = function
  | [] -> true
  | t :: rest -> (
      match t with
      | TChar _ -> scripts_ok rest
      | TSpace -> scripts_ok rest
      | TPar _ -> scripts_ok rest
      | TOpen -> scripts_ok rest
      | TClose -> scripts_ok rest
      | TDollar -> scripts_ok rest
      | TMOpenInline -> scripts_ok rest
      | TMCloseInline -> scripts_ok rest
      | TMOpenDisplay -> scripts_ok rest
      | TMCloseDisplay -> scripts_ok rest
      | TScript _ -> (
          match rest with
          | [] -> false
          | t0 :: _ -> (
              match t0 with
              | TChar _ -> scripts_ok rest
              | TSpace -> false
              | TPar _ -> false
              | TOpen -> scripts_ok rest
              | TClose -> false
              | TDollar -> false
              | TMOpenInline -> false
              | TMCloseInline -> false
              | TMOpenDisplay -> false
              | TMCloseDisplay -> false
              | TScript _ -> false
              | TCs _ -> false
              | TEnd -> false))
      | TCs _ -> scripts_ok rest
      | TEnd -> scripts_ok rest)

let is_argcmd c n0 =
  (c.c_defined n0 && negb (is_some (c.c_sig n0))) && is_some (c.c_arg n0)

let rec wfa c need = function
  | [] -> need = 0
  | t :: r -> (
      match t with
      | TChar _ -> wfa c need r
      | TSpace -> wfa c need r
      | TPar _ -> wfa c need r
      | TOpen -> wfa c (if need = 0 then 0 else Stdlib.Int.succ need) r
      | TClose -> wfa c (pred need) r
      | TDollar -> wfa c need r
      | TMOpenInline -> wfa c need r
      | TMCloseInline -> wfa c need r
      | TMOpenDisplay -> wfa c need r
      | TMCloseDisplay -> wfa c need r
      | TScript _ -> wfa c need r
      | TCs n0 ->
          if is_argcmd c n0 then
            match r with
            | [] -> false
            | t0 :: r' -> (
                match t0 with
                | TChar _ -> false
                | TSpace -> false
                | TPar _ -> false
                | TOpen -> wfa c (Stdlib.Int.succ need) r'
                | TClose -> false
                | TDollar -> false
                | TMOpenInline -> false
                | TMCloseInline -> false
                | TMOpenDisplay -> false
                | TMCloseDisplay -> false
                | TScript _ -> false
                | TCs _ -> false
                | TEnd -> false)
          else wfa c need r
      | TEnd -> need = 0)

type step_res =
  | Go1 of state
  | Go2 of state
  | Stop of outcome
  | Stuck
  | Defer of scan
  | Defer2 of scan

let halt fs r l =
  if in_arg fs then Defer (start_scan fs r) else Stop (Fatal (r, l))

let rec scan_run sc p = function
  | [] -> None
  | t :: rest -> (
      match t with
      | TChar _ -> scan_run sc (Stdlib.Int.succ p) rest
      | TSpace -> scan_run sc (Stdlib.Int.succ p) rest
      | TPar _ ->
          if sc.sc_ou then Some (Fatal (E6, p))
          else if sc.sc_sh = 0 then scan_run sc (Stdlib.Int.succ p) rest
          else
            scan_run
              { sc_r = E6; sc_k = sc.sc_k; sc_sh = sc.sc_sh; sc_ou = false }
              (Stdlib.Int.succ p) rest
      | TOpen ->
          scan_run
            {
              sc_r = sc.sc_r;
              sc_k = Stdlib.Int.succ sc.sc_k;
              sc_sh = sc.sc_sh;
              sc_ou = sc.sc_ou;
            }
            (Stdlib.Int.succ p) rest
      | TClose ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ -> None)
            (fun n0 ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ -> Some (Fatal (sc.sc_r, p)))
                (fun k ->
                  scan_run
                    {
                      sc_r = sc.sc_r;
                      sc_k = Stdlib.Int.succ k;
                      sc_sh = close_sh (Stdlib.Int.succ k) sc.sc_sh;
                      sc_ou = sc.sc_ou;
                    }
                    (Stdlib.Int.succ p) rest)
                n0)
            sc.sc_k
      | TDollar -> scan_run sc (Stdlib.Int.succ p) rest
      | TMOpenInline -> scan_run sc (Stdlib.Int.succ p) rest
      | TMCloseInline -> scan_run sc (Stdlib.Int.succ p) rest
      | TMOpenDisplay -> scan_run sc (Stdlib.Int.succ p) rest
      | TMCloseDisplay -> scan_run sc (Stdlib.Int.succ p) rest
      | TScript _ -> scan_run sc (Stdlib.Int.succ p) rest
      | TCs _ -> scan_run sc (Stdlib.Int.succ p) rest
      | TEnd -> None)

let step c s t nx =
  let fs = s.s_frames in
  let o = s.s_out in
  let p = s.s_pos in
  match t with
  | TChar _ ->
      if in_math fs then
        Go1 { s_frames = fresh_tail fs; s_out = o; s_pos = Stdlib.Int.succ p }
      else Go1 { s_frames = fs; s_out = true; s_pos = Stdlib.Int.succ p }
  | TSpace -> Go1 { s_frames = fs; s_out = o; s_pos = Stdlib.Int.succ p }
  | TPar _ ->
      if negb (short_depth fs = 0) then halt fs E6 p
      else if in_math fs then halt fs E6 p
      else Go1 { s_frames = fs; s_out = o; s_pos = Stdlib.Int.succ p }
  | TOpen ->
      if in_math fs then
        Go1
          {
            s_frames = FMGroup (false, false, false) :: fresh_tail fs;
            s_out = o;
            s_pos = Stdlib.Int.succ p;
          }
      else
        Go1 { s_frames = FSimple :: fs; s_out = o; s_pos = Stdlib.Int.succ p }
  | TClose -> (
      match fs with
      | [] -> Stop (Fatal (E5, p))
      | f :: r -> (
          match f with
          | FSimple ->
              Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
          | FShift (_, _, _) -> halt fs E5 p
          | FMGroup (_, _, _) ->
              Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
          | FArg (_, _, _, _, _) ->
              Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }))
  | TDollar -> (
      match fs with
      | [] -> (
          if mgroup_head fs then halt fs E5 p
          else if restricted fs then
            Go1
              {
                s_frames = FShift (false, false, false) :: fs;
                s_out = true;
                s_pos = Stdlib.Int.succ p;
              }
          else
            match nx with
            | Some t0 -> (
                match t0 with
                | TChar _ ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TSpace ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TPar _ ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TOpen ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TClose ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TDollar ->
                    Go2
                      {
                        s_frames = FShift (true, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                      }
                | TMOpenInline ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TMCloseInline ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TMOpenDisplay ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TMCloseDisplay ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TScript _ ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TCs _ ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      }
                | TEnd ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      })
            | None ->
                Go1
                  {
                    s_frames = FShift (false, false, false) :: fs;
                    s_out = true;
                    s_pos = Stdlib.Int.succ p;
                  })
      | f :: r -> (
          match f with
          | FSimple -> (
              if mgroup_head fs then halt fs E5 p
              else if restricted fs then
                Go1
                  {
                    s_frames = FShift (false, false, false) :: fs;
                    s_out = true;
                    s_pos = Stdlib.Int.succ p;
                  }
              else
                match nx with
                | Some t0 -> (
                    match t0 with
                    | TChar _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TSpace ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TPar _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TOpen ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TClose ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TDollar ->
                        Go2
                          {
                            s_frames = FShift (true, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                          }
                    | TMOpenInline ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMCloseInline ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMOpenDisplay ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMCloseDisplay ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TScript _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TCs _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TEnd ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          })
                | None ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      })
          | FShift (display, _, _) ->
              if display then
                match nx with
                | Some t0 -> (
                    match t0 with
                    | TChar _ -> halt fs E5 p
                    | TSpace -> halt fs E5 p
                    | TPar _ -> halt fs E5 p
                    | TOpen -> halt fs E5 p
                    | TClose -> halt fs E5 p
                    | TDollar ->
                        Go2
                          {
                            s_frames = r;
                            s_out = o;
                            s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                          }
                    | TMOpenInline -> halt fs E5 p
                    | TMCloseInline -> halt fs E5 p
                    | TMOpenDisplay -> halt fs E5 p
                    | TMCloseDisplay -> halt fs E5 p
                    | TScript _ -> halt fs E5 p
                    | TCs n0 ->
                        if c.c_defined n0 then
                          if is_some (c.c_sig n0) || is_some (c.c_arg n0) then
                            halt fs E5 p
                          else Stuck
                        else halt fs E1 (Stdlib.Int.succ p)
                    | TEnd -> halt fs E5 p)
                | None -> halt fs E5 p
              else Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
          | FMGroup (_, _, _) -> (
              if mgroup_head fs then halt fs E5 p
              else if restricted fs then
                Go1
                  {
                    s_frames = FShift (false, false, false) :: fs;
                    s_out = true;
                    s_pos = Stdlib.Int.succ p;
                  }
              else
                match nx with
                | Some t0 -> (
                    match t0 with
                    | TChar _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TSpace ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TPar _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TOpen ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TClose ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TDollar ->
                        Go2
                          {
                            s_frames = FShift (true, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                          }
                    | TMOpenInline ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMCloseInline ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMOpenDisplay ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMCloseDisplay ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TScript _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TCs _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TEnd ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          })
                | None ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      })
          | FArg (_, _, _, _, _) -> (
              if mgroup_head fs then halt fs E5 p
              else if restricted fs then
                Go1
                  {
                    s_frames = FShift (false, false, false) :: fs;
                    s_out = true;
                    s_pos = Stdlib.Int.succ p;
                  }
              else
                match nx with
                | Some t0 -> (
                    match t0 with
                    | TChar _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TSpace ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TPar _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TOpen ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TClose ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TDollar ->
                        Go2
                          {
                            s_frames = FShift (true, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                          }
                    | TMOpenInline ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMCloseInline ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMOpenDisplay ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TMCloseDisplay ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TScript _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TCs _ ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          }
                    | TEnd ->
                        Go1
                          {
                            s_frames = FShift (false, false, false) :: fs;
                            s_out = true;
                            s_pos = Stdlib.Int.succ p;
                          })
                | None ->
                    Go1
                      {
                        s_frames = FShift (false, false, false) :: fs;
                        s_out = true;
                        s_pos = Stdlib.Int.succ p;
                      })))
  | TMOpenInline ->
      if in_math fs then halt fs E5 p
      else
        Go1
          {
            s_frames = FShift (false, false, false) :: fs;
            s_out = true;
            s_pos = Stdlib.Int.succ p;
          }
  | TMCloseInline -> (
      match fs with
      | [] -> halt fs E5 p
      | f :: r -> (
          match f with
          | FSimple -> halt fs E5 p
          | FShift (display, _, _) ->
              if display then halt fs E5 p
              else Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
          | FMGroup (_, _, _) -> halt fs E5 p
          | FArg (_, _, _, _, _) -> halt fs E5 p))
  | TMOpenDisplay ->
      if in_math fs then halt fs E5 p
      else if restricted fs then
        Go1 { s_frames = fs; s_out = o; s_pos = Stdlib.Int.succ p }
      else
        Go1
          {
            s_frames = FShift (true, false, false) :: fs;
            s_out = true;
            s_pos = Stdlib.Int.succ p;
          }
  | TMCloseDisplay -> (
      match fs with
      | [] -> halt fs E5 p
      | f :: r -> (
          match f with
          | FSimple -> halt fs E5 p
          | FShift (display, _, _) ->
              if display then
                Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
              else halt fs E5 p
          | FMGroup (_, _, _) -> halt fs E5 p
          | FArg (_, _, _, _, _) -> halt fs E5 p))
  | TScript up -> (
      if negb (in_math fs) then halt fs E3 p
      else if tail_has up fs then halt fs E4 p
      else
        match nx with
        | Some t0 -> (
            match t0 with
            | TChar _ ->
                Go2
                  {
                    s_frames = mark_script up fs;
                    s_out = o;
                    s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                  }
            | TSpace -> Stuck
            | TPar _ -> Stuck
            | TOpen ->
                Go2
                  {
                    s_frames = FMGroup (true, false, false) :: mark_script up fs;
                    s_out = o;
                    s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                  }
            | TClose -> Stuck
            | TDollar -> Stuck
            | TMOpenInline -> Stuck
            | TMCloseInline -> Stuck
            | TMOpenDisplay -> Stuck
            | TMCloseDisplay -> Stuck
            | TScript _ -> Stuck
            | TCs _ -> Stuck
            | TEnd -> Stuck)
        | None -> Stuck)
  | TCs n0 -> (
      if negb (c.c_defined n0) then halt fs E1 p
      else
        match c.c_sig n0 with
        | Some sg -> (
            if in_math fs then
              match sg.sig_math with
              | MxNoad ->
                  Go1
                    {
                      s_frames = fresh_tail fs;
                      s_out = o;
                      s_pos = Stdlib.Int.succ p;
                    }
              | MxNoop ->
                  Go1 { s_frames = fs; s_out = o; s_pos = Stdlib.Int.succ p }
              | MxFatal r -> halt fs r p
            else
              match sg.sig_text with
              | TxMaterial ->
                  Go1 { s_frames = fs; s_out = true; s_pos = Stdlib.Int.succ p }
              | TxNoop ->
                  Go1 { s_frames = fs; s_out = o; s_pos = Stdlib.Int.succ p }
              | TxFatal r -> halt fs r p)
        | None -> (
            match c.c_arg n0 with
            | Some a -> (
                if in_math fs then
                  match a.as_math with
                  | MFatalNow r -> halt fs r p
                  | MFatalAfter r -> (
                      match nx with
                      | Some t0 -> (
                          match t0 with
                          | TChar _ -> Stuck
                          | TSpace -> Stuck
                          | TPar _ -> Stuck
                          | TOpen ->
                              Defer2
                                (start_scan
                                   (FArg
                                      (a.as_long, PText false, 0, false, false)
                                   :: fs)
                                   r)
                          | TClose -> Stuck
                          | TDollar -> Stuck
                          | TMOpenInline -> Stuck
                          | TMCloseInline -> Stuck
                          | TMOpenDisplay -> Stuck
                          | TMCloseDisplay -> Stuck
                          | TScript _ -> Stuck
                          | TCs _ -> Stuck
                          | TEnd -> Stuck)
                      | None -> Stuck)
                  | MRun (pl, g) -> (
                      match nx with
                      | Some t0 -> (
                          match t0 with
                          | TChar _ -> Stuck
                          | TSpace -> Stuck
                          | TPar _ -> Stuck
                          | TOpen ->
                              Go2
                                {
                                  s_frames =
                                    FArg (a.as_long, pl, g, false, false)
                                    :: fresh_tail fs;
                                  s_out = o;
                                  s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                                }
                          | TClose -> Stuck
                          | TDollar -> Stuck
                          | TMOpenInline -> Stuck
                          | TMCloseInline -> Stuck
                          | TMOpenDisplay -> Stuck
                          | TMCloseDisplay -> Stuck
                          | TScript _ -> Stuck
                          | TCs _ -> Stuck
                          | TEnd -> Stuck)
                      | None -> Stuck)
                else
                  match a.as_text with
                  | TFatalNow r -> halt fs r p
                  | TFatalAfter r -> (
                      match nx with
                      | Some t0 -> (
                          match t0 with
                          | TChar _ -> Stuck
                          | TSpace -> Stuck
                          | TPar _ -> Stuck
                          | TOpen ->
                              Defer2
                                (start_scan
                                   (FArg
                                      (a.as_long, PText false, 0, false, false)
                                   :: fs)
                                   r)
                          | TClose -> Stuck
                          | TDollar -> Stuck
                          | TMOpenInline -> Stuck
                          | TMCloseInline -> Stuck
                          | TMOpenDisplay -> Stuck
                          | TMCloseDisplay -> Stuck
                          | TScript _ -> Stuck
                          | TCs _ -> Stuck
                          | TEnd -> Stuck)
                      | None -> Stuck)
                  | TRun (m, pl, g) -> (
                      match nx with
                      | Some t0 -> (
                          match t0 with
                          | TChar _ -> Stuck
                          | TSpace -> Stuck
                          | TPar _ -> Stuck
                          | TOpen ->
                              Go2
                                {
                                  s_frames =
                                    FArg (a.as_long, pl, g, false, false) :: fs;
                                  s_out = o || m;
                                  s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                                }
                          | TClose -> Stuck
                          | TDollar -> Stuck
                          | TMOpenInline -> Stuck
                          | TMCloseInline -> Stuck
                          | TMOpenDisplay -> Stuck
                          | TMCloseDisplay -> Stuck
                          | TScript _ -> Stuck
                          | TCs _ -> Stuck
                          | TEnd -> Stuck)
                      | None -> Stuck))
            | None -> Stuck))
  | TEnd ->
      if in_arg fs then Stuck
      else if in_math fs then Stop (Fatal (E5, p))
      else if o then Stop Compiles
      else Stop (Fatal (E0, p))

let rec run c s = function
  | [] -> Some (Fatal (E5, s.s_pos))
  | t :: rest -> (
      match step c s t (hd_error rest) with
      | Go1 s' -> run c s' rest
      | Go2 s' -> ( match rest with [] -> None | _ :: rest' -> run c s' rest')
      | Stop o -> Some o
      | Stuck -> None
      | Defer sc -> scan_run sc s.s_pos (t :: rest)
      | Defer2 sc -> (
          match rest with
          | [] -> None
          | _ :: rest' ->
              scan_run sc (Stdlib.Int.succ (Stdlib.Int.succ s.s_pos)) rest'))

let ten =
  Stdlib.Int.succ
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))

let max_groups = Nat.mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Nat.mul ten ten)
let max_tokens = Nat.mul max_groups (Nat.mul ten ten)
let max_name = Nat.mul ten ten
let max_mem = Nat.mul max_tokens (Nat.mul ten ten)

let frame_groups = function
  | FSimple -> Stdlib.Int.succ 0
  | FShift (_, _, _) -> Stdlib.Int.succ 0
  | FMGroup (_, _, _) -> Stdlib.Int.succ 0
  | FArg (_, _, g, _, _) -> g

let rec groups = function [] -> 0 | f :: r -> add (frame_groups f) (groups r)

let rec peak c s = function
  | [] -> groups s.s_frames
  | t :: rest ->
      Nat.max (groups s.s_frames)
        (match step c s t (hd_error rest) with
        | Go1 s' -> peak c s' rest
        | Go2 s' -> ( match rest with [] -> 0 | _ :: rest' -> peak c s' rest')
        | Stop _ -> 0
        | Stuck -> 0
        | Defer _ -> 0
        | Defer2 _ -> 0)

let short_names ts =
  forallb
    (fun t ->
      match t with
      | TChar _ -> true
      | TSpace -> true
      | TPar _ -> true
      | TOpen -> true
      | TClose -> true
      | TDollar -> true
      | TMOpenInline -> true
      | TMCloseInline -> true
      | TMOpenDisplay -> true
      | TMCloseDisplay -> true
      | TScript _ -> true
      | TCs n0 -> length n0 <= max_name
      | TEnd -> true)
    ts

let copy_of c n0 = match c.c_arg n0 with Some a -> a.as_copy | None -> 0

let rec open_copies = function
  | [] -> 0
  | p :: r ->
      let _, c = p in
      add c (open_copies r)

let rec held_from c b opens = function
  | [] -> 0
  | t :: r ->
      add (open_copies opens)
        (match t with
        | TChar _ -> held_from c b opens r
        | TSpace -> held_from c b opens r
        | TPar _ -> held_from c b opens r
        | TOpen -> held_from c (Stdlib.Int.succ b) opens r
        | TClose ->
            held_from c (pred b)
              (filter (fun x -> Nat.ltb (fst x) (pred b)) opens)
              r
        | TDollar -> held_from c b opens r
        | TMOpenInline -> held_from c b opens r
        | TMCloseInline -> held_from c b opens r
        | TMOpenDisplay -> held_from c b opens r
        | TMCloseDisplay -> held_from c b opens r
        | TScript _ -> held_from c b opens r
        | TCs n0 ->
            if is_argcmd c n0 then
              match r with
              | [] -> held_from c b opens r
              | t0 :: r' -> (
                  match t0 with
                  | TChar _ -> held_from c b opens r
                  | TSpace -> held_from c b opens r
                  | TPar _ -> held_from c b opens r
                  | TOpen ->
                      add (open_copies opens)
                        (held_from c (Stdlib.Int.succ b)
                           ((b, copy_of c n0) :: opens)
                           r')
                  | TClose -> held_from c b opens r
                  | TDollar -> held_from c b opens r
                  | TMOpenInline -> held_from c b opens r
                  | TMCloseInline -> held_from c b opens r
                  | TMOpenDisplay -> held_from c b opens r
                  | TMCloseDisplay -> held_from c b opens r
                  | TScript _ -> held_from c b opens r
                  | TCs _ -> held_from c b opens r
                  | TEnd -> held_from c b opens r)
            else held_from c b opens r
        | TEnd -> held_from c b opens r)

let held c ts = held_from c 0 [] ts

let rec node_cost c = function
  | [] -> 0
  | t :: r -> add (c.c_cost t) (node_cost c r)

let mem c ts = add (node_cost c ts) (held c ts)

let bounded c ts =
  ((length ts <= max_tokens && short_names ts) && peak c init ts <= max_groups)
  && mem c ts <= max_mem

let in_strict_b c d =
  ((forallb (tok_ok c) (flatten_doc d) && scripts_ok (flatten_doc d))
  && wfa c 0 (flatten_doc d))
  && bounded c (flatten_doc d)

type verdict = ProvenReady | ProvenNotReady of reason * int | NotStrict

let verdict_of = function
  | Some o -> (
      match o with
      | Compiles -> ProvenReady
      | Fatal (rs, l) -> ProvenNotReady (rs, l))
  | None -> NotStrict

let decide c d =
  if in_strict_b c d then verdict_of (run c init (flatten_doc d)) else NotStrict
