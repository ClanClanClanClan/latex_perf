(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the strict-tier kernel L_S0 (ADR-012, M2 phase 1):
   [decide] (proofs/Strict/Decide.v) and [render] (proofs/Strict/Syntax.v) with
   their dependencies. Regenerate with
   scripts/tools/regen_strict_kernel_extract.sh from proofs/Strict/Extract.v.

   [decide] is proved equal, in both directions, to the declarative semantics
   [Runs] (strict_decider_exact; Print Assumptions: Closed). Nothing in the
   product links this module: phase 1 runs it only in the generated differential
   (scripts/tools/strict_differential.py via strict_decide.exe).

   nat is extracted to OCaml int (ExtrOcamlNatInt): the only nats are token
   positions, non-negative and bounded by the length of the token list. *)

[@@@warning "-a"]

let negb = function true -> false | false -> true

let app x =
  let rec app0 l m = match l with [] -> m | a :: l1 -> a :: app0 l1 m in
  app0 x

type comparison = Eq | Lt | Gt
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
type contract = { c_defined : name -> bool; c_sig : name -> signature option }

type frame =
  | FSimple
  | FShift of bool * bool * bool
  | FMGroup of bool * bool * bool

type state = { s_frames : frame list; s_out : bool; s_pos : int }

let init = { s_frames = []; s_out = false; s_pos = 0 }

type outcome = Compiles | Fatal of reason * int

let in_math = function
  | [] -> false
  | f :: _ -> (
      match f with
      | FSimple -> false
      | FShift (_, _, _) -> true
      | FMGroup (_, _, _) -> true)

let tail_has up = function
  | [] -> false
  | f :: _ -> (
      match f with
      | FSimple -> false
      | FShift (_, sp, sb) -> if up then sp else sb
      | FMGroup (_, sp, sb) -> if up then sp else sb)

let fresh_tail fs =
  match fs with
  | [] -> fs
  | f :: r -> (
      match f with
      | FSimple -> fs
      | FShift (d, _, _) -> FShift (d, false, false) :: r
      | FMGroup (g, _, _) -> FMGroup (g, false, false) :: r)

let mark_script up fs =
  match fs with
  | [] -> fs
  | f :: r -> (
      match f with
      | FSimple -> fs
      | FShift (d, sp, sb) ->
          FShift (d, (if up then true else sp), if up then sb else true) :: r
      | FMGroup (g, sp, sb) ->
          FMGroup (g, (if up then true else sp), if up then sb else true) :: r)

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
  | TCs n0 -> name_ok n0 && (negb (c.c_defined n0) || is_some (c.c_sig n0))
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

let in_strict_b c d =
  forallb (tok_ok c) (flatten_doc d) && scripts_ok (flatten_doc d)

type step_res = Go1 of state | Go2 of state | Stop of outcome | Stuck

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
      if in_math fs then Stop (Fatal (E6, p))
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
          | FShift (_, _, _) -> Stop (Fatal (E5, p))
          | FMGroup (_, _, _) ->
              Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }))
  | TDollar -> (
      match fs with
      | [] -> (
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
                    | TChar _ -> Stop (Fatal (E5, p))
                    | TSpace -> Stop (Fatal (E5, p))
                    | TPar _ -> Stop (Fatal (E5, p))
                    | TOpen -> Stop (Fatal (E5, p))
                    | TClose -> Stop (Fatal (E5, p))
                    | TDollar ->
                        Go2
                          {
                            s_frames = r;
                            s_out = o;
                            s_pos = Stdlib.Int.succ (Stdlib.Int.succ p);
                          }
                    | TMOpenInline -> Stop (Fatal (E5, p))
                    | TMCloseInline -> Stop (Fatal (E5, p))
                    | TMOpenDisplay -> Stop (Fatal (E5, p))
                    | TMCloseDisplay -> Stop (Fatal (E5, p))
                    | TScript _ -> Stop (Fatal (E5, p))
                    | TCs n0 ->
                        if c.c_defined n0 then
                          if is_some (c.c_sig n0) then Stop (Fatal (E5, p))
                          else Stuck
                        else Stop (Fatal (E1, Stdlib.Int.succ p))
                    | TEnd -> Stop (Fatal (E5, p)))
                | None -> Stop (Fatal (E5, p))
              else Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
          | FMGroup (_, _, _) -> Stop (Fatal (E5, p))))
  | TMOpenInline ->
      if in_math fs then Stop (Fatal (E5, p))
      else
        Go1
          {
            s_frames = FShift (false, false, false) :: fs;
            s_out = true;
            s_pos = Stdlib.Int.succ p;
          }
  | TMCloseInline -> (
      match fs with
      | [] -> Stop (Fatal (E5, p))
      | f :: r -> (
          match f with
          | FSimple -> Stop (Fatal (E5, p))
          | FShift (display, _, _) ->
              if display then Stop (Fatal (E5, p))
              else Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
          | FMGroup (_, _, _) -> Stop (Fatal (E5, p))))
  | TMOpenDisplay ->
      if in_math fs then Stop (Fatal (E5, p))
      else
        Go1
          {
            s_frames = FShift (true, false, false) :: fs;
            s_out = true;
            s_pos = Stdlib.Int.succ p;
          }
  | TMCloseDisplay -> (
      match fs with
      | [] -> Stop (Fatal (E5, p))
      | f :: r -> (
          match f with
          | FSimple -> Stop (Fatal (E5, p))
          | FShift (display, _, _) ->
              if display then
                Go1 { s_frames = r; s_out = o; s_pos = Stdlib.Int.succ p }
              else Stop (Fatal (E5, p))
          | FMGroup (_, _, _) -> Stop (Fatal (E5, p))))
  | TScript up -> (
      if negb (in_math fs) then Stop (Fatal (E3, p))
      else if tail_has up fs then Stop (Fatal (E4, p))
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
      if negb (c.c_defined n0) then Stop (Fatal (E1, p))
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
              | MxFatal r -> Stop (Fatal (r, p))
            else
              match sg.sig_text with
              | TxMaterial ->
                  Go1 { s_frames = fs; s_out = true; s_pos = Stdlib.Int.succ p }
              | TxNoop ->
                  Go1 { s_frames = fs; s_out = o; s_pos = Stdlib.Int.succ p }
              | TxFatal r -> Stop (Fatal (r, p)))
        | None -> Stuck)
  | TEnd ->
      if in_math fs then Stop (Fatal (E5, p))
      else if o then Stop Compiles
      else Stop (Fatal (E0, p))

let rec run c s = function
  | [] -> Some (Fatal (E5, s.s_pos))
  | t :: rest -> (
      match step c s t (hd_error rest) with
      | Go1 s' -> run c s' rest
      | Go2 s' -> ( match rest with [] -> None | _ :: rest' -> run c s' rest')
      | Stop o -> Some o
      | Stuck -> None)

type verdict = ProvenReady | ProvenNotReady of reason * int | NotStrict

let verdict_of = function
  | Some o -> (
      match o with
      | Compiles -> ProvenReady
      | Fatal (rs, l) -> ProvenNotReady (rs, l))
  | None -> NotStrict

let decide c d =
  if in_strict_b c d then verdict_of (run c init (flatten_doc d)) else NotStrict
