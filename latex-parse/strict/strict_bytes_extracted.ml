(* GENERATED — DO NOT EDIT BY HAND.

   Coq→OCaml extraction of the strict-tier decision on bytes (ADR-012, M2 phase
   2): [decide_bytes] (proofs/Strict/DecideBytes.v), the lexer [lex]
   (proofs/Strict/Lexer.v), the parser [parse] (proofs/Strict/Front.v) and the
   phase-1 kernel they run, with the diagnostic [explain]
   (proofs/Strict/Explain.v). Regenerate with
   scripts/tools/regen_strict_bytes_extract.sh from
   proofs/Strict/ExtractBytes.v.

   [decide_bytes] is proved equal to the declarative reading, parse and
   semantics (decide_bytes_exact, lex_exact, parse_exact; Print Assumptions:
   Closed). Nothing in the product links this module (M3 wires it): it runs in
   strict_decide.exe (file mode) and the byte-level evidence
   (scripts/tools/strict_differential.py --bytes).

   nat is extracted to OCaml int (ExtrOcamlNatInt): token positions, line
   numbers, byte offsets, lengths and TeX group counts, all non-negative. *)

[@@@warning "-a"]

let negb = function true -> false | false -> true
let option_map f = function Some a -> Some (f a) | None -> None

type ('a, 'b) sum = Inl of 'a | Inr of 'b

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

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n0
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

  let of_nat n0 =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> N0)
      (fun n' -> Npos (Pos.of_succ_nat n'))
      n0
end

let hd_error = function [] -> None | x :: _ -> Some x

let nth_error l =
  let rec nth_error0 l0 n0 =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> match l0 with [] -> None | x :: _ -> Some x)
      (fun n1 -> match l0 with [] -> None | _ :: l1 -> nth_error0 l1 n1)
      n0
  in
  nth_error0 l

let last l =
  let rec last0 l0 d =
    match l0 with
    | [] -> d
    | a :: l1 -> ( match l1 with [] -> a | _ :: _ -> last0 l1 d)
  in
  last0 l

let map f =
  let rec map0 = function [] -> [] | a :: t -> f a :: map0 t in
  map0

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

let zero = '\000'
let one = '\001'
let shift b c = Char.chr (((Char.code c lsl 1) land 255) + if b then 1 else 0)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> zero)
      (fun n' ->
        match p with
        | XI p' -> shift true (loop n' p')
        | XO p' -> shift false (loop n' p')
        | XH -> one)
      n0
  in
  loop
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))

let ascii_of_N = function N0 -> zero | Npos p -> ascii_of_pos p
let ascii_of_nat a = ascii_of_N (N.of_nat a)

let compare0 c1 c2 =
  let cmp = Char.compare c1 c2 in
  if cmp < 0 then Lt else if cmp = 0 then Eq else Gt

type name = char list

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
  c_dim : bool -> tok -> int;
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
      | FShift (_, sp0, sb) -> if up then sp0 else sb
      | FMGroup (_, sp0, sb) -> if up then sp0 else sb
      | FArg (_, p, _, sp0, sb) -> (
          match p with PText _ -> false | PMath -> if up then sp0 else sb))

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
      | FShift (d, sp0, sb) ->
          FShift (d, (if up then true else sp0), if up then sb else true) :: r
      | FMGroup (g, sp0, sb) ->
          FMGroup (g, (if up then true else sp0), if up then sb else true) :: r
      | FArg (l, p, g, sp0, sb) ->
          FArg (l, p, g, (if up then true else sp0), if up then sb else true)
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

let max_dim =
  Nat.mul
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
    (Nat.mul ten (Nat.mul ten ten))

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

let seg_start s = function
  | TChar _ -> false
  | TSpace -> false
  | TPar _ -> ( match s.s_frames with [] -> true | _ :: _ -> false)
  | TOpen -> false
  | TClose -> false
  | TDollar -> false
  | TMOpenInline -> false
  | TMCloseInline -> false
  | TMOpenDisplay -> false
  | TMCloseDisplay -> false
  | TScript _ -> false
  | TCs _ -> false
  | TEnd -> false

let maxl a b = if a <= b then b else a

let rec dim_run c s acc = function
  | [] -> acc
  | t :: rest ->
      let m = in_math s.s_frames in
      let a = if seg_start s t then c.c_dim m t else add acc (c.c_dim m t) in
      maxl a
        (match step c s t (hd_error rest) with
        | Go1 s' -> dim_run c s' a rest
        | Go2 s' -> (
            match rest with
            | [] -> a
            | t2 :: rest' -> dim_run c s' (add a (c.c_dim m t2)) rest')
        | Stop _ -> a
        | Stuck -> a
        | Defer _ -> a
        | Defer2 _ -> a)

let dim c ts = dim_run c init (c.c_dim false (TPar false)) ts

let bounded c ts =
  (((length ts <= max_tokens && short_names ts) && peak c init ts <= max_groups)
  && mem c ts <= max_mem)
  && dim c ts <= max_dim

type verdict = ProvenReady | ProvenNotReady of reason * int | NotStrict

type cat =
  | CEscape
  | CBgroup
  | CEgroup
  | CMath
  | CAlign
  | CEol
  | CParam
  | CSup
  | CSub
  | CIgnored
  | CSpacer
  | CLetter
  | COther
  | CActive
  | CComment
  | CInvalid

let cat_eqb a b =
  match a with
  | CEscape -> (
      match b with
      | CEscape -> true
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CBgroup -> (
      match b with
      | CEscape -> false
      | CBgroup -> true
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CEgroup -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> true
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CMath -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> true
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CAlign -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> true
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CEol -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> true
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CParam -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> true
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CSup -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> true
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CSub -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> true
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CIgnored -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> true
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CSpacer -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> true
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CLetter -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> true
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | COther -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> true
      | CActive -> false
      | CComment -> false
      | CInvalid -> false)
  | CActive -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> true
      | CComment -> false
      | CInvalid -> false)
  | CComment -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> true
      | CInvalid -> false)
  | CInvalid -> (
      match b with
      | CEscape -> false
      | CBgroup -> false
      | CEgroup -> false
      | CMath -> false
      | CAlign -> false
      | CEol -> false
      | CParam -> false
      | CSup -> false
      | CSub -> false
      | CIgnored -> false
      | CSpacer -> false
      | CLetter -> false
      | COther -> false
      | CActive -> false
      | CComment -> false
      | CInvalid -> true)

type lexcon = {
  lx_cat : char -> cat;
  lx_endline : char option;
  lx_par : name;
  lx_end : name;
  lx_begin : name;
  lx_docclass : name;
  lx_class : char list;
  lx_docenv : char list;
  lx_mopen_inline : char;
  lx_mclose_inline : char;
  lx_mopen_display : char;
  lx_mclose_display : char;
}

type bad = BadCat | BadHatHat | BadNullCs | BadLongLine | BadFirstLine

type rtok =
  | RChar of char
  | RSpace
  | RPar
  | RBgroup
  | REgroup
  | RMath
  | RSup
  | RSub
  | RWord of name
  | RSym of char
  | RBad of bad

type lt = { lt_tok : rtok; lt_line : int; lt_off : int }

let lf =
  ascii_of_nat
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ
                      (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))

let cr =
  ascii_of_nat
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ
                      (Stdlib.Int.succ
                         (Stdlib.Int.succ
                            (Stdlib.Int.succ
                               (Stdlib.Int.succ
                                  (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))

let sp =
  ascii_of_nat
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ
                      (Stdlib.Int.succ
                         (Stdlib.Int.succ
                            (Stdlib.Int.succ
                               (Stdlib.Int.succ
                                  (Stdlib.Int.succ
                                     (Stdlib.Int.succ
                                        (Stdlib.Int.succ
                                           (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                                (Stdlib.Int.succ
                                                                   (Stdlib.Int
                                                                    .succ
                                                                      (Stdlib
                                                                       .Int
                                                                       .succ
                                                                         (Stdlib
                                                                          .Int
                                                                          .succ
                                                                            (Stdlib
                                                                             .Int
                                                                             .succ
                                                                               (Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                0))))))))))))))))))))))))))))))))

let rec index o = function
  | [] -> []
  | c :: r -> (c, o) :: index (Stdlib.Int.succ o) r

type line = (char * int) list * int

let rec rtrim = function
  | [] -> []
  | p :: r -> (
      match rtrim r with
      | [] -> if fst p = sp then [] else p :: []
      | p0 :: l0 -> p :: p0 :: l0)

let buffer l l0 eo =
  app (rtrim l0)
    (match l.lx_endline with Some e -> (e, eo) :: [] | None -> [])

type lstate = SN | SM | SS

let hathat l c rest =
  cat_eqb (l.lx_cat c) CSup
  &&
  match rest with
  | [] -> false
  | p :: _ ->
      let d, _ = p in
      d = c

let sym_state l c = if cat_eqb (l.lx_cat c) CSpacer then SS else SM
let max_line_bytes = Nat.mul ten (Nat.mul ten (Nat.mul ten ten))

let line_start l eo =
  match l with
  | [] -> eo
  | p :: _ ->
      let _, o = p in
      o

let pct =
  ascii_of_nat
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ
                      (Stdlib.Int.succ
                         (Stdlib.Int.succ
                            (Stdlib.Int.succ
                               (Stdlib.Int.succ
                                  (Stdlib.Int.succ
                                     (Stdlib.Int.succ
                                        (Stdlib.Int.succ
                                           (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                                (Stdlib.Int.succ
                                                                   (Stdlib.Int
                                                                    .succ
                                                                      (Stdlib
                                                                       .Int
                                                                       .succ
                                                                         (Stdlib
                                                                          .Int
                                                                          .succ
                                                                            (Stdlib
                                                                             .Int
                                                                             .succ
                                                                               (Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                0)))))))))))))))))))))))))))))))))))))

let amp =
  ascii_of_nat
    (Stdlib.Int.succ
       (Stdlib.Int.succ
          (Stdlib.Int.succ
             (Stdlib.Int.succ
                (Stdlib.Int.succ
                   (Stdlib.Int.succ
                      (Stdlib.Int.succ
                         (Stdlib.Int.succ
                            (Stdlib.Int.succ
                               (Stdlib.Int.succ
                                  (Stdlib.Int.succ
                                     (Stdlib.Int.succ
                                        (Stdlib.Int.succ
                                           (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                                (Stdlib.Int.succ
                                                                   (Stdlib.Int
                                                                    .succ
                                                                      (Stdlib
                                                                       .Int
                                                                       .succ
                                                                         (Stdlib
                                                                          .Int
                                                                          .succ
                                                                            (Stdlib
                                                                             .Int
                                                                             .succ
                                                                               (Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                (
                                                                                Stdlib
                                                                                .Int
                                                                                .succ
                                                                                0))))))))))))))))))))))))))))))))))))))

let rec split_line = function
  | [] -> ([], None)
  | c :: r ->
      if c = lf then ([], Some (r, Stdlib.Int.succ 0))
      else if c = cr then
        match r with
        | [] -> ([], Some ([], Stdlib.Int.succ 0))
        | d :: r' ->
            if d = lf then ([], Some (r', Stdlib.Int.succ (Stdlib.Int.succ 0)))
            else ([], Some (r, Stdlib.Int.succ 0))
      else
        let l, t = split_line r in
        (c :: l, t)

let rec lines_f fuel o b =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun f ->
      match b with
      | [] -> []
      | _ :: _ -> (
          let l, t = split_line b in
          match t with
          | Some p ->
              let rest, k = p in
              (index o l, add o (length l))
              :: lines_f f (add (add o (length l)) k) rest
          | None -> (index o l, add o (length l)) :: []))
    fuel

let split_lines b = lines_f (Stdlib.Int.succ (length b)) 0 b

let rec split_letters l buf =
  match buf with
  | [] -> ([], [])
  | p :: r ->
      if cat_eqb (l.lx_cat (fst p)) CLetter then
        let w, rest = split_letters l r in
        (p :: w, rest)
      else ([], buf)

let rec lexl l ln fuel st buf =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun f ->
      match buf with
      | [] -> []
      | p :: rest -> (
          let c, o = p in
          match l.lx_cat c with
          | CEscape -> (
              match rest with
              | [] ->
                  { lt_tok = RBad BadNullCs; lt_line = ln; lt_off = o } :: []
              | p0 :: rest' ->
                  let d, _ = p0 in
                  if cat_eqb (l.lx_cat d) CLetter then
                    let w, after = split_letters l rest in
                    match after with
                    | [] ->
                        { lt_tok = RWord (map fst w); lt_line = ln; lt_off = o }
                        :: []
                    | p1 :: after' ->
                        let x, _ = p1 in
                        if hathat l x after' then
                          { lt_tok = RBad BadHatHat; lt_line = ln; lt_off = o }
                          :: []
                        else
                          {
                            lt_tok = RWord (map fst w);
                            lt_line = ln;
                            lt_off = o;
                          }
                          :: lexl l ln f SS after
                  else if hathat l d rest' then
                    { lt_tok = RBad BadHatHat; lt_line = ln; lt_off = o } :: []
                  else
                    { lt_tok = RSym d; lt_line = ln; lt_off = o }
                    :: lexl l ln f (sym_state l d) rest')
          | CBgroup ->
              { lt_tok = RBgroup; lt_line = ln; lt_off = o }
              :: lexl l ln f SM rest
          | CEgroup ->
              { lt_tok = REgroup; lt_line = ln; lt_off = o }
              :: lexl l ln f SM rest
          | CMath ->
              { lt_tok = RMath; lt_line = ln; lt_off = o }
              :: lexl l ln f SM rest
          | CAlign -> { lt_tok = RBad BadCat; lt_line = ln; lt_off = o } :: []
          | CEol -> (
              match st with
              | SN -> { lt_tok = RPar; lt_line = ln; lt_off = o } :: []
              | SM -> { lt_tok = RSpace; lt_line = ln; lt_off = o } :: []
              | SS -> [])
          | CParam -> { lt_tok = RBad BadCat; lt_line = ln; lt_off = o } :: []
          | CSup ->
              if hathat l c rest then
                { lt_tok = RBad BadHatHat; lt_line = ln; lt_off = o } :: []
              else
                { lt_tok = RSup; lt_line = ln; lt_off = o }
                :: lexl l ln f SM rest
          | CSub ->
              { lt_tok = RSub; lt_line = ln; lt_off = o } :: lexl l ln f SM rest
          | CIgnored -> { lt_tok = RBad BadCat; lt_line = ln; lt_off = o } :: []
          | CSpacer -> (
              match st with
              | SN -> lexl l ln f st rest
              | SM ->
                  { lt_tok = RSpace; lt_line = ln; lt_off = o }
                  :: lexl l ln f SS rest
              | SS -> lexl l ln f st rest)
          | CLetter ->
              { lt_tok = RChar c; lt_line = ln; lt_off = o }
              :: lexl l ln f SM rest
          | COther ->
              { lt_tok = RChar c; lt_line = ln; lt_off = o }
              :: lexl l ln f SM rest
          | CActive -> { lt_tok = RBad BadCat; lt_line = ln; lt_off = o } :: []
          | CComment -> []
          | CInvalid -> { lt_tok = RBad BadCat; lt_line = ln; lt_off = o } :: []
          ))
    fuel

let lex_line l ln buf = lexl l ln (Stdlib.Int.succ (length buf)) SN buf

let rec lex_lines l ln = function
  | [] -> []
  | l0 :: r ->
      let l1, eo = l0 in
      app
        (if length l1 <= max_line_bytes then lex_line l ln (buffer l l1 eo)
         else
           {
             lt_tok = RBad BadLongLine;
             lt_line = ln;
             lt_off = line_start l1 eo;
           }
           :: [])
        (lex_lines l (Stdlib.Int.succ ln) r)

let first_directive = function
  | [] -> false
  | c1 :: l -> ( match l with [] -> false | c2 :: _ -> c1 = pct && c2 = amp)

let first_toks b =
  if first_directive b then
    { lt_tok = RBad BadFirstLine; lt_line = Stdlib.Int.succ 0; lt_off = 0 }
    :: []
  else []

let lex l b =
  app (first_toks b) (lex_lines l (Stdlib.Int.succ 0) (split_lines b))

type ktok = { k_tok : tok; k_line : int; k_off : int }

let toks_of ks = map (fun k -> k.k_tok) ks

let rec name_eqb a b =
  match a with
  | [] -> ( match b with [] -> true | _ :: _ -> false)
  | x :: a' -> (
      match b with [] -> false | y :: b' -> x = y && name_eqb a' b')

let sym_tok l c =
  if c = l.lx_mopen_inline then Some TMOpenInline
  else if c = l.lx_mclose_inline then Some TMCloseInline
  else if c = l.lx_mopen_display then Some TMOpenDisplay
  else if c = l.lx_mclose_display then Some TMCloseDisplay
  else None

let kt k t = { k_tok = k; k_line = t.lt_line; k_off = t.lt_off }

let fillerb l t =
  match t.lt_tok with
  | RChar _ -> false
  | RSpace -> true
  | RPar -> true
  | RBgroup -> false
  | REgroup -> false
  | RMath -> false
  | RSup -> false
  | RSub -> false
  | RWord n0 -> name_eqb n0 l.lx_par
  | RSym _ -> false
  | RBad _ -> false

let rec skip_fill l ts =
  match ts with [] -> [] | t :: r -> if fillerb l t then skip_fill l r else ts

let is_char_tok c t =
  match t.lt_tok with
  | RChar d -> c = d
  | RSpace -> false
  | RPar -> false
  | RBgroup -> false
  | REgroup -> false
  | RMath -> false
  | RSup -> false
  | RSub -> false
  | RWord _ -> false
  | RSym _ -> false
  | RBad _ -> false

let rec match_chars w ts =
  match w with
  | [] -> Some ts
  | c :: w' -> (
      match ts with
      | [] -> None
      | t :: r -> if is_char_tok c t then match_chars w' r else None)

let is_word n0 t =
  match t.lt_tok with
  | RChar _ -> false
  | RSpace -> false
  | RPar -> false
  | RBgroup -> false
  | REgroup -> false
  | RMath -> false
  | RSup -> false
  | RSub -> false
  | RWord m -> name_eqb m n0
  | RSym _ -> false
  | RBad _ -> false

let is_tok k t =
  match k with
  | RChar _ -> false
  | RSpace -> false
  | RPar -> false
  | RBgroup -> (
      match t.lt_tok with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> true
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | REgroup -> (
      match t.lt_tok with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> true
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RMath -> false
  | RSup -> false
  | RSub -> false
  | RWord _ -> false
  | RSym _ -> false
  | RBad _ -> false

let braced n0 w = function
  | [] -> None
  | t :: l -> (
      match l with
      | [] -> None
      | ob :: r ->
          if is_word n0 t && is_tok RBgroup ob then
            match match_chars w r with
            | Some l0 -> (
                match l0 with
                | [] -> None
                | cb :: rest ->
                    if is_tok REgroup cb then Some (cb, rest) else None)
            | None -> None
          else None)

let prologue l ts =
  if name_eqb l.lx_docclass l.lx_par || name_eqb l.lx_begin l.lx_par then None
  else
    match braced l.lx_docclass l.lx_class (skip_fill l ts) with
    | Some p -> (
        let _, r = p in
        match braced l.lx_begin l.lx_docenv (skip_fill l r) with
        | Some p0 ->
            let _, rest = p0 in
            Some rest
        | None -> None)
    | None -> None

let cons_k k = function Some ks -> Some (k :: ks) | None -> None

let rec body l s ts =
  match ts with
  | [] -> Some []
  | t :: rest -> (
      match t.lt_tok with
      | RChar c -> cons_k (kt (TChar c) t) (body l false rest)
      | RSpace ->
          if s then body l true rest
          else cons_k (kt TSpace t) (body l false rest)
      | RPar -> cons_k (kt (TPar false) t) (body l false rest)
      | RBgroup -> cons_k (kt TOpen t) (body l false rest)
      | REgroup -> cons_k (kt TClose t) (body l false rest)
      | RMath -> cons_k (kt TDollar t) (body l false rest)
      | RSup -> cons_k (kt (TScript true) t) (body l true rest)
      | RSub -> cons_k (kt (TScript false) t) (body l true rest)
      | RWord n0 ->
          if name_eqb n0 l.lx_par then
            cons_k (kt (TPar true) t) (body l false rest)
          else if name_eqb n0 l.lx_end then
            match braced l.lx_end l.lx_docenv ts with
            | Some p ->
                let cb, _ = p in
                Some
                  ({ k_tok = TEnd; k_line = cb.lt_line; k_off = t.lt_off } :: [])
            | None -> None
          else cons_k (kt (TCs n0) t) (body l false rest)
      | RSym c -> (
          match sym_tok l c with
          | Some k -> cons_k (kt k t) (body l false rest)
          | None -> None)
      | RBad _ -> None)

let front l ts =
  match prologue l ts with Some rest -> body l false rest | None -> None

let parse l b = front l (lex l b)

type bcontract = { bc_kernel : contract; bc_lex : lexcon }

let max_file_bytes = Nat.mul max_line_bytes (Nat.mul ten ten)

let ends_dollar ts =
  match last ts TSpace with
  | TChar _ -> false
  | TSpace -> false
  | TPar _ -> false
  | TOpen -> false
  | TClose -> false
  | TDollar -> true
  | TMOpenInline -> false
  | TMCloseInline -> false
  | TMOpenDisplay -> false
  | TMCloseDisplay -> false
  | TScript _ -> false
  | TCs _ -> false
  | TEnd -> false

let strict_ks_b k ts =
  (((forallb (tok_ok k) ts && scripts_ok ts) && wfa k 0 ts) && bounded k ts)
  && negb (ends_dollar ts)

let in_strict_bytes_b c b =
  length b <= max_file_bytes
  &&
  match parse c.bc_lex b with
  | Some ks -> strict_ks_b c.bc_kernel (toks_of ks)
  | None -> false

let reads_next s = function
  | TChar _ -> false
  | TSpace -> false
  | TPar _ -> false
  | TOpen -> false
  | TClose -> false
  | TDollar -> (
      match s.s_frames with
      | [] -> false
      | f :: _ -> (
          match f with
          | FSimple -> false
          | FShift (display, _, _) -> if display then true else false
          | FMGroup (_, _, _) -> false
          | FArg (_, _, _, _, _) -> false))
  | TMOpenInline -> false
  | TMCloseInline -> false
  | TMOpenDisplay -> false
  | TMCloseDisplay -> false
  | TScript _ -> false
  | TCs _ -> false
  | TEnd -> false

let rec rd_scan sc = function
  | [] -> None
  | t :: rest -> (
      match t with
      | TChar _ -> option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TSpace -> option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TPar _ ->
          if sc.sc_ou then Some (Stdlib.Int.succ 0)
          else if sc.sc_sh = 0 then
            option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
          else
            option_map
              (fun x -> Stdlib.Int.succ x)
              (rd_scan
                 { sc_r = E6; sc_k = sc.sc_k; sc_sh = sc.sc_sh; sc_ou = false }
                 rest)
      | TOpen ->
          option_map
            (fun x -> Stdlib.Int.succ x)
            (rd_scan
               {
                 sc_r = sc.sc_r;
                 sc_k = Stdlib.Int.succ sc.sc_k;
                 sc_sh = sc.sc_sh;
                 sc_ou = sc.sc_ou;
               }
               rest)
      | TClose ->
          (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
            (fun _ -> None)
            (fun n0 ->
              (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                (fun _ -> Some (Stdlib.Int.succ 0))
                (fun k ->
                  option_map
                    (fun x -> Stdlib.Int.succ x)
                    (rd_scan
                       {
                         sc_r = sc.sc_r;
                         sc_k = Stdlib.Int.succ k;
                         sc_sh = close_sh (Stdlib.Int.succ k) sc.sc_sh;
                         sc_ou = sc.sc_ou;
                       }
                       rest))
                n0)
            sc.sc_k
      | TDollar -> option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TMOpenInline ->
          option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TMCloseInline ->
          option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TMOpenDisplay ->
          option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TMCloseDisplay ->
          option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TScript _ -> option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TCs _ -> option_map (fun x -> Stdlib.Int.succ x) (rd_scan sc rest)
      | TEnd -> None)

let rec rd k s = function
  | [] -> None
  | t :: rest -> (
      match step k s t (hd_error rest) with
      | Go1 s' -> option_map (fun x -> Stdlib.Int.succ x) (rd k s' rest)
      | Go2 s' -> (
          match rest with
          | [] -> None
          | _ :: r' ->
              option_map
                (fun n0 -> Stdlib.Int.succ (Stdlib.Int.succ n0))
                (rd k s' r'))
      | Stop _ ->
          if reads_next s t then
            match rest with
            | [] -> None
            | _ :: _ -> Some (Stdlib.Int.succ (Stdlib.Int.succ 0))
          else Some (Stdlib.Int.succ 0)
      | Stuck -> None
      | Defer sc -> rd_scan sc (t :: rest)
      | Defer2 sc -> (
          match rest with
          | [] -> None
          | _ :: r' ->
              option_map
                (fun n0 -> Stdlib.Int.succ (Stdlib.Int.succ n0))
                (rd_scan sc r')))

let line_at ks k = match nth_error ks k with Some t -> t.k_line | None -> 0
let report_line ks = function Some n0 -> line_at ks (pred n0) | None -> 0

let decide_bytes c b =
  if length b <= max_file_bytes then
    match parse c.bc_lex b with
    | Some ks ->
        if strict_ks_b c.bc_kernel (toks_of ks) then
          match run c.bc_kernel init (toks_of ks) with
          | Some o -> (
              match o with
              | Compiles -> ProvenReady
              | Fatal (r, _) ->
                  ProvenNotReady
                    (r, report_line ks (rd c.bc_kernel init (toks_of ks))))
          | None -> NotStrict
        else NotStrict
    | None -> NotStrict
  else NotStrict

type why_out =
  | WTooBig
  | WLexBad of bad
  | WPrologue
  | WToken
  | WNotAdmitted
  | WScriptArg
  | WBound
  | WEndsDollar
  | WArgForm

let rtok_eqb a b =
  match a with
  | RChar x -> (
      match b with
      | RChar y -> x = y
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RSpace -> (
      match b with
      | RChar _ -> false
      | RSpace -> true
      | RPar -> false
      | RBgroup -> false
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RPar -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> true
      | RBgroup -> false
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RBgroup -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> true
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | REgroup -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> true
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RMath -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> false
      | RMath -> true
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RSup -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> false
      | RMath -> false
      | RSup -> true
      | RSub -> false
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RSub -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> true
      | RWord _ -> false
      | RSym _ -> false
      | RBad _ -> false)
  | RWord m -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord n0 -> name_eqb m n0
      | RSym _ -> false
      | RBad _ -> false)
  | RSym x -> (
      match b with
      | RChar _ -> false
      | RSpace -> false
      | RPar -> false
      | RBgroup -> false
      | REgroup -> false
      | RMath -> false
      | RSup -> false
      | RSub -> false
      | RWord _ -> false
      | RSym y -> x = y
      | RBad _ -> false)
  | RBad _ -> false

let rec expect exp ts =
  match exp with
  | [] -> Inr ts
  | e :: exp' -> (
      match ts with
      | [] -> Inl None
      | t :: r -> if rtok_eqb e t.lt_tok then expect exp' r else Inl (Some t))

let cmd_seq n0 w =
  RWord n0 :: RBgroup :: app (map (fun x -> RChar x) w) (REgroup :: [])

let blame t w =
  match t.lt_tok with
  | RChar _ -> (t.lt_off, w)
  | RSpace -> (t.lt_off, w)
  | RPar -> (t.lt_off, w)
  | RBgroup -> (t.lt_off, w)
  | REgroup -> (t.lt_off, w)
  | RMath -> (t.lt_off, w)
  | RSup -> (t.lt_off, w)
  | RSub -> (t.lt_off, w)
  | RWord _ -> (t.lt_off, w)
  | RSym _ -> (t.lt_off, w)
  | RBad k -> (t.lt_off, WLexBad k)

let explain_prologue l eof ts =
  match expect (cmd_seq l.lx_docclass l.lx_class) (skip_fill l ts) with
  | Inl o -> (
      match o with
      | Some t -> Inl (blame t WPrologue)
      | None -> Inl (eof, WPrologue))
  | Inr r -> (
      match expect (cmd_seq l.lx_begin l.lx_docenv) (skip_fill l r) with
      | Inl o -> (
          match o with
          | Some t -> Inl (blame t WPrologue)
          | None -> Inl (eof, WPrologue))
      | Inr rest -> Inr rest)

let rec explain_body l ts =
  match ts with
  | [] -> None
  | t :: rest -> (
      match t.lt_tok with
      | RChar _ -> explain_body l rest
      | RSpace -> explain_body l rest
      | RPar -> explain_body l rest
      | RBgroup -> explain_body l rest
      | REgroup -> explain_body l rest
      | RMath -> explain_body l rest
      | RSup -> explain_body l rest
      | RSub -> explain_body l rest
      | RWord n0 ->
          if name_eqb n0 l.lx_par then explain_body l rest
          else if name_eqb n0 l.lx_end then
            match braced l.lx_end l.lx_docenv ts with
            | Some _ -> None
            | None -> Some (t.lt_off, WToken)
          else explain_body l rest
      | RSym c -> (
          match sym_tok l c with
          | Some _ -> explain_body l rest
          | None -> Some (t.lt_off, WToken))
      | RBad k -> Some (t.lt_off, WLexBad k))

let rec first_not_admitted k = function
  | [] -> None
  | k0 :: r -> if tok_ok k k0.k_tok then first_not_admitted k r else Some k0

let rec first_bad_script = function
  | [] -> None
  | k :: r -> (
      match k.k_tok with
      | TChar _ -> first_bad_script r
      | TSpace -> first_bad_script r
      | TPar _ -> first_bad_script r
      | TOpen -> first_bad_script r
      | TClose -> first_bad_script r
      | TDollar -> first_bad_script r
      | TMOpenInline -> first_bad_script r
      | TMCloseInline -> first_bad_script r
      | TMOpenDisplay -> first_bad_script r
      | TMCloseDisplay -> first_bad_script r
      | TScript _ -> (
          match r with
          | [] -> Some k
          | k2 :: _ -> (
              match k2.k_tok with
              | TChar _ -> first_bad_script r
              | TSpace -> Some k
              | TPar _ -> Some k
              | TOpen -> first_bad_script r
              | TClose -> Some k
              | TDollar -> Some k
              | TMOpenInline -> Some k
              | TMCloseInline -> Some k
              | TMOpenDisplay -> Some k
              | TMCloseDisplay -> Some k
              | TScript _ -> Some k
              | TCs _ -> Some k
              | TEnd -> Some k))
      | TCs _ -> first_bad_script r
      | TEnd -> first_bad_script r)

let rec first_bad_arg k need = function
  | [] -> if need = 0 then None else Some None
  | k0 :: r -> (
      match k0.k_tok with
      | TChar _ -> first_bad_arg k need r
      | TSpace -> first_bad_arg k need r
      | TPar _ -> first_bad_arg k need r
      | TOpen ->
          first_bad_arg k (if need = 0 then 0 else Stdlib.Int.succ need) r
      | TClose -> first_bad_arg k (pred need) r
      | TDollar -> first_bad_arg k need r
      | TMOpenInline -> first_bad_arg k need r
      | TMCloseInline -> first_bad_arg k need r
      | TMOpenDisplay -> first_bad_arg k need r
      | TMCloseDisplay -> first_bad_arg k need r
      | TScript _ -> first_bad_arg k need r
      | TCs n0 ->
          if is_argcmd k n0 then
            match r with
            | [] -> Some (Some k0)
            | k2 :: r' -> (
                match k2.k_tok with
                | TChar _ -> Some (Some k0)
                | TSpace -> Some (Some k0)
                | TPar _ -> Some (Some k0)
                | TOpen -> first_bad_arg k (Stdlib.Int.succ need) r'
                | TClose -> Some (Some k0)
                | TDollar -> Some (Some k0)
                | TMOpenInline -> Some (Some k0)
                | TMCloseInline -> Some (Some k0)
                | TMOpenDisplay -> Some (Some k0)
                | TMCloseDisplay -> Some (Some k0)
                | TScript _ -> Some (Some k0)
                | TCs _ -> Some (Some k0)
                | TEnd -> Some (Some k0))
          else first_bad_arg k need r
      | TEnd -> if need = 0 then None else Some (Some k0))

let rec first_long_name = function
  | [] -> None
  | k :: r -> (
      match k.k_tok with
      | TChar _ -> first_long_name r
      | TSpace -> first_long_name r
      | TPar _ -> first_long_name r
      | TOpen -> first_long_name r
      | TClose -> first_long_name r
      | TDollar -> first_long_name r
      | TMOpenInline -> first_long_name r
      | TMCloseInline -> first_long_name r
      | TMOpenDisplay -> first_long_name r
      | TMCloseDisplay -> first_long_name r
      | TScript _ -> first_long_name r
      | TCs n0 -> if length n0 <= max_name then first_long_name r else Some k
      | TEnd -> first_long_name r)

let rec first_over k s = function
  | [] -> None
  | k0 :: r -> (
      match
        step k s k0.k_tok (option_map (fun k1 -> k1.k_tok) (hd_error r))
      with
      | Go1 s' ->
          if Nat.ltb max_groups (groups s'.s_frames) then Some k0
          else first_over k s' r
      | Go2 s' -> (
          match r with
          | [] -> None
          | _ :: r' ->
              if Nat.ltb max_groups (groups s'.s_frames) then Some k0
              else first_over k s' r')
      | Stop _ -> None
      | Stuck -> None
      | Defer _ -> None
      | Defer2 _ -> None)

let rec first_heavy k b opens acc = function
  | [] -> None
  | k0 :: r -> (
      let acc1 = add (add acc (k.c_cost k0.k_tok)) (open_copies opens) in
      if Nat.ltb max_mem acc1 then Some k0
      else
        match k0.k_tok with
        | TChar _ -> first_heavy k b opens acc1 r
        | TSpace -> first_heavy k b opens acc1 r
        | TPar _ -> first_heavy k b opens acc1 r
        | TOpen -> first_heavy k (Stdlib.Int.succ b) opens acc1 r
        | TClose ->
            first_heavy k (pred b)
              (filter (fun x -> Nat.ltb (fst x) (pred b)) opens)
              acc1 r
        | TDollar -> first_heavy k b opens acc1 r
        | TMOpenInline -> first_heavy k b opens acc1 r
        | TMCloseInline -> first_heavy k b opens acc1 r
        | TMOpenDisplay -> first_heavy k b opens acc1 r
        | TMCloseDisplay -> first_heavy k b opens acc1 r
        | TScript _ -> first_heavy k b opens acc1 r
        | TCs n0 ->
            if is_argcmd k n0 then
              match r with
              | [] -> None
              | k2 :: r' -> (
                  match k2.k_tok with
                  | TChar _ -> first_heavy k b opens acc1 r
                  | TSpace -> first_heavy k b opens acc1 r
                  | TPar _ -> first_heavy k b opens acc1 r
                  | TOpen ->
                      let acc2 =
                        add (add acc1 (k.c_cost TOpen)) (open_copies opens)
                      in
                      if Nat.ltb max_mem acc2 then Some k2
                      else
                        first_heavy k (Stdlib.Int.succ b)
                          ((b, copy_of k n0) :: opens)
                          acc2 r'
                  | TClose -> first_heavy k b opens acc1 r
                  | TDollar -> first_heavy k b opens acc1 r
                  | TMOpenInline -> first_heavy k b opens acc1 r
                  | TMCloseInline -> first_heavy k b opens acc1 r
                  | TMOpenDisplay -> first_heavy k b opens acc1 r
                  | TMCloseDisplay -> first_heavy k b opens acc1 r
                  | TScript _ -> first_heavy k b opens acc1 r
                  | TCs _ -> first_heavy k b opens acc1 r
                  | TEnd -> first_heavy k b opens acc1 r)
            else first_heavy k b opens acc1 r
        | TEnd -> first_heavy k b opens acc1 r)

let rec first_wide k s acc = function
  | [] -> None
  | k0 :: r -> (
      let t = k0.k_tok in
      let m = in_math s.s_frames in
      let a = if seg_start s t then k.c_dim m t else add acc (k.c_dim m t) in
      if Nat.ltb max_dim a then Some k0
      else
        match step k s t (option_map (fun k1 -> k1.k_tok) (hd_error r)) with
        | Go1 s' -> first_wide k s' a r
        | Go2 s' -> (
            match r with
            | [] -> None
            | k2 :: r' ->
                let a2 = add a (k.c_dim m k2.k_tok) in
                if Nat.ltb max_dim a2 then Some k2 else first_wide k s' a2 r')
        | Stop _ -> None
        | Stuck -> None
        | Defer _ -> None
        | Defer2 _ -> None)

let off_or o dflt = match o with Some k -> k.k_off | None -> dflt

let explain c b =
  let l = c.bc_lex in
  let k = c.bc_kernel in
  if negb (length b <= max_file_bytes) then Some (max_file_bytes, WTooBig)
  else
    match explain_prologue l (length b) (lex l b) with
    | Inl e -> Some e
    | Inr rest -> (
        match explain_body l rest with
        | Some e -> Some e
        | None -> (
            match body l false rest with
            | Some ks -> (
                match first_not_admitted k ks with
                | Some k0 -> Some (k0.k_off, WNotAdmitted)
                | None -> (
                    match first_bad_script ks with
                    | Some k0 -> Some (k0.k_off, WScriptArg)
                    | None -> (
                        match first_bad_arg k 0 ks with
                        | Some o -> (
                            match o with
                            | Some k0 -> Some (k0.k_off, WArgForm)
                            | None -> Some (length b, WArgForm))
                        | None -> (
                            if negb (length ks <= max_tokens) then
                              Some
                                ( off_or (nth_error ks max_tokens) (length b),
                                  WBound )
                            else
                              match first_long_name ks with
                              | Some k0 -> Some (k0.k_off, WBound)
                              | None -> (
                                  match first_over k init ks with
                                  | Some k0 -> Some (k0.k_off, WBound)
                                  | None -> (
                                      match first_heavy k 0 [] 0 ks with
                                      | Some k0 -> Some (k0.k_off, WBound)
                                      | None -> (
                                          match
                                            first_wide k init
                                              (k.c_dim false (TPar false))
                                              ks
                                          with
                                          | Some k0 -> Some (k0.k_off, WBound)
                                          | None ->
                                              if ends_dollar (toks_of ks) then
                                                Some
                                                  ( off_or
                                                      (last
                                                         (map
                                                            (fun x -> Some x)
                                                            ks)
                                                         None)
                                                      (length b),
                                                    WEndsDollar )
                                              else None)))))))
            | None -> Some (length b, WToken)))
