
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a option =
| Some of 'a
| None

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add n0 m =
   (fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> m)
     (fun p -> succ (add p m))
     n0
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun p -> add m (mul p m))
    n0

(** val sub : int -> int -> int **)

let rec sub n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> n0)
    (fun k ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun l -> sub k l)
      m)
    n0

(** val max : int -> int -> int **)

let rec max n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun m' -> succ (max n' m'))
      m)
    n0

(** val min : int -> int -> int **)

let rec min n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun m' -> succ (min n' m'))
      m)
    n0

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  if b1 then if b2 then Left else Right else if b2 then Right else Left

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n0

  (** val leb : int -> int -> bool **)

  let rec leb n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    leb (succ n0) m
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (succ 0)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  (** val to_nat : n -> int **)

  let to_nat = function
  | N0 -> 0
  | Npos p -> Pos.to_nat p

  (** val of_nat : int -> n **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> N0)
      (fun n' -> Npos (Pos.of_succ_nat n'))
      n0
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val zero : char **)

let zero =
  '\000'

(** val one : char **)

let one =
  '\001'

(** val shift : bool -> char -> char **)

let shift c = function
| %s (a1, a2, a3, a4, a5, a6, a7, _) -> %s (c, a1, a2, a3, a4, a5, a6, a7)

(** val ascii_dec : char -> char -> sumbool **)

let ascii_dec a b =
  let %s (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let %s (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match bool_dec b0 b8 with
   | Left ->
     (match bool_dec b1 b9 with
      | Left ->
        (match bool_dec b2 b10 with
         | Left ->
           (match bool_dec b3 b11 with
            | Left ->
              (match bool_dec b4 b12 with
               | Left ->
                 (match bool_dec b5 b13 with
                  | Left ->
                    (match bool_dec b6 b14 with
                     | Left -> bool_dec b7 b15
                     | Right -> Right)
                  | Right -> Right)
               | Right -> Right)
            | Right -> Right)
         | Right -> Right)
      | Right -> Right)
   | Right -> Right)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      match p with
      | XI p' -> shift true (loop n' p')
      | XO p' -> shift false (loop n' p')
      | XH -> one)
      n0
  in loop (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b::l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii = function
| %s (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[]))))))))

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | "" -> s2
  | String.make 1 (%s) ^ %s (c, s1') ->
    String.make 1 (%s) ^ %s (c, (append s1' s2))

(** val length : string -> int **)

let rec length = function
| "" -> 0
| String.make 1 (%s) ^ %s (_, s') -> succ (length s')

type catcode =
| CatEscape
| CatBeginGroup
| CatEndGroup
| CatMathShift
| CatAlignment
| CatParameter
| CatSuperscript
| CatSubscript
| CatSpace
| CatLetter
| CatOther
| CatComment

type catcode_table = char -> catcode

(** val ascii_backslash : char **)

let ascii_backslash =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_lbrace : char **)

let ascii_lbrace =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_rbrace : char **)

let ascii_rbrace =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_dollar : char **)

let ascii_dollar =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ 0))))))))))))))))))))))))))))))))))))

(** val ascii_ampersand : char **)

let ascii_ampersand =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ 0))))))))))))))))))))))))))))))))))))))

(** val ascii_hash : char **)

let ascii_hash =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ 0)))))))))))))))))))))))))))))))))))

(** val ascii_caret : char **)

let ascii_caret =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_underscore : char **)

let ascii_underscore =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_space : char **)

let ascii_space =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))

(** val ascii_percent : char **)

let ascii_percent =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ 0)))))))))))))))))))))))))))))))))))))

(** val is_letter : char -> bool **)

let is_letter c =
  let n0 = nat_of_ascii c in
  if if Nat.leb (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          n0
     then Nat.leb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ
            0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     else false
  then true
  else if Nat.leb (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            n0
       then Nat.leb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ
              0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       else false

(** val default_catcodes : catcode_table **)

let default_catcodes c =
  match ascii_dec c ascii_backslash with
  | Left -> CatEscape
  | Right ->
    (match ascii_dec c ascii_lbrace with
     | Left -> CatBeginGroup
     | Right ->
       (match ascii_dec c ascii_rbrace with
        | Left -> CatEndGroup
        | Right ->
          (match ascii_dec c ascii_dollar with
           | Left -> CatMathShift
           | Right ->
             (match ascii_dec c ascii_ampersand with
              | Left -> CatAlignment
              | Right ->
                (match ascii_dec c ascii_hash with
                 | Left -> CatParameter
                 | Right ->
                   (match ascii_dec c ascii_caret with
                    | Left -> CatSuperscript
                    | Right ->
                      (match ascii_dec c ascii_underscore with
                       | Left -> CatSubscript
                       | Right ->
                         (match ascii_dec c ascii_space with
                          | Left -> CatSpace
                          | Right ->
                            (match ascii_dec c ascii_percent with
                             | Left -> CatComment
                             | Right ->
                               if is_letter c then CatLetter else CatOther)))))))))

type latex_token =
| TCommand of string
| TBeginGroup
| TEndGroup
| TMathShift
| TAlignment
| TParameter
| TSuperscript
| TSubscript
| TText of string
| TSpace
| TComment of string
| TNewline
| TEOF

type lexer_state = { input : string; position : int;
                     tokens : latex_token list; line_number : int;
                     column_number : int }

(** val initial_state : string -> lexer_state **)

let initial_state s =
  { input = s; position = 0; tokens = []; line_number = (succ 0);
    column_number = (succ 0) }

(** val peek_char : lexer_state -> char option **)

let peek_char st =
  match st.input with
  | "" -> None
  | String.make 1 (%s) ^ %s (c, _) -> Some c

(** val advance_char : lexer_state -> lexer_state **)

let advance_char st =
  match st.input with
  | "" -> st
  | String.make 1 (%s) ^ %s (c, rest) ->
    let new_column =
      match ascii_dec c
              (ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ 0))))))))))) with
      | Left -> succ 0
      | Right -> succ st.column_number
    in
    let new_line =
      match ascii_dec c
              (ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ 0))))))))))) with
      | Left -> succ st.line_number
      | Right -> st.line_number
    in
    { input = rest; position = (succ st.position); tokens = st.tokens;
    line_number = new_line; column_number = new_column }

(** val add_token : latex_token -> lexer_state -> lexer_state **)

let add_token tok st =
  { input = st.input; position = st.position; tokens = (tok::st.tokens);
    line_number = st.line_number; column_number = st.column_number }

(** val take_while : (char -> bool) -> string -> string*string **)

let rec take_while f s = match s with
| "" -> "",""
| String.make 1 (%s) ^ %s (c, rest) ->
  if f c
  then let taken,remaining = take_while f rest in
       (String.make 1 (%s) ^ %s (c, taken)),remaining
  else "",s

(** val is_command_char : char -> bool **)

let is_command_char =
  is_letter

(** val is_whitespace : char -> bool **)

let is_whitespace c =
  let n0 = nat_of_ascii c in
  if if Nat.eqb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
          (succ 0))))))))))))))))))))))))))))))))
     then true
     else Nat.eqb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
            0)))))))))
  then true
  else if Nat.eqb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ 0))))))))))
       then true
       else Nat.eqb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ 0)))))))))))))

(** val is_text_char : char -> bool **)

let is_text_char c =
  if is_letter c
  then true
  else let n0 = nat_of_ascii c in
       if Nat.leb (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ
            0)))))))))))))))))))))))))))))))))))))))))))))))) n0
       then Nat.leb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ
              0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       else false

(** val lex_command : lexer_state -> latex_token*lexer_state **)

let lex_command st =
  match st.input with
  | "" -> TEOF,st
  | String.make 1 (%s) ^ %s (backslash, _) ->
    (match ascii_dec backslash ascii_backslash with
     | Left ->
       let st' = advance_char st in
       let cmd_name,remaining = take_while is_command_char st'.input in
       (match remaining with
        | "" ->
          let final_st = { input = remaining; position =
            (add st'.position (length cmd_name)); tokens = st'.tokens;
            line_number = st'.line_number; column_number =
            (add st'.column_number (length cmd_name)) }
          in
          (TCommand cmd_name),final_st
        | String.make 1 (%s) ^ %s (star, rest') ->
          (match ascii_dec star
                   (ascii_of_nat (succ (succ (succ (succ (succ (succ (succ
                     (succ (succ (succ (succ (succ (succ (succ (succ (succ
                     (succ (succ (succ (succ (succ (succ (succ (succ (succ
                     (succ (succ (succ (succ (succ (succ (succ (succ (succ
                     (succ (succ (succ (succ (succ (succ (succ (succ
                     0))))))))))))))))))))))))))))))))))))))))))) with
           | Left ->
             let final_name = append cmd_name "*" in
             let final_st = { input = rest'; position =
               (add st'.position (length final_name)); tokens = st'.tokens;
               line_number = st'.line_number; column_number =
               (add st'.column_number (length final_name)) }
             in
             (TCommand final_name),final_st
           | Right ->
             let final_st = { input = remaining; position =
               (add st'.position (length cmd_name)); tokens = st'.tokens;
               line_number = st'.line_number; column_number =
               (add st'.column_number (length cmd_name)) }
             in
             (TCommand cmd_name),final_st))
     | Right -> TEOF,st)

(** val lex_whitespace : lexer_state -> latex_token*lexer_state **)

let lex_whitespace st =
  let spaces,remaining = take_while is_whitespace st.input in
  let final_st = { input = remaining; position =
    (add st.position (length spaces)); tokens = st.tokens; line_number =
    st.line_number; column_number = (add st.column_number (length spaces)) }
  in
  TSpace,final_st

(** val lex_comment : lexer_state -> latex_token*lexer_state **)

let lex_comment st =
  match st.input with
  | "" -> TEOF,st
  | String.make 1 (%s) ^ %s (percent, _) ->
    (match ascii_dec percent ascii_percent with
     | Left ->
       let st' = advance_char st in
       let comment_text,remaining =
         take_while (fun c ->
           negb
             (Nat.eqb (nat_of_ascii c) (succ (succ (succ (succ (succ (succ
               (succ (succ (succ (succ 0)))))))))))) st'.input
       in
       let final_st = { input = remaining; position =
         (add st'.position (length comment_text)); tokens = st'.tokens;
         line_number = st'.line_number; column_number =
         (add st'.column_number (length comment_text)) }
       in
       (TComment comment_text),final_st
     | Right -> TEOF,st)

(** val lex_text : lexer_state -> latex_token*lexer_state **)

let lex_text st =
  match peek_char st with
  | Some c ->
    if is_text_char c
    then let text,remaining = take_while is_text_char st.input in
         let final_st = { input = remaining; position =
           (add st.position (length text)); tokens = st.tokens; line_number =
           st.line_number; column_number =
           (add st.column_number (length text)) }
         in
         (TText text),final_st
    else let st' = advance_char st in
         (TText (String.make 1 (%s) ^ %s (c, ""))),st'
  | None -> TEOF,st

(** val lex_step : lexer_state -> (latex_token*lexer_state) option **)

let lex_step st =
  match peek_char st with
  | Some c ->
    (match default_catcodes c with
     | CatEscape -> Some (lex_command st)
     | CatBeginGroup -> let st' = advance_char st in Some (TBeginGroup,st')
     | CatEndGroup -> let st' = advance_char st in Some (TEndGroup,st')
     | CatMathShift -> let st' = advance_char st in Some (TMathShift,st')
     | CatAlignment -> let st' = advance_char st in Some (TAlignment,st')
     | CatParameter -> let st' = advance_char st in Some (TParameter,st')
     | CatSuperscript -> let st' = advance_char st in Some (TSuperscript,st')
     | CatSubscript -> let st' = advance_char st in Some (TSubscript,st')
     | CatSpace -> Some (lex_whitespace st)
     | CatComment -> Some (lex_comment st)
     | _ -> Some (lex_text st))
  | None -> None

(** val lex_all_steps : lexer_state -> int -> latex_token list **)

let rec lex_all_steps st fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> rev st.tokens)
    (fun n0 ->
    match lex_step st with
    | Some p -> let tok,st' = p in lex_all_steps (add_token tok st') n0
    | None -> rev st.tokens)
    fuel

(** val lex_string : string -> latex_token list **)

let lex_string s =
  let fuel = mul (succ (succ 0)) (length s) in
  lex_all_steps (initial_state s) fuel

(** val lex_from_string : string -> latex_token list **)

let lex_from_string =
  lex_string

type checkpoint_state = { cp_position : int; cp_tokens : latex_token list;
                          cp_line : int; cp_column : int;
                          cp_catcodes : (char -> catcode); cp_in_math : 
                          bool; cp_env_stack : string list }

type edit_operation =
| Insert of int * string
| Delete of int * int
| Replace of int * int * string

type incremental_result = { ir_tokens : latex_token list;
                            ir_checkpoints : checkpoint_state list;
                            ir_stats : (int*int) }

(** val checkpoint_interval : int **)

let checkpoint_interval = 1000

(** val create_checkpoint :
    lexer_state -> bool -> string list -> checkpoint_state **)

let create_checkpoint st in_math env_stack =
  { cp_position = st.position; cp_tokens = (rev st.tokens); cp_line =
    st.line_number; cp_column = st.column_number; cp_catcodes =
    default_catcodes; cp_in_math = in_math; cp_env_stack = env_stack }

(** val string_skip : int -> string -> string **)

let rec string_skip n0 s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> s)
    (fun n' ->
    match s with
    | "" -> ""
    | String.make 1 (%s) ^ %s (_, rest) -> string_skip n' rest)
    n0

(** val find_checkpoint_before :
    int -> checkpoint_state list -> checkpoint_state option **)

let rec find_checkpoint_before pos = function
| [] -> None
| cp::rest ->
  (match rest with
   | [] -> if Nat.leb cp.cp_position pos then Some cp else None
   | next_cp::_ ->
     if if Nat.leb cp.cp_position pos
        then Nat.ltb pos next_cp.cp_position
        else false
     then Some cp
     else find_checkpoint_before pos rest)

(** val string_take : int -> string -> string **)

let rec string_take n0 s =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> "")
    (fun n' ->
    match s with
    | "" -> ""
    | String.make 1 (%s) ^ %s (c, rest) ->
      String.make 1 (%s) ^ %s (c, (string_take n' rest)))
    n0

(** val string_substring : int -> int -> string -> string **)

let string_substring start len s =
  string_take len (string_skip start s)

(** val apply_edit_to_string : string -> edit_operation -> string **)

let apply_edit_to_string s = function
| Insert (pos, text) ->
  append (string_take pos s) (append text (string_skip pos s))
| Delete (pos, len) ->
  append (string_take pos s) (string_skip (add pos len) s)
| Replace (pos, len, text) ->
  append (string_take pos s) (append text (string_skip (add pos len) s))

(** val lex_incremental :
    string -> checkpoint_state list -> edit_operation -> incremental_result **)

let lex_incremental doc checkpoints op =
  let new_doc = apply_edit_to_string doc op in
  let edit_pos =
    match op with
    | Insert (pos, _) -> pos
    | Delete (pos, _) -> pos
    | Replace (pos, _, _) -> pos
  in
  (match find_checkpoint_before edit_pos checkpoints with
   | Some cp ->
     let relex_start = cp.cp_position in
     let edit_size =
       match op with
       | Insert (_, text) -> length text
       | Delete (_, len) -> len
       | Replace (_, len, text) -> max (length text) len
     in
     let relex_end =
       if Nat.leb edit_size (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ 0))))))))))
       then min
              (add edit_pos (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                (succ (succ
                0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              (length new_doc)
       else length new_doc
     in
     let relex_content =
       string_substring relex_start (sub relex_end relex_start) new_doc
     in
     let new_tokens = lex_from_string relex_content in
     let final_tokens = app cp.cp_tokens new_tokens in
     { ir_tokens = final_tokens; ir_checkpoints = checkpoints; ir_stats =
     ((sub relex_end relex_start),(length new_doc)) }
   | None ->
     let tokens0 = lex_from_string new_doc in
     { ir_tokens = tokens0; ir_checkpoints = []; ir_stats =
     ((length new_doc),(length new_doc)) })

type checkpoint_lexer_state = { cl_base : lexer_state;
                                cl_checkpoints : checkpoint_state list;
                                cl_last_checkpoint : int; cl_in_math : 
                                bool; cl_env_stack : string list }

(** val checkpoint_lex_step :
    checkpoint_lexer_state -> (latex_token*checkpoint_lexer_state) option **)

let checkpoint_lex_step st =
  match lex_step st.cl_base with
  | Some p ->
    let tok,new_base = p in
    let should_checkpoint =
      Nat.leb checkpoint_interval
        (sub new_base.position st.cl_last_checkpoint)
    in
    let new_checkpoints =
      if should_checkpoint
      then (create_checkpoint new_base st.cl_in_math st.cl_env_stack)::st.cl_checkpoints
      else st.cl_checkpoints
    in
    let new_last =
      if should_checkpoint then new_base.position else st.cl_last_checkpoint
    in
    let new_math =
      match tok with
      | TMathShift -> negb st.cl_in_math
      | _ -> st.cl_in_math
    in
    let new_env_stack =
      match tok with
      | TCommand s ->
        (match s with
         | "" -> st.cl_env_stack
         | String.make 1 (%s) ^ %s (a, s0) ->
           let %s (b, b0, b1, b2, b3, b4, b5, b6) = a in
           if b
           then if b0
                then st.cl_env_stack
                else if b1
                     then if b2
                          then st.cl_env_stack
                          else if b3
                               then st.cl_env_stack
                               else if b4
                                    then if b5
                                         then if b6
                                              then st.cl_env_stack
                                              else (match s0 with
                                                    | "" -> st.cl_env_stack
                                                    | String.make 1 (%s) ^ %s (
                                                        a0, s1) ->
                                                      let %s (b7, b8, b9,
                                                              b10, b11, b12,
                                                              b13, b14) = a0
                                                      in
                                                      if b7
                                                      then st.cl_env_stack
                                                      else if b8
                                                           then if b9
                                                                then 
                                                                  if b10
                                                                  then 
                                                                    if b11
                                                                    then 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    (match s1 with
                                                                    | "" ->
                                                                    st.cl_env_stack
                                                                    | String.make 1 (%s) ^ %s (
                                                                    a1, s2) ->
                                                                    let %s (
                                                                    b15, b16,
                                                                    b17, b18,
                                                                    b19, b20,
                                                                    b21, b22) =
                                                                    a1
                                                                    in
                                                                    if b15
                                                                    then 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    (match s2 with
                                                                    | "" ->
                                                                    (match st.cl_env_stack with
                                                                    | [] -> []
                                                                    | _::rest ->
                                                                    rest)
                                                                    | String.make 1 (%s) ^ %s (
                                                                    _, _) ->
                                                                    st.cl_env_stack)
                                                                    else 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    st.cl_env_stack)
                                                                    else 
                                                                    st.cl_env_stack
                                                                    else 
                                                                    st.cl_env_stack
                                                                  else 
                                                                    st.cl_env_stack
                                                                else 
                                                                  st.cl_env_stack
                                                           else st.cl_env_stack)
                                         else st.cl_env_stack
                                    else st.cl_env_stack
                     else st.cl_env_stack
           else st.cl_env_stack)
      | _ -> st.cl_env_stack
    in
    Some (tok,{ cl_base = new_base; cl_checkpoints = new_checkpoints;
    cl_last_checkpoint = new_last; cl_in_math = new_math; cl_env_stack =
    new_env_stack })
  | None -> None

(** val lex_with_checkpoints_fuel :
    checkpoint_lexer_state -> int -> latex_token list*checkpoint_state list **)

let rec lex_with_checkpoints_fuel st fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (rev st.cl_base.tokens),(rev st.cl_checkpoints))
    (fun n0 ->
    match checkpoint_lex_step st with
    | Some p ->
      let tok,st' = p in
      let updated_base = add_token tok st'.cl_base in
      let updated_st = { cl_base = updated_base; cl_checkpoints =
        st'.cl_checkpoints; cl_last_checkpoint = st'.cl_last_checkpoint;
        cl_in_math = st'.cl_in_math; cl_env_stack = st'.cl_env_stack }
      in
      lex_with_checkpoints_fuel updated_st n0
    | None -> (rev st.cl_base.tokens),(rev st.cl_checkpoints))
    fuel

(** val lex_document_with_checkpoints :
    string -> latex_token list*checkpoint_state list **)

let lex_document_with_checkpoints doc =
  let initial_state0 = { cl_base = (initial_state doc); cl_checkpoints = [];
    cl_last_checkpoint = 0; cl_in_math = false; cl_env_stack = [] }
  in
  let fuel =
    mul (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      0)))))))))) (length doc)
  in
  lex_with_checkpoints_fuel initial_state0 fuel
