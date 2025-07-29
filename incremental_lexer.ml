
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

(** val max : nat -> nat -> nat **)

let rec max n0 m =
  match n0 with
  | O -> m
  | S n' -> (match m with
             | O -> n0
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n0 m =
  match n0 with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n0 m =
    leb (S n0) m
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

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
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

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val zero : ascii **)

let zero =
  Ascii (False, False, False, False, False, False, False, False)

(** val one : ascii **)

let one =
  Ascii (True, False, False, False, False, False, False, False)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
| Ascii (a1, a2, a3, a4, a5, a6, a7, _) ->
  Ascii (c, a1, a2, a3, a4, a5, a6, a7)

(** val ascii_dec : ascii -> ascii -> sumbool **)

let ascii_dec a b =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
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

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | O -> zero
    | S n' ->
      (match p with
       | XI p' -> shift True (loop n' p')
       | XO p' -> shift False (loop n' p')
       | XH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> ascii **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> ascii **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| Nil -> N0
| Cons (b, l') ->
  N.add (match b with
         | True -> Npos XH
         | False -> N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : ascii -> n **)

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (Cons (a0, (Cons (a1, (Cons (a2, (Cons (a3, (Cons (a4, (Cons
    (a5, (Cons (a6, (Cons (a7, Nil))))))))))))))))

(** val nat_of_ascii : ascii -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

type string =
| EmptyString
| String of ascii * string

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

(** val length : string -> nat **)

let rec length = function
| EmptyString -> O
| String (_, s') -> S (length s')

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

type catcode_table = ascii -> catcode

(** val ascii_backslash : ascii **)

let ascii_backslash =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_lbrace : ascii **)

let ascii_lbrace =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_rbrace : ascii **)

let ascii_rbrace =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_dollar : ascii **)

let ascii_dollar =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))

(** val ascii_ampersand : ascii **)

let ascii_ampersand =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))

(** val ascii_hash : ascii **)

let ascii_hash =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))

(** val ascii_caret : ascii **)

let ascii_caret =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_underscore : ascii **)

let ascii_underscore =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_space : ascii **)

let ascii_space =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))

(** val ascii_percent : ascii **)

let ascii_percent =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))

(** val is_letter : ascii -> bool **)

let is_letter c =
  let n0 = nat_of_ascii c in
  (match match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 n0 with
         | True ->
           Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         | False -> False with
   | True -> True
   | False ->
     (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              n0 with
      | True ->
        Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | False -> False))

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
                               (match is_letter c with
                                | True -> CatLetter
                                | False -> CatOther))))))))))

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

type lexer_state = { input : string; position : nat;
                     tokens : latex_token list; line_number : nat;
                     column_number : nat }

(** val initial_state : string -> lexer_state **)

let initial_state s =
  { input = s; position = O; tokens = Nil; line_number = (S O);
    column_number = (S O) }

(** val peek_char : lexer_state -> ascii option **)

let peek_char st =
  match st.input with
  | EmptyString -> None
  | String (c, _) -> Some c

(** val advance_char : lexer_state -> lexer_state **)

let advance_char st =
  match st.input with
  | EmptyString -> st
  | String (c, rest) ->
    let new_column =
      match ascii_dec c
              (ascii_of_nat (S (S (S (S (S (S (S (S (S (S O))))))))))) with
      | Left -> S O
      | Right -> S st.column_number
    in
    let new_line =
      match ascii_dec c
              (ascii_of_nat (S (S (S (S (S (S (S (S (S (S O))))))))))) with
      | Left -> S st.line_number
      | Right -> st.line_number
    in
    { input = rest; position = (S st.position); tokens = st.tokens;
    line_number = new_line; column_number = new_column }

(** val add_token : latex_token -> lexer_state -> lexer_state **)

let add_token tok st =
  { input = st.input; position = st.position; tokens = (Cons (tok,
    st.tokens)); line_number = st.line_number; column_number =
    st.column_number }

(** val take_while : (ascii -> bool) -> string -> (string, string) prod **)

let rec take_while f s = match s with
| EmptyString -> Pair (EmptyString, EmptyString)
| String (c, rest) ->
  (match f c with
   | True ->
     let Pair (taken, remaining) = take_while f rest in
     Pair ((String (c, taken)), remaining)
   | False -> Pair (EmptyString, s))

(** val is_command_char : ascii -> bool **)

let is_command_char =
  is_letter

(** val is_whitespace : ascii -> bool **)

let is_whitespace c =
  let n0 = nat_of_ascii c in
  (match match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))) with
         | True -> True
         | False -> Nat.eqb n0 (S (S (S (S (S (S (S (S (S O))))))))) with
   | True -> True
   | False ->
     (match Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S O)))))))))) with
      | True -> True
      | False ->
        Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

(** val is_text_char : ascii -> bool **)

let is_text_char c =
  match is_letter c with
  | True -> True
  | False ->
    let n0 = nat_of_ascii c in
    (match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))))) n0 with
     | True ->
       Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | False -> False)

(** val lex_command : lexer_state -> (latex_token, lexer_state) prod **)

let lex_command st =
  match st.input with
  | EmptyString -> Pair (TEOF, st)
  | String (backslash, _) ->
    (match ascii_dec backslash ascii_backslash with
     | Left ->
       let st' = advance_char st in
       let Pair (cmd_name, remaining) = take_while is_command_char st'.input
       in
       (match remaining with
        | EmptyString ->
          let final_st = { input = remaining; position =
            (add st'.position (length cmd_name)); tokens = st'.tokens;
            line_number = st'.line_number; column_number =
            (add st'.column_number (length cmd_name)) }
          in
          Pair ((TCommand cmd_name), final_st)
        | String (star, rest') ->
          (match ascii_dec star
                   (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S
                     O))))))))))))))))))))))))))))))))))))))))))) with
           | Left ->
             let final_name =
               append cmd_name (String ((Ascii (False, True, False, True,
                 False, True, False, False)), EmptyString))
             in
             let final_st = { input = rest'; position =
               (add st'.position (length final_name)); tokens = st'.tokens;
               line_number = st'.line_number; column_number =
               (add st'.column_number (length final_name)) }
             in
             Pair ((TCommand final_name), final_st)
           | Right ->
             let final_st = { input = remaining; position =
               (add st'.position (length cmd_name)); tokens = st'.tokens;
               line_number = st'.line_number; column_number =
               (add st'.column_number (length cmd_name)) }
             in
             Pair ((TCommand cmd_name), final_st)))
     | Right -> Pair (TEOF, st))

(** val lex_whitespace : lexer_state -> (latex_token, lexer_state) prod **)

let lex_whitespace st =
  let Pair (spaces, remaining) = take_while is_whitespace st.input in
  let final_st = { input = remaining; position =
    (add st.position (length spaces)); tokens = st.tokens; line_number =
    st.line_number; column_number = (add st.column_number (length spaces)) }
  in
  Pair (TSpace, final_st)

(** val lex_comment : lexer_state -> (latex_token, lexer_state) prod **)

let lex_comment st =
  match st.input with
  | EmptyString -> Pair (TEOF, st)
  | String (percent, _) ->
    (match ascii_dec percent ascii_percent with
     | Left ->
       let st' = advance_char st in
       let Pair (comment_text, remaining) =
         take_while (fun c ->
           negb
             (Nat.eqb (nat_of_ascii c) (S (S (S (S (S (S (S (S (S (S
               O)))))))))))) st'.input
       in
       let final_st = { input = remaining; position =
         (add st'.position (length comment_text)); tokens = st'.tokens;
         line_number = st'.line_number; column_number =
         (add st'.column_number (length comment_text)) }
       in
       Pair ((TComment comment_text), final_st)
     | Right -> Pair (TEOF, st))

(** val lex_text : lexer_state -> (latex_token, lexer_state) prod **)

let lex_text st =
  match peek_char st with
  | Some c ->
    (match is_text_char c with
     | True ->
       let Pair (text, remaining) = take_while is_text_char st.input in
       let final_st = { input = remaining; position =
         (add st.position (length text)); tokens = st.tokens; line_number =
         st.line_number; column_number =
         (add st.column_number (length text)) }
       in
       Pair ((TText text), final_st)
     | False ->
       let st' = advance_char st in
       Pair ((TText (String (c, EmptyString))), st'))
  | None -> Pair (TEOF, st)

(** val lex_step : lexer_state -> (latex_token, lexer_state) prod option **)

let lex_step st =
  match peek_char st with
  | Some c ->
    (match default_catcodes c with
     | CatEscape -> Some (lex_command st)
     | CatBeginGroup ->
       let st' = advance_char st in Some (Pair (TBeginGroup, st'))
     | CatEndGroup ->
       let st' = advance_char st in Some (Pair (TEndGroup, st'))
     | CatMathShift ->
       let st' = advance_char st in Some (Pair (TMathShift, st'))
     | CatAlignment ->
       let st' = advance_char st in Some (Pair (TAlignment, st'))
     | CatParameter ->
       let st' = advance_char st in Some (Pair (TParameter, st'))
     | CatSuperscript ->
       let st' = advance_char st in Some (Pair (TSuperscript, st'))
     | CatSubscript ->
       let st' = advance_char st in Some (Pair (TSubscript, st'))
     | CatSpace -> Some (lex_whitespace st)
     | CatComment -> Some (lex_comment st)
     | _ -> Some (lex_text st))
  | None -> None

(** val lex_all_steps : lexer_state -> nat -> latex_token list **)

let rec lex_all_steps st = function
| O -> rev st.tokens
| S n0 ->
  (match lex_step st with
   | Some p -> let Pair (tok, st') = p in lex_all_steps (add_token tok st') n0
   | None -> rev st.tokens)

(** val lex_string : string -> latex_token list **)

let lex_string s =
  let fuel = mul (S (S O)) (length s) in lex_all_steps (initial_state s) fuel

(** val lex_from_string : string -> latex_token list **)

let lex_from_string =
  lex_string

type checkpoint_state = { cp_position : nat; cp_tokens : latex_token list;
                          cp_line : nat; cp_column : nat;
                          cp_catcodes : (ascii -> catcode);
                          cp_in_math : bool; cp_env_stack : string list }

type edit_operation =
| Insert of nat * string
| Delete of nat * nat
| Replace of nat * nat * string

type incremental_result = { ir_tokens : latex_token list;
                            ir_checkpoints : checkpoint_state list;
                            ir_stats : (nat, nat) prod }

(** val checkpoint_interval : nat **)

let checkpoint_interval =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val create_checkpoint :
    lexer_state -> bool -> string list -> checkpoint_state **)

let create_checkpoint = IncrementalLexer.create_checkpoint

(** val string_skip : nat -> string -> string **)

let rec string_skip n0 s =
  match n0 with
  | O -> s
  | S n' ->
    (match s with
     | EmptyString -> EmptyString
     | String (_, rest) -> string_skip n' rest)

(** val find_checkpoint_before :
    nat -> checkpoint_state list -> checkpoint_state option **)

let rec find_checkpoint_before = IncrementalLexer.find_checkpoint_before

(** val string_take : nat -> string -> string **)

let rec string_take n0 s =
  match n0 with
  | O -> EmptyString
  | S n' ->
    (match s with
     | EmptyString -> EmptyString
     | String (c, rest) -> String (c, (string_take n' rest)))

(** val string_substring : nat -> nat -> string -> string **)

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
       match Nat.leb edit_size (S (S (S (S (S (S (S (S (S (S O)))))))))) with
       | True ->
         min
           (add edit_pos (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           (length new_doc)
       | False -> length new_doc
     in
     let relex_content =
       string_substring relex_start (sub relex_end relex_start) new_doc
     in
     let new_tokens = lex_from_string relex_content in
     let final_tokens = app cp.cp_tokens new_tokens in
     { ir_tokens = final_tokens; ir_checkpoints = checkpoints; ir_stats =
     (Pair ((sub relex_end relex_start), (length new_doc))) }
   | None ->
     let tokens0 = lex_from_string new_doc in
     { ir_tokens = tokens0; ir_checkpoints = Nil; ir_stats = (Pair
     ((length new_doc), (length new_doc))) })

type checkpoint_lexer_state = { cl_base : lexer_state;
                                cl_checkpoints : checkpoint_state list;
                                cl_last_checkpoint : nat; cl_in_math : 
                                bool; cl_env_stack : string list }

(** val checkpoint_lex_step :
    checkpoint_lexer_state -> (latex_token, checkpoint_lexer_state) prod
    option **)

let checkpoint_lex_step st =
  match lex_step st.cl_base with
  | Some p ->
    let Pair (tok, new_base) = p in
    let should_checkpoint =
      Nat.leb checkpoint_interval
        (sub new_base.position st.cl_last_checkpoint)
    in
    let new_checkpoints =
      match should_checkpoint with
      | True ->
        Cons ((create_checkpoint new_base st.cl_in_math st.cl_env_stack),
          st.cl_checkpoints)
      | False -> st.cl_checkpoints
    in
    let new_last =
      match should_checkpoint with
      | True -> new_base.position
      | False -> st.cl_last_checkpoint
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
         | EmptyString -> st.cl_env_stack
         | String (a, s0) ->
           let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = a in
           (match b with
            | True ->
              (match b0 with
               | True -> st.cl_env_stack
               | False ->
                 (match b1 with
                  | True ->
                    (match b2 with
                     | True -> st.cl_env_stack
                     | False ->
                       (match b3 with
                        | True -> st.cl_env_stack
                        | False ->
                          (match b4 with
                           | True ->
                             (match b5 with
                              | True ->
                                (match b6 with
                                 | True -> st.cl_env_stack
                                 | False ->
                                   (match s0 with
                                    | EmptyString -> st.cl_env_stack
                                    | String (a0, s1) ->
                                      let Ascii (b7, b8, b9, b10, b11, b12,
                                                 b13, b14) = a0
                                      in
                                      (match b7 with
                                       | True -> st.cl_env_stack
                                       | False ->
                                         (match b8 with
                                          | True ->
                                            (match b9 with
                                             | True ->
                                               (match b10 with
                                                | True ->
                                                  (match b11 with
                                                   | True -> st.cl_env_stack
                                                   | False ->
                                                     (match b12 with
                                                      | True ->
                                                        (match b13 with
                                                         | True ->
                                                           (match b14 with
                                                            | True ->
                                                              st.cl_env_stack
                                                            | False ->
                                                              (match s1 with
                                                               | EmptyString ->
                                                                 st.cl_env_stack
                                                               | String (
                                                                   a1, s2) ->
                                                                 let Ascii (
                                                                   b15, b16,
                                                                   b17, b18,
                                                                   b19, b20,
                                                                   b21, b22) =
                                                                   a1
                                                                 in
                                                                 (match b15 with
                                                                  | True ->
                                                                    st.cl_env_stack
                                                                  | False ->
                                                                    (match b16 with
                                                                    | True ->
                                                                    st.cl_env_stack
                                                                    | False ->
                                                                    (match b17 with
                                                                    | True ->
                                                                    (match b18 with
                                                                    | True ->
                                                                    st.cl_env_stack
                                                                    | False ->
                                                                    (match b19 with
                                                                    | True ->
                                                                    st.cl_env_stack
                                                                    | False ->
                                                                    (match b20 with
                                                                    | True ->
                                                                    (match b21 with
                                                                    | True ->
                                                                    (match b22 with
                                                                    | True ->
                                                                    st.cl_env_stack
                                                                    | False ->
                                                                    (match s2 with
                                                                    | EmptyString ->
                                                                    (match st.cl_env_stack with
                                                                    | Nil ->
                                                                    Nil
                                                                    | Cons (
                                                                    _, rest) ->
                                                                    rest)
                                                                    | String (
                                                                    _, _) ->
                                                                    st.cl_env_stack))
                                                                    | False ->
                                                                    st.cl_env_stack)
                                                                    | False ->
                                                                    st.cl_env_stack)))
                                                                    | False ->
                                                                    st.cl_env_stack)))))
                                                         | False ->
                                                           st.cl_env_stack)
                                                      | False ->
                                                        st.cl_env_stack))
                                                | False -> st.cl_env_stack)
                                             | False -> st.cl_env_stack)
                                          | False -> st.cl_env_stack))))
                              | False -> st.cl_env_stack)
                           | False -> st.cl_env_stack)))
                  | False -> st.cl_env_stack))
            | False -> st.cl_env_stack))
      | _ -> st.cl_env_stack
    in
    Some (Pair (tok, { cl_base = new_base; cl_checkpoints = new_checkpoints;
    cl_last_checkpoint = new_last; cl_in_math = new_math; cl_env_stack =
    new_env_stack }))
  | None -> None

(** val lex_with_checkpoints_fuel :
    checkpoint_lexer_state -> nat -> (latex_token list, checkpoint_state
    list) prod **)

let rec lex_with_checkpoints_fuel st = function
| O -> Pair ((rev st.cl_base.tokens), (rev st.cl_checkpoints))
| S n0 ->
  (match checkpoint_lex_step st with
   | Some p ->
     let Pair (tok, st') = p in
     let updated_base = add_token tok st'.cl_base in
     let updated_st = { cl_base = updated_base; cl_checkpoints =
       st'.cl_checkpoints; cl_last_checkpoint = st'.cl_last_checkpoint;
       cl_in_math = st'.cl_in_math; cl_env_stack = st'.cl_env_stack }
     in
     lex_with_checkpoints_fuel updated_st n0
   | None -> Pair ((rev st.cl_base.tokens), (rev st.cl_checkpoints)))

(** val lex_document_with_checkpoints :
    string -> (latex_token list, checkpoint_state list) prod **)

let lex_document_with_checkpoints doc =
  let initial_state0 = { cl_base = (initial_state doc); cl_checkpoints = Nil;
    cl_last_checkpoint = O; cl_in_math = False; cl_env_stack = Nil }
  in
  let fuel = mul (S (S (S (S (S (S (S (S (S (S O)))))))))) (length doc) in
  lex_with_checkpoints_fuel initial_state0 fuel
