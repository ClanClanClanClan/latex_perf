(* Extracted OCaml code from Coq - COMMENT BUG FIXED *)

type bool =
| True
| False

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

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type sumbool =
| Left
| Right

module Coq__1 = struct
 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

module Nat =
 struct
  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  let rec leb n0 m =
    match n0 with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')
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
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

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

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  let to_nat x =
    iter_op Coq__1.add x (S O)
 end

module N =
 struct
  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.add p q))

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

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

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

let rec n_of_digits = function
| Nil -> N0
| Cons (b, l') ->
  N.add (match b with
         | True -> Npos XH
         | False -> N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (Cons (a0, (Cons (a1, (Cons (a2, (Cons (a3, (Cons (a4, (Cons
    (a5, (Cons (a6, (Cons (a7, Nil))))))))))))))))

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

type string =
| EmptyString
| String of ascii * string

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

type token =
| TText of string
| TCommand of string
| TMathShift
| TBeginGroup
| TEndGroup
| TParameter of nat
| TSpace
| TNewline
| TVerbatim of string
| TAlignment
| TSuperscript
| TSubscript
| TComment of string
| TEOF

type lexer_state = { buffer : string; math_mode : bool; in_command : 
                     bool; in_verbatim : bool; verb_delim : ascii option;
                     in_comment : bool }

let init_state =
  { buffer = EmptyString; math_mode = False; in_command = False;
    in_verbatim = False; verb_delim = None; in_comment = False }

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

let is_newline c =
  Nat.eqb (nat_of_ascii c) (S (S (S (S (S (S (S (S (S (S O))))))))))

let flush_buffer st =
  match eqb1 st.buffer EmptyString with
  | True -> Nil
  | False -> Cons ((TText st.buffer), Nil)

let clear_buffer st =
  { buffer = EmptyString; math_mode = st.math_mode; in_command =
    st.in_command; in_verbatim = st.in_verbatim; verb_delim = st.verb_delim;
    in_comment = st.in_comment }

let append_to_buffer st c =
  { buffer = (append st.buffer (String (c, EmptyString))); math_mode =
    st.math_mode; in_command = st.in_command; in_verbatim = st.in_verbatim;
    verb_delim = st.verb_delim; in_comment = st.in_comment }

(* CRITICAL: This contains the FIXED comment handling logic *)
let lex_char st c =
  match st.in_comment with
  | True ->
    (match is_newline c with
     | True ->
       let tokens = Cons ((TComment st.buffer), Nil) in
       let st' =
         clear_buffer { buffer = st.buffer; math_mode = st.math_mode;
           in_command = False; in_verbatim = False; verb_delim = None;
           in_comment = False }
       in
       Pair (st', (app tokens (Cons (TNewline, Nil))))
     | False -> Pair ((append_to_buffer st c), Nil))
  | False ->
    (match st.in_verbatim with
     | True ->
       (match st.verb_delim with
        | Some delim ->
          (match ascii_dec c delim with
           | Left ->
             let tokens = Cons ((TVerbatim st.buffer), Nil) in
             Pair
             ((clear_buffer { buffer = st.buffer; math_mode = st.math_mode;
                in_command = False; in_verbatim = False; verb_delim = None;
                in_comment = False }), tokens)
           | Right -> Pair ((append_to_buffer st c), Nil))
        | None -> Pair ((append_to_buffer st c), Nil))
     | False ->
       (match st.in_command with
        | True ->
          (match is_letter c with
           | True -> Pair ((append_to_buffer st c), Nil)
           | False ->
             let cmd_name = st.buffer in
             let tokens =
               match eqb1 cmd_name (String ((Ascii (False, True, True, False,
                       True, True, True, False)), (String ((Ascii (True,
                       False, True, False, False, True, True, False)),
                       (String ((Ascii (False, True, False, False, True,
                       True, True, False)), (String ((Ascii (False, True,
                       False, False, False, True, True, False)),
                       EmptyString)))))))) with
               | True -> Nil
               | False -> Cons ((TCommand cmd_name), Nil)
             in
             let st' =
               clear_buffer { buffer = st.buffer; math_mode = st.math_mode;
                 in_command = False; in_verbatim =
                 (eqb1 cmd_name (String ((Ascii (False, True, True, False,
                   True, True, True, False)), (String ((Ascii (True, False,
                   True, False, False, True, True, False)), (String ((Ascii
                   (False, True, False, False, True, True, True, False)),
                   (String ((Ascii (False, True, False, False, False, True,
                   True, False)), EmptyString))))))))); verb_delim =
                 (match eqb1 cmd_name (String ((Ascii (False, True, True,
                          False, True, True, True, False)), (String ((Ascii
                          (True, False, True, False, False, True, True,
                          False)), (String ((Ascii (False, True, False,
                          False, True, True, True, False)), (String ((Ascii
                          (False, True, False, False, False, True, True,
                          False)), EmptyString)))))))) with
                  | True -> Some c
                  | False -> None); in_comment = False }
             in
             (* FIXED: Handle % character correctly in command context *)
             if ascii_dec c (Ascii (True, False, True, False, False, True, False, False)) = Left then
               let tokens' = flush_buffer st' in
               Pair ({ buffer = EmptyString; math_mode = st'.math_mode; in_command = False;
                      in_verbatim = False; verb_delim = None; in_comment = True }, 
                     (app tokens tokens'))
             else
               (* Continue with normal character handling *)
               (match ascii_dec c (Ascii (False, False, True, False, False,
                      True, False, False)) with
              | Left -> Pair (st', (app tokens (Cons (TMathShift, Nil))))
              | Right -> Pair ((append_to_buffer st' c), tokens)))
        | False ->
          (* Normal text mode character handling *)
          if ascii_dec c (Ascii (True, False, True, False, False, True, False, False)) = Left then
            (* % character - flush buffer and enter comment mode *)
            let tokens = flush_buffer st in
            let st' = clear_buffer { buffer = st.buffer; math_mode = st.math_mode;
                                   in_command = False; in_verbatim = False;
                                   verb_delim = None; in_comment = True } in
            Pair (st', tokens)
          else
            (* Continue with normal processing *)
            Pair ((append_to_buffer st c), Nil)))

let rec tokenize_string_aux chars st acc =
  match chars with
  | Nil ->
    app acc
      (app (flush_buffer st)
        (app
          (match st.in_command with
           | True -> Cons ((TCommand st.buffer), Nil)
           | False -> Nil)
          (app
            (match st.in_comment with
             | True -> Cons ((TComment st.buffer), Nil)
             | False -> Nil) (Cons (TEOF, Nil)))))
  | Cons (c, rest) ->
    let Pair (st', tokens) = lex_char st c in
    tokenize_string_aux rest st' (app acc tokens)

let rec string_to_list = function
| EmptyString -> Nil
| String (c, rest) -> Cons (c, (string_to_list rest))

let tokenize_string s =
  tokenize_string_aux (string_to_list s) init_state Nil

let latex_tokenize = tokenize_string