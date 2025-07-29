(* Combined lexer and tokenizer for native compilation *)
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

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

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
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

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

(** val eqb0 : ascii -> ascii -> bool **)

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

(** val eqb1 : string -> string -> bool **)

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

(** val append : string -> string -> string **)

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

(** val init_state : lexer_state **)

let init_state =
  { buffer = EmptyString; math_mode = False; in_command = False;
    in_verbatim = False; verb_delim = None; in_comment = False }

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

(** val is_newline : ascii -> bool **)

let is_newline c =
  Nat.eqb (nat_of_ascii c) (S (S (S (S (S (S (S (S (S (S O))))))))))

(** val flush_buffer : lexer_state -> token list **)

let flush_buffer st =
  match eqb1 st.buffer EmptyString with
  | True -> Nil
  | False -> Cons ((TText st.buffer), Nil)

(** val clear_buffer : lexer_state -> lexer_state **)

let clear_buffer st =
  { buffer = EmptyString; math_mode = st.math_mode; in_command =
    st.in_command; in_verbatim = st.in_verbatim; verb_delim = st.verb_delim;
    in_comment = st.in_comment }

(** val append_to_buffer : lexer_state -> ascii -> lexer_state **)

let append_to_buffer st c =
  { buffer = (append st.buffer (String (c, EmptyString))); math_mode =
    st.math_mode; in_command = st.in_command; in_verbatim = st.in_verbatim;
    verb_delim = st.verb_delim; in_comment = st.in_comment }

(** val lex_char : lexer_state -> ascii -> (lexer_state, token list) prod **)

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
             (match ascii_dec c (Ascii (False, False, True, False, False,
                      True, False, False)) with
              | Left -> Pair (st', (app tokens (Cons (TMathShift, Nil))))
              | Right ->
                (match ascii_dec c (Ascii (True, True, False, True, True,
                         True, True, False)) with
                 | Left -> Pair (st', (app tokens (Cons (TBeginGroup, Nil))))
                 | Right ->
                   (match ascii_dec c (Ascii (True, False, True, True, True,
                            True, True, False)) with
                    | Left -> Pair (st', (app tokens (Cons (TEndGroup, Nil))))
                    | Right ->
                      (match ascii_dec c (Ascii (False, True, True, False,
                               False, True, False, False)) with
                       | Left ->
                         Pair (st', (app tokens (Cons (TAlignment, Nil))))
                       | Right ->
                         (match ascii_dec c (Ascii (False, True, True, True,
                                  True, False, True, False)) with
                          | Left ->
                            Pair (st',
                              (app tokens (Cons (TSuperscript, Nil))))
                          | Right ->
                            (match ascii_dec c (Ascii (True, True, True,
                                     True, True, False, True, False)) with
                             | Left ->
                               Pair (st',
                                 (app tokens (Cons (TSubscript, Nil))))
                             | Right ->
                               (match ascii_dec c (Ascii (True, False, True,
                                        False, False, True, False, False)) with
                                | Left ->
                                  let tokens' = flush_buffer st' in
                                  Pair ({ buffer = EmptyString; math_mode =
                                  st'.math_mode; in_command = False;
                                  in_verbatim = False; verb_delim = None;
                                  in_comment = True }, (app tokens tokens'))
                                | Right ->
                                  (match ascii_dec c (Ascii (False, False,
                                           True, True, True, False, True,
                                           False)) with
                                   | Left ->
                                     Pair ({ buffer = EmptyString;
                                       math_mode = st'.math_mode;
                                       in_command = True; in_verbatim =
                                       False; verb_delim = None; in_comment =
                                       False }, tokens)
                                   | Right ->
                                     (match ascii_dec c (Ascii (False, False,
                                              False, False, False, True,
                                              False, False)) with
                                      | Left ->
                                        Pair (st',
                                          (app tokens (Cons (TSpace, Nil))))
                                      | Right ->
                                        (match is_newline c with
                                         | True ->
                                           Pair (st',
                                             (app tokens (Cons (TNewline,
                                               Nil))))
                                         | False ->
                                           (match eqb1 cmd_name (String
                                                    ((Ascii (False, True,
                                                    True, False, True, True,
                                                    True, False)), (String
                                                    ((Ascii (True, False,
                                                    True, False, False, True,
                                                    True, False)), (String
                                                    ((Ascii (False, True,
                                                    False, False, True, True,
                                                    True, False)), (String
                                                    ((Ascii (False, True,
                                                    False, False, False,
                                                    True, True, False)),
                                                    EmptyString)))))))) with
                                            | True -> Pair (st', tokens)
                                            | False ->
                                              Pair ((append_to_buffer st' c),
                                                tokens)))))))))))))
        | False ->
          (match ascii_dec c (Ascii (False, False, True, False, False, True,
                   False, False)) with
           | Left ->
             let tokens = flush_buffer st in
             let st' =
               clear_buffer { buffer = st.buffer; math_mode =
                 (negb st.math_mode); in_command = False; in_verbatim =
                 False; verb_delim = None; in_comment = False }
             in
             Pair (st', (app tokens (Cons (TMathShift, Nil))))
           | Right ->
             (match ascii_dec c (Ascii (True, True, False, True, True, True,
                      True, False)) with
              | Left ->
                let tokens = flush_buffer st in
                let st' = clear_buffer st in
                Pair (st', (app tokens (Cons (TBeginGroup, Nil))))
              | Right ->
                (match ascii_dec c (Ascii (True, False, True, True, True,
                         True, True, False)) with
                 | Left ->
                   let tokens = flush_buffer st in
                   let st' = clear_buffer st in
                   Pair (st', (app tokens (Cons (TEndGroup, Nil))))
                 | Right ->
                   (match ascii_dec c (Ascii (False, False, True, True, True,
                            False, True, False)) with
                    | Left ->
                      let tokens = flush_buffer st in
                      let st' =
                        clear_buffer { buffer = st.buffer; math_mode =
                          st.math_mode; in_command = True; in_verbatim =
                          False; verb_delim = None; in_comment = False }
                      in
                      Pair (st', tokens)
                    | Right ->
                      (match ascii_dec c (Ascii (False, True, True, False,
                               False, True, False, False)) with
                       | Left ->
                         let tokens = flush_buffer st in
                         let st' = clear_buffer st in
                         Pair (st', (app tokens (Cons (TAlignment, Nil))))
                       | Right ->
                         (match ascii_dec c (Ascii (False, True, True, True,
                                  True, False, True, False)) with
                          | Left ->
                            let tokens = flush_buffer st in
                            let st' = clear_buffer st in
                            Pair (st',
                            (app tokens (Cons (TSuperscript, Nil))))
                          | Right ->
                            (match ascii_dec c (Ascii (True, True, True,
                                     True, True, False, True, False)) with
                             | Left ->
                               let tokens = flush_buffer st in
                               let st' = clear_buffer st in
                               Pair (st',
                               (app tokens (Cons (TSubscript, Nil))))
                             | Right ->
                               (match ascii_dec c (Ascii (True, False, True,
                                        False, False, True, False, False)) with
                                | Left ->
                                  let tokens = flush_buffer st in
                                  let st' =
                                    clear_buffer { buffer = st.buffer;
                                      math_mode = st.math_mode; in_command =
                                      False; in_verbatim = False;
                                      verb_delim = None; in_comment = True }
                                  in
                                  Pair (st', tokens)
                                | Right ->
                                  (match ascii_dec c (Ascii (False, False,
                                           False, False, False, True, False,
                                           False)) with
                                   | Left ->
                                     let tokens = flush_buffer st in
                                     let st' = clear_buffer st in
                                     Pair (st',
                                     (app tokens (Cons (TSpace, Nil))))
                                   | Right ->
                                     (match is_newline c with
                                      | True ->
                                        let tokens = flush_buffer st in
                                        let st' = clear_buffer st in
                                        Pair (st',
                                        (app tokens (Cons (TNewline, Nil))))
                                      | False ->
                                        Pair ((append_to_buffer st c), Nil)))))))))))))

(** val tokenize_string_aux :
    ascii list -> lexer_state -> token list -> token list **)

let rec tokenize_string_aux chars st acc =
  match chars with
  | Nil ->
    app acc
      (app (match st.in_comment with
            | True -> Nil
            | False -> flush_buffer st)
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

(** val string_to_list : string -> ascii list **)

let rec string_to_list = function
| EmptyString -> Nil
| String (c, rest) -> Cons (c, (string_to_list rest))

(** val tokenize_string : string -> token list **)

let tokenize_string s =
  tokenize_string_aux (string_to_list s) init_state Nil

(** val latex_tokenize : string -> token list **)

let latex_tokenize =
  tokenize_string

let bool_to_int = function True -> 1 | False -> 0;;

let rec coq_string_to_ocaml = function
  | EmptyString -> ""
  | String (c, rest) -> 
    let Ascii (b0,b1,b2,b3,b4,b5,b6,b7) = c in
    let code = (bool_to_int b0) + 2 * (bool_to_int b1) + 
               4 * (bool_to_int b2) + 8 * (bool_to_int b3) +
               16 * (bool_to_int b4) + 32 * (bool_to_int b5) +
               64 * (bool_to_int b6) + 128 * (bool_to_int b7) in
    String.make 1 (Char.chr code) ^ coq_string_to_ocaml rest;;

let int_to_bool = function 0 -> False | _ -> True;;

let rec ocaml_string_to_coq s =
  if String.length s = 0 then EmptyString
  else
    let c = s.[0] in
    let code = Char.code c in
    let b0 = int_to_bool (code land 1) in
    let b1 = int_to_bool (code land 2) in
    let b2 = int_to_bool (code land 4) in
    let b3 = int_to_bool (code land 8) in
    let b4 = int_to_bool (code land 16) in
    let b5 = int_to_bool (code land 32) in
    let b6 = int_to_bool (code land 64) in
    let b7 = int_to_bool (code land 128) in
    let ascii_char = Ascii (b0,b1,b2,b3,b4,b5,b6,b7) in
    String (ascii_char, ocaml_string_to_coq (String.sub s 1 (String.length s - 1)));;

let write_token_simple = function
  | TText s -> Printf.printf "TEXT:%s\n" (coq_string_to_ocaml s)
  | TCommand s -> Printf.printf "COMMAND:%s\n" (coq_string_to_ocaml s)
  | TMathShift -> Printf.printf "MATHSHIFT\n"
  | TBeginGroup -> Printf.printf "BEGINGROUP\n"
  | TEndGroup -> Printf.printf "ENDGROUP\n"
  | TSpace -> Printf.printf "SPACE\n"
  | TNewline -> Printf.printf "NEWLINE\n"
  | TAlignment -> Printf.printf "ALIGNMENT\n"
  | TSuperscript -> Printf.printf "SUPERSCRIPT\n"
  | TSubscript -> Printf.printf "SUBSCRIPT\n"
  | TComment s -> Printf.printf "COMMENT:%s\n" (coq_string_to_ocaml s)
  | TVerbatim s -> Printf.printf "VERBATIM:%s\n" (coq_string_to_ocaml s)
  | TEOF -> Printf.printf "EOF\n"
  | TParameter n -> Printf.printf "PARAMETER:0\n";;

let rec write_tokens = function
  | Nil -> ()
  | Cons (token, rest) -> 
    write_token_simple token;
    write_tokens rest;;

(* Read input file and tokenize *)
let () =
  let input_file = Sys.argv.(1) in
  let ic = open_in input_file in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  
  let coq_input = ocaml_string_to_coq content in
  let tokens = latex_tokenize coq_input in
  write_tokens tokens;;
