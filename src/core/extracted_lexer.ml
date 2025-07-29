
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

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

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> true
    | S n' -> (match m with
               | O -> false
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
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | O -> zero
    | S n' ->
      (match p with
       | XI p' -> shift true (loop n' p')
       | XO p' -> shift false (loop n' p')
       | XH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b :: l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val length : char list -> nat **)

let rec length = function
| [] -> O
| _::s' -> S (length s')

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
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_lbrace : char **)

let ascii_lbrace =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_rbrace : char **)

let ascii_rbrace =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_dollar : char **)

let ascii_dollar =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))

(** val ascii_ampersand : char **)

let ascii_ampersand =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))

(** val ascii_hash : char **)

let ascii_hash =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))

(** val ascii_caret : char **)

let ascii_caret =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_underscore : char **)

let ascii_underscore =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_space : char **)

let ascii_space =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))

(** val ascii_percent : char **)

let ascii_percent =
  ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))

(** val is_letter : char -> bool **)

let is_letter c =
  let n0 = nat_of_ascii c in
  (||)
    ((&&)
      (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n0)
      (Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((&&)
      (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n0)
      (Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val default_catcodes : catcode_table **)

let default_catcodes c =
  if (=) c ascii_backslash
  then CatEscape
  else if (=) c ascii_lbrace
       then CatBeginGroup
       else if (=) c ascii_rbrace
            then CatEndGroup
            else if (=) c ascii_dollar
                 then CatMathShift
                 else if (=) c ascii_ampersand
                      then CatAlignment
                      else if (=) c ascii_hash
                           then CatParameter
                           else if (=) c ascii_caret
                                then CatSuperscript
                                else if (=) c ascii_underscore
                                     then CatSubscript
                                     else if (=) c ascii_space
                                          then CatSpace
                                          else if (=) c ascii_percent
                                               then CatComment
                                               else if is_letter c
                                                    then CatLetter
                                                    else CatOther

type latex_token =
| TCommand of char list
| TBeginGroup
| TEndGroup
| TMathShift
| TAlignment
| TParameter
| TSuperscript
| TSubscript
| TText of char list
| TSpace
| TComment of char list
| TNewline
| TEOF

type lexer_state = { input : char list; position : nat;
                     tokens : latex_token list; line_number : nat;
                     column_number : nat }

(** val initial_state : char list -> lexer_state **)

let initial_state s =
  { input = s; position = O; tokens = []; line_number = (S O);
    column_number = (S O) }

(** val peek_char : lexer_state -> char option **)

let peek_char st =
  match st.input with
  | [] -> None
  | c::_ -> Some c

(** val advance_char : lexer_state -> lexer_state **)

let advance_char st =
  match st.input with
  | [] -> st
  | c::rest ->
    let new_column =
      if (=) c (ascii_of_nat (S (S (S (S (S (S (S (S (S (S O)))))))))))
      then S O
      else S st.column_number
    in
    let new_line =
      if (=) c (ascii_of_nat (S (S (S (S (S (S (S (S (S (S O)))))))))))
      then S st.line_number
      else st.line_number
    in
    { input = rest; position = (S st.position); tokens = st.tokens;
    line_number = new_line; column_number = new_column }

(** val add_token : latex_token -> lexer_state -> lexer_state **)

let add_token tok st =
  { input = st.input; position = st.position; tokens = (tok :: st.tokens);
    line_number = st.line_number; column_number = st.column_number }

(** val take_while : (char -> bool) -> char list -> char list * char list **)

let rec take_while f s = match s with
| [] -> ([], [])
| c::rest ->
  if f c
  then let (taken, remaining) = take_while f rest in ((c::taken), remaining)
  else ([], s)

(** val is_command_char : char -> bool **)

let is_command_char =
  is_letter

(** val is_whitespace : char -> bool **)

let is_whitespace c =
  let n0 = nat_of_ascii c in
  (||)
    ((||)
      (Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
      (Nat.eqb n0 (S (S (S (S (S (S (S (S (S O)))))))))))
    ((||) (Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S O)))))))))))
      (Nat.eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

(** val is_text_char : char -> bool **)

let is_text_char c =
  (||) (is_letter c)
    (let n0 = nat_of_ascii c in
     (&&)
       (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))) n0)
       (Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val lex_command : lexer_state -> latex_token * lexer_state **)

let lex_command st =
  match st.input with
  | [] -> (TEOF, st)
  | backslash::_ ->
    if (=) backslash ascii_backslash
    then let st' = advance_char st in
         let (cmd_name, remaining) = take_while is_command_char st'.input in
         (match remaining with
          | [] ->
            let final_st = { input = remaining; position =
              (add st'.position (length cmd_name)); tokens = st'.tokens;
              line_number = st'.line_number; column_number =
              (add st'.column_number (length cmd_name)) }
            in
            ((TCommand cmd_name), final_st)
          | star::rest' ->
            if (=) star
                 (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S
                   O)))))))))))))))))))))))))))))))))))))))))))
            then let final_name = append cmd_name ('*'::[]) in
                 let final_st = { input = rest'; position =
                   (add st'.position (length final_name)); tokens =
                   st'.tokens; line_number = st'.line_number; column_number =
                   (add st'.column_number (length final_name)) }
                 in
                 ((TCommand final_name), final_st)
            else let final_st = { input = remaining; position =
                   (add st'.position (length cmd_name)); tokens = st'.tokens;
                   line_number = st'.line_number; column_number =
                   (add st'.column_number (length cmd_name)) }
                 in
                 ((TCommand cmd_name), final_st))
    else (TEOF, st)

(** val lex_whitespace : lexer_state -> latex_token * lexer_state **)

let lex_whitespace st =
  let (spaces, remaining) = take_while is_whitespace st.input in
  let final_st = { input = remaining; position =
    (add st.position (length spaces)); tokens = st.tokens; line_number =
    st.line_number; column_number = (add st.column_number (length spaces)) }
  in
  (TSpace, final_st)

(** val lex_comment : lexer_state -> latex_token * lexer_state **)

let lex_comment st =
  match st.input with
  | [] -> (TEOF, st)
  | percent::_ ->
    if (=) percent ascii_percent
    then let st' = advance_char st in
         let (comment_text, remaining) =
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
         ((TComment comment_text), final_st)
    else (TEOF, st)

(** val lex_text : lexer_state -> latex_token * lexer_state **)

let lex_text st =
  match peek_char st with
  | Some c ->
    if is_text_char c
    then let (text, remaining) = take_while is_text_char st.input in
         let final_st = { input = remaining; position =
           (add st.position (length text)); tokens = st.tokens; line_number =
           st.line_number; column_number =
           (add st.column_number (length text)) }
         in
         ((TText text), final_st)
    else let st' = advance_char st in ((TText (c::[])), st')
  | None -> (TEOF, st)

(** val lex_step : lexer_state -> (latex_token * lexer_state) option **)

let lex_step st =
  match peek_char st with
  | Some c ->
    (match default_catcodes c with
     | CatEscape -> Some (lex_command st)
     | CatBeginGroup -> let st' = advance_char st in Some (TBeginGroup, st')
     | CatEndGroup -> let st' = advance_char st in Some (TEndGroup, st')
     | CatMathShift -> let st' = advance_char st in Some (TMathShift, st')
     | CatAlignment -> let st' = advance_char st in Some (TAlignment, st')
     | CatParameter -> let st' = advance_char st in Some (TParameter, st')
     | CatSuperscript -> let st' = advance_char st in Some (TSuperscript, st')
     | CatSubscript -> let st' = advance_char st in Some (TSubscript, st')
     | CatSpace -> Some (lex_whitespace st)
     | CatComment -> Some (lex_comment st)
     | _ -> Some (lex_text st))
  | None -> None

(** val lex_all_steps : lexer_state -> nat -> latex_token list **)

let rec lex_all_steps st = function
| O -> rev st.tokens
| S n0 ->
  (match lex_step st with
   | Some p -> let (tok, st') = p in lex_all_steps (add_token tok st') n0
   | None -> rev st.tokens)

(** val lex_string : char list -> latex_token list **)

let lex_string s =
  let fuel = mul (S (S O)) (length s) in lex_all_steps (initial_state s) fuel

(** val list_ascii_to_string : char list -> char list **)

let rec list_ascii_to_string = function
| [] -> []
| c :: rest -> c::(list_ascii_to_string rest)

(** val lex : char list -> latex_token list **)

let lex chars =
  let s = list_ascii_to_string chars in lex_string s

(** val lex_from_string : char list -> latex_token list **)

let lex_from_string =
  lex_string
