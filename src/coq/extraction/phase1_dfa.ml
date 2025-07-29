
type ('a, 'b) prod =
| Pair of 'a * 'b



type sumbool =
| Left
| Right

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  if b1 then if b2 then Left else Right else if b2 then Right else Left

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb n0 m =
    match n0 with
    | 0 -> (match m with
            | 0 -> true
            | succ _ -> false)
    | succ n' -> (match m with
                  | 0 -> false
                  | succ m' -> eqb n' m')
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

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat = function
  | 0 -> XH
  | succ x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val of_nat : int -> n **)

  let of_nat = function
  | 0 -> N0
  | succ n' -> Npos (Pos.of_succ_nat n')
 end

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> if f a then true else existsb f l0

(** val zero : char **)

let zero =
  '\000'

(** val one : char **)

let one =
  '\001'

(** val shift : bool -> char -> char **)

let shift c a =
  ascii_to_bool_list
    (fun a1 a2 a3 a4 a5 a6 a7 _ -> ascii_of_bool_list (c, a1, a2, a3, a4, a5,
    a6, a7))
    a

(** val ascii_dec : char -> char -> sumbool **)

let ascii_dec a b =
  ascii_to_bool_list
    (fun b0 b1 b2 b3 b4 b5 b6 b7 ->
    ascii_to_bool_list
      (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
      match bool_dec b0 b8 with
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
      b)
    a

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | 0 -> zero
    | succ n' ->
      (match p with
       | XI p' -> shift true (loop n' p')
       | XO p' -> shift false (loop n' p')
       | XH -> one)
  in loop (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

type rule_id = int

type document = string

type position = int

type error_message = string

type validation_result = ((rule_id, position) prod, error_message) prod list

type rule_category =
| CategoryA
| CategoryB
| CategoryC

type rule_pattern =
| CharPattern of char
| StringPattern of string
| RegexPattern of string
| BalancedPattern of char * char
| ContextPattern of string

type rule = { rule_identifier : rule_id; rule_name : string;
              rule_cat : rule_category; rule_pat : rule_pattern;
              rule_message : error_message; rule_enabled : bool }

type regex =
| Empty
| Char of char
| Alt of regex * regex
| Seq of regex * regex
| Star of regex

type input_string = string

type state = int

type transition_func = state -> char -> state

type dfa = { states : state list; start_state : state;
             accept_states : state list; transition : transition_func }

(** val run_dfa_helper : dfa -> state -> input_string -> state **)

let rec run_dfa_helper d current_state = function
| emptystring -> current_state
| string (c, rest) ->
  let next_state = d.transition current_state c in
  run_dfa_helper d next_state rest

(** val run_dfa : dfa -> input_string -> bool **)

let run_dfa d input =
  let final_state = run_dfa_helper d d.start_state input in
  existsb (Nat.eqb final_state) d.accept_states

(** val ascii_eqb : char -> char -> bool **)

let ascii_eqb a1 a2 =
  match ascii_dec a1 a2 with
  | Left -> true
  | Right -> false

(** val compile_regex : regex -> dfa **)

let compile_regex = function
| Empty ->
  { states = (0::[]); start_state = 0; accept_states = (0::[]); transition =
    (fun s _ -> s) }
| Char c ->
  { states = (0::((succ 0)::((succ (succ 0))::[]))); start_state = 0;
    accept_states = ((succ 0)::[]); transition = (fun s ch ->
    match s with
    | 0 -> if ascii_eqb ch c then succ 0 else succ (succ 0)
    | succ _ -> succ (succ 0)) }
| _ ->
  { states = (0::[]); start_state = 0; accept_states = []; transition =
    (fun s _ -> s) }

(** val backslash_char : char **)

let backslash_char =
  ascii_of_nat (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val backslash_rule : regex **)

let backslash_rule =
  Char backslash_char

(** val backslash_dfa : dfa **)

let backslash_dfa =
  compile_regex backslash_rule

(** val vnv2_single_rule_validator : input_string -> bool **)

let vnv2_single_rule_validator input =
  run_dfa backslash_dfa input

(** val compile_phase1 : rule list -> dfa **)

let compile_phase1 =
  failwith "AXIOM TO BE REALIZED (Compiler.compile_phase1)"

(** val validate_phase1 : dfa -> document -> validation_result **)

let validate_phase1 =
  failwith "AXIOM TO BE REALIZED (Compiler.validate_phase1)"
