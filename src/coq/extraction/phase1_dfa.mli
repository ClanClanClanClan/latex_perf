
type ('a, 'b) prod =
| Pair of 'a * 'b



type sumbool =
| Left
| Right

val bool_dec : bool -> bool -> sumbool

module Nat :
 sig
  val eqb : int -> int -> bool
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos :
 sig
  val succ : positive -> positive

  val of_succ_nat : int -> positive
 end

module N :
 sig
  val of_nat : int -> n
 end

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_dec : char -> char -> sumbool

val ascii_of_pos : positive -> char

val ascii_of_N : n -> char

val ascii_of_nat : int -> char

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

val run_dfa_helper : dfa -> state -> input_string -> state

val run_dfa : dfa -> input_string -> bool

val ascii_eqb : char -> char -> bool

val compile_regex : regex -> dfa

val backslash_char : char

val backslash_rule : regex

val backslash_dfa : dfa

val vnv2_single_rule_validator : input_string -> bool

val compile_phase1 : rule list -> dfa

val validate_phase1 : dfa -> document -> validation_result
