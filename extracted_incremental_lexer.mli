
type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

module Nat :
 sig
  val leb : nat -> nat -> bool
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

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module N :
 sig
  val add : n -> n -> n

  val mul : n -> n -> n

  val to_nat : n -> nat

  val of_nat : nat -> n
 end

val rev : 'a1 list -> 'a1 list

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : positive -> char

val ascii_of_N : n -> char

val ascii_of_nat : nat -> char

val n_of_digits : bool list -> n

val n_of_ascii : char -> n

val nat_of_ascii : char -> nat

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

val ascii_backslash : char

val ascii_lbrace : char

val ascii_rbrace : char

val ascii_dollar : char

val ascii_ampersand : char

val ascii_hash : char

val ascii_caret : char

val ascii_underscore : char

val ascii_space : char

val ascii_percent : char

val is_letter : char -> bool

val default_catcodes : catcode_table

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

type checkpoint_state = { cp_position : nat; cp_tokens : latex_token list;
                          cp_line : nat; cp_column : nat;
                          cp_catcodes : (char -> catcode); cp_in_math : 
                          bool; cp_env_stack : char list list }

val checkpoint_interval : nat

val create_checkpoint :
  lexer_state -> bool -> char list list -> checkpoint_state

val incremental_lex : char list -> char list -> char list -> char list
