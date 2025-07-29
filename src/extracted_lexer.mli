
val negb : bool -> bool

type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

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

val append : char list -> char list -> char list

val length : char list -> nat

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

val initial_state : char list -> lexer_state

val peek_char : lexer_state -> char option

val advance_char : lexer_state -> lexer_state

val add_token : latex_token -> lexer_state -> lexer_state

val take_while : (char -> bool) -> char list -> char list * char list

val is_command_char : char -> bool

val is_whitespace : char -> bool

val is_text_char : char -> bool

val lex_command : lexer_state -> latex_token * lexer_state

val lex_whitespace : lexer_state -> latex_token * lexer_state

val lex_comment : lexer_state -> latex_token * lexer_state

val lex_text : lexer_state -> latex_token * lexer_state

val lex_step : lexer_state -> (latex_token * lexer_state) option

val lex_all_steps : lexer_state -> nat -> latex_token list

val lex_string : char list -> latex_token list

val list_ascii_to_string : char list -> char list

val lex : char list -> latex_token list

val lex_from_string : char list -> latex_token list
