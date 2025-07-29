
type bool =
| True
| False

val negb : bool -> bool

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

val app : 'a1 list -> 'a1 list -> 'a1 list

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val max : nat -> nat -> nat

val min : nat -> nat -> nat

val bool_dec : bool -> bool -> sumbool

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
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

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val zero : ascii

val one : ascii

val shift : bool -> ascii -> ascii

val ascii_dec : ascii -> ascii -> sumbool

val ascii_of_pos : positive -> ascii

val ascii_of_N : n -> ascii

val ascii_of_nat : nat -> ascii

val n_of_digits : bool list -> n

val n_of_ascii : ascii -> n

val nat_of_ascii : ascii -> nat

type string =
| EmptyString
| String of ascii * string

val append : string -> string -> string

val length : string -> nat

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

val ascii_backslash : ascii

val ascii_lbrace : ascii

val ascii_rbrace : ascii

val ascii_dollar : ascii

val ascii_ampersand : ascii

val ascii_hash : ascii

val ascii_caret : ascii

val ascii_underscore : ascii

val ascii_space : ascii

val ascii_percent : ascii

val is_letter : ascii -> bool

val default_catcodes : catcode_table

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

val initial_state : string -> lexer_state

val peek_char : lexer_state -> ascii option

val advance_char : lexer_state -> lexer_state

val add_token : latex_token -> lexer_state -> lexer_state

val take_while : (ascii -> bool) -> string -> (string, string) prod

val is_command_char : ascii -> bool

val is_whitespace : ascii -> bool

val is_text_char : ascii -> bool

val lex_command : lexer_state -> (latex_token, lexer_state) prod

val lex_whitespace : lexer_state -> (latex_token, lexer_state) prod

val lex_comment : lexer_state -> (latex_token, lexer_state) prod

val lex_text : lexer_state -> (latex_token, lexer_state) prod

val lex_step : lexer_state -> (latex_token, lexer_state) prod option

val lex_all_steps : lexer_state -> nat -> latex_token list

val lex_string : string -> latex_token list

val lex_from_string : string -> latex_token list

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

val checkpoint_interval : nat

val create_checkpoint : lexer_state -> bool -> string list -> checkpoint_state

val string_skip : nat -> string -> string

val find_checkpoint_before :
  nat -> checkpoint_state list -> checkpoint_state option

val string_take : nat -> string -> string

val string_substring : nat -> nat -> string -> string

val apply_edit_to_string : string -> edit_operation -> string

val lex_incremental :
  string -> checkpoint_state list -> edit_operation -> incremental_result

type checkpoint_lexer_state = { cl_base : lexer_state;
                                cl_checkpoints : checkpoint_state list;
                                cl_last_checkpoint : nat; cl_in_math : 
                                bool; cl_env_stack : string list }

val checkpoint_lex_step :
  checkpoint_lexer_state -> (latex_token, checkpoint_lexer_state) prod option

val lex_with_checkpoints_fuel :
  checkpoint_lexer_state -> nat -> (latex_token list, checkpoint_state list)
  prod

val lex_document_with_checkpoints :
  string -> (latex_token list, checkpoint_state list) prod
