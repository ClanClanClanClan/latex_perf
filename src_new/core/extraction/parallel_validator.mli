
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val pred : int -> int

val add : int -> int -> int

val sub : int -> int -> int

val leb : int -> int -> bool

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : uint -> int -> int

val of_uint : uint -> int

val of_hex_uint_acc : uint0 -> int -> int

val of_hex_uint : uint0 -> int

val of_num_uint : uint1 -> int

val divmod : int -> int -> int -> int -> int * int

val div : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Nat :
 sig
  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_succ_nat : int -> positive
 end

module N :
 sig
  val add : n -> n -> n

  val mul : n -> n -> n

  val to_nat : n -> int

  val of_nat : int -> n
 end

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : positive -> char

val ascii_of_N : n -> char

val ascii_of_nat : int -> char

val n_of_digits : bool list -> n

val n_of_ascii : char -> n

val nat_of_ascii : char -> int

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val string_dec : char list -> char list -> bool

val length0 : char list -> int

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

type layer =
| L0_Lexer
| L1_Expanded
| L2_Ast
| L3_Semantics
| L4_Style

type severity =
| Error
| Warning
| Info

type maturity =
| Draft
| Stable
| Proven

type bucket =
| TokenKind_Text
| TokenKind_Command
| TokenKind_MathShift
| TokenKind_BeginGroup
| TokenKind_EndGroup
| TokenKind_Other

type location = { line : int; column : int; file : char list option }

type validation_issue = { rule_id : char list; issue_severity : severity;
                          message : char list; loc : location option;
                          suggested_fix : char list option;
                          rule_owner : char list }

type document_state = { tokens : latex_token list;
                        expanded_tokens : latex_token list option;
                        ast : char list option; semantics : char list option;
                        filename : char list; doc_layer : layer }

type soundness_proof =
  char list
  (* singleton inductive, whose constructor was ProofRef *)

type validation_rule = { id : char list; description : char list;
                         precondition : layer; default_severity : severity;
                         rule_maturity : maturity; owner : char list;
                         performance_bucket : bucket;
                         auto_fix : char list option;
                         implementation_file : char list;
                         validator : (document_state -> validation_issue list);
                         rule_sound : soundness_proof option }

val rule_applicable : validation_rule -> document_state -> bool

val execute_rule : validation_rule -> document_state -> validation_issue list

val execute_rules :
  validation_rule list -> document_state -> validation_issue list

val bucket_eq : bucket -> bucket -> bool

val execute_rules_bucketed :
  validation_rule list -> document_state -> validation_issue list

val string_contains : char list -> char -> bool

val string_prefix : char list -> char list -> bool

val string_contains_substring : char list -> char list -> bool

val count_char : char list -> char -> int

val string_ends_with_spaces : char list -> bool

val string_eqb : char list -> char list -> bool

val typo_001_check : char list -> bool

val typo_001_validator : document_state -> validation_issue list

val typo_001_rule : validation_rule

val typo_002_check : char list -> bool

val typo_002_validator : document_state -> validation_issue list

val typo_002_rule : validation_rule

val typo_003_check : char list -> bool

val typo_003_validator : document_state -> validation_issue list

val typo_003_rule : validation_rule

val typo_004_check : char list -> bool

val typo_004_validator : document_state -> validation_issue list

val typo_004_rule : validation_rule

val typo_005_check : char list -> bool

val typo_005_validator : document_state -> validation_issue list

val typo_005_rule : validation_rule

val typo_006_check : char list -> bool

val typo_006_validator : document_state -> validation_issue list

val typo_006_rule : validation_rule

val typo_007_check : char list -> bool

val typo_007_validator : document_state -> validation_issue list

val typo_007_rule : validation_rule

val typo_008_check : char list -> bool

val typo_008_validator : document_state -> validation_issue list

val typo_008_rule : validation_rule

val typo_009_check : char list -> bool

val typo_009_validator : document_state -> validation_issue list

val typo_009_rule : validation_rule

val typo_010_check : char list -> bool

val typo_010_validator : document_state -> validation_issue list

val typo_010_rule : validation_rule

val typo_011_check : char list -> bool

val typo_011_validator : document_state -> validation_issue list

val typo_011_rule : validation_rule

val typo_012_check : char list -> bool

val typo_012_validator : document_state -> validation_issue list

val typo_012_rule : validation_rule

val typo_013_check : char list -> bool

val typo_013_validator : document_state -> validation_issue list

val typo_013_rule : validation_rule

val typo_014_check : char list -> bool

val typo_014_validator : document_state -> validation_issue list

val typo_014_rule : validation_rule

val typo_015_check : char list -> bool

val typo_015_validator : document_state -> validation_issue list

val typo_015_rule : validation_rule

val typo_016_check : char list -> bool

val typo_016_validator : document_state -> validation_issue list

val typo_016_rule : validation_rule

val typo_017_check : char list -> bool

val typo_017_validator : document_state -> validation_issue list

val typo_017_rule : validation_rule

val typo_018_check : char list -> bool

val typo_018_validator : document_state -> validation_issue list

val typo_018_rule : validation_rule

val typo_019_check : char list -> bool

val typo_019_validator : document_state -> validation_issue list

val typo_019_rule : validation_rule

val typo_020_check : char list -> bool

val typo_020_validator : document_state -> validation_issue list

val typo_020_rule : validation_rule

val typo_021_check : char list -> bool

val typo_021_validator : document_state -> validation_issue list

val typo_021_rule : validation_rule

val typo_022_check : char list -> bool

val typo_022_validator : document_state -> validation_issue list

val typo_022_rule : validation_rule

val typo_023_check : char list -> bool

val typo_023_validator : document_state -> validation_issue list

val typo_023_rule : validation_rule

val typo_024_check : char list -> bool

val typo_024_validator : document_state -> validation_issue list

val typo_024_rule : validation_rule

val typo_025_check : char list -> bool

val typo_025_validator : document_state -> validation_issue list

val typo_025_rule : validation_rule

val enc_001_check : char list -> bool

val enc_001_validator : document_state -> validation_issue list

val enc_001_rule : validation_rule

val enc_002_check : char list -> bool

val enc_002_validator : document_state -> validation_issue list

val enc_002_rule : validation_rule

val enc_003_check : char list -> bool

val enc_003_validator : document_state -> validation_issue list

val enc_003_rule : validation_rule

val enc_004_check : char list -> bool

val enc_004_validator : document_state -> validation_issue list

val enc_004_rule : validation_rule

val enc_005_check : char list -> bool

val enc_005_validator : document_state -> validation_issue list

val enc_005_rule : validation_rule

val char_001_check : char list -> bool

val char_001_validator : document_state -> validation_issue list

val char_001_rule : validation_rule

val char_002_check : char list -> bool

val char_002_validator : document_state -> validation_issue list

val char_002_rule : validation_rule

val char_003_check_chars : char list -> bool

val char_003_check : char list -> bool

val char_003_validator : document_state -> validation_issue list

val char_003_rule : validation_rule

val char_004_check : char list -> bool

val char_004_validator : document_state -> validation_issue list

val char_004_rule : validation_rule

val char_005_check : char list -> bool

val char_005_validator : document_state -> validation_issue list

val char_005_rule : validation_rule

val env_001_check_aux : char list -> bool

val env_001_check : latex_token list -> bool

val env_001_validator : document_state -> validation_issue list

val env_001_rule : validation_rule

val env_002_check_aux : char list -> bool

val env_002_check : latex_token list -> bool

val env_002_validator : document_state -> validation_issue list

val env_002_rule : validation_rule

val env_003_check : latex_token list -> bool

val env_003_validator : document_state -> validation_issue list

val env_003_rule : validation_rule

val env_004_count_nesting : latex_token list -> int -> int -> int

val env_004_check : latex_token list -> bool

val env_004_validator : document_state -> validation_issue list

val env_004_rule : validation_rule

val env_005_check_aux : char list -> bool

val env_005_check : latex_token list -> bool

val env_005_validator : document_state -> validation_issue list

val env_005_rule : validation_rule

val math_001_check : char list -> bool

val math_001_validator : document_state -> validation_issue list

val math_001_rule : validation_rule

val math_002_count_delimiters : latex_token list -> int -> bool

val math_002_validator : document_state -> validation_issue list

val math_002_rule : validation_rule

val math_003_check : char list -> bool

val math_003_validator : document_state -> validation_issue list

val math_003_rule : validation_rule

val math_004_check : char list -> bool

val math_004_validator : document_state -> validation_issue list

val math_004_rule : validation_rule

val math_005_check : char list -> bool

val math_005_validator : document_state -> validation_issue list

val math_005_rule : validation_rule

val struct_001_check_aux : char list -> bool

val struct_001_check : latex_token list -> bool

val struct_001_validator : document_state -> validation_issue list

val struct_001_rule : validation_rule

val struct_002_check : latex_token list -> bool

val struct_002_validator : document_state -> validation_issue list

val struct_002_rule : validation_rule

val struct_003_count_documentclass : latex_token list -> int -> int

val struct_003_check : latex_token list -> bool

val struct_003_validator : document_state -> validation_issue list

val struct_003_rule : validation_rule

val struct_004_check_order : latex_token list -> bool -> bool

val struct_004_check : latex_token list -> bool

val struct_004_validator : document_state -> validation_issue list

val struct_004_rule : validation_rule

val struct_005_check : latex_token list -> bool

val struct_005_validator : document_state -> validation_issue list

val struct_005_rule : validation_rule

val struct_006_check : latex_token list -> bool

val struct_006_validator : document_state -> validation_issue list

val struct_006_rule : validation_rule

val struct_007_check_packages : latex_token list -> bool -> bool

val struct_007_check : latex_token list -> bool

val struct_007_validator : document_state -> validation_issue list

val struct_007_rule : validation_rule

val struct_008_count_braces : latex_token list -> int -> int -> int * int

val struct_008_check : latex_token list -> bool

val struct_008_validator : document_state -> validation_issue list

val struct_008_rule : validation_rule

val struct_009_count_consecutive_newlines :
  latex_token list -> int -> int -> int

val struct_009_check : latex_token list -> bool

val struct_009_validator : document_state -> validation_issue list

val struct_009_rule : validation_rule

val struct_010_check_text_before_class : latex_token list -> bool

val struct_010_validator : document_state -> validation_issue list

val struct_010_rule : validation_rule

val ref_001_check_aux : char list -> bool

val ref_001_check : latex_token list -> bool

val ref_001_validator : document_state -> validation_issue list

val ref_001_rule : validation_rule

val ref_002_check_labels : latex_token list -> bool -> bool

val ref_002_check : latex_token list -> bool

val ref_002_validator : document_state -> validation_issue list

val ref_002_rule : validation_rule

val ref_003_has_cite : latex_token list -> bool

val ref_003_has_bibliography : latex_token list -> bool

val ref_003_check : latex_token list -> bool

val ref_003_validator : document_state -> validation_issue list

val ref_003_rule : validation_rule

val ref_004_check : latex_token list -> bool

val ref_004_validator : document_state -> validation_issue list

val ref_004_rule : validation_rule

val ref_005_check_aux : char list -> bool

val ref_005_check : latex_token list -> bool

val ref_005_validator : document_state -> validation_issue list

val ref_005_rule : validation_rule

val ref_006_check_equation_refs : latex_token list -> bool

val ref_006_validator : document_state -> validation_issue list

val ref_006_rule : validation_rule

val ref_007_count_ref_styles : latex_token list -> int -> int -> int * int

val ref_007_check : latex_token list -> bool

val ref_007_validator : document_state -> validation_issue list

val ref_007_rule : validation_rule

val ref_008_check_footnotes : latex_token list -> bool -> bool

val ref_008_check : latex_token list -> bool

val ref_008_validator : document_state -> validation_issue list

val ref_008_rule : validation_rule

val ref_009_has_url : latex_token list -> bool

val ref_009_has_hyperref : latex_token list -> bool

val ref_009_check : latex_token list -> bool

val ref_009_validator : document_state -> validation_issue list

val ref_009_rule : validation_rule

val ref_010_check_bibstyle : latex_token list -> bool

val ref_010_validator : document_state -> validation_issue list

val ref_010_rule : validation_rule

val style_001_check : char list -> bool

val style_001_validator : document_state -> validation_issue list

val style_001_rule : validation_rule

val style_002_check : char list -> bool

val style_002_validator : document_state -> validation_issue list

val style_002_rule : validation_rule

val style_003_check : char list -> bool

val style_003_validator : document_state -> validation_issue list

val style_003_rule : validation_rule

val style_004_check : char list -> bool

val style_004_validator : document_state -> validation_issue list

val style_004_rule : validation_rule

val style_005_has_frac : latex_token list -> bool

val style_005_has_tfrac : latex_token list -> bool

val style_005_check : latex_token list -> bool

val style_005_validator : document_state -> validation_issue list

val style_005_rule : validation_rule

val style_006_check_line_length : char list -> bool

val style_006_validator : document_state -> validation_issue list

val style_006_rule : validation_rule

val style_007_count_brackets : latex_token list -> int -> int -> int * int

val style_007_check : latex_token list -> bool

val style_007_validator : document_state -> validation_issue list

val style_007_rule : validation_rule

val style_008_has_itemize : latex_token list -> bool

val style_008_has_enumerate : latex_token list -> bool

val style_008_check : latex_token list -> bool

val style_008_validator : document_state -> validation_issue list

val style_008_rule : validation_rule

val style_009_has_emph : latex_token list -> bool

val style_009_has_textit : latex_token list -> bool

val style_009_check : latex_token list -> bool

val style_009_validator : document_state -> validation_issue list

val style_009_rule : validation_rule

val style_010_check : char list -> bool

val style_010_validator : document_state -> validation_issue list

val style_010_rule : validation_rule

val all_l0_rules : validation_rule list

type rule_chunk = validation_rule list

val combine_results : validation_issue list list -> validation_issue list

val execute_chunk : rule_chunk -> document_state -> validation_issue list

val create_chunks_helper :
  validation_rule list -> int -> int -> rule_chunk list

val create_chunks : validation_rule list -> int -> rule_chunk list

val optimal_chunk_size : validation_rule list -> int -> int

val parallel_execute_spec :
  validation_rule list -> document_state -> int -> validation_issue list

type rule_priority =
| HighPriority
| MediumPriority
| LowPriority

val get_rule_priority : validation_rule -> rule_priority

val filter_by_priority :
  validation_rule list -> rule_priority -> validation_rule list

val parallel_execute_prioritized :
  validation_rule list -> document_state -> int -> validation_issue list

val execute_rules_early_termination :
  validation_rule list -> document_state -> int -> validation_issue list

val parallel_execute_early_termination :
  validation_rule list -> document_state -> int -> int -> validation_issue
  list

val balance_chunks : validation_rule list -> int -> rule_chunk list

val enterprise_parallel_execute :
  validation_rule list -> document_state -> int -> int -> validation_issue
  list

val all_parallel_functions :
  ((((((((validation_rule list -> document_state -> int -> validation_issue
  list) * (validation_rule list -> document_state -> int -> validation_issue
  list)) * (validation_rule list -> document_state -> int -> int ->
  validation_issue list)) * (validation_rule list -> document_state -> int ->
  int -> validation_issue list)) * (validation_rule list -> int -> rule_chunk
  list)) * (validation_rule list -> int -> int)) * (validation_rule list ->
  int -> rule_chunk list)) * (rule_chunk -> document_state ->
  validation_issue list)) * (validation_issue list list -> validation_issue
  list)

val parallel_all_l0_rules : validation_rule list

val estimate_parallel_speedup : validation_rule list -> int -> int
