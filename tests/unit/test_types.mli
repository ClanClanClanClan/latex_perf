
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val app : 'a1 list -> 'a1 list -> 'a1 list

module Nat :
 sig
  val pred : int -> int

  val ltb : int -> int -> bool
 end

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val find : ('a1 -> bool) -> 'a1 list -> 'a1 option

val eqb : char list -> char list -> bool

val append : char list -> char list -> char list

val length : char list -> int

val prefix : char list -> char list -> bool

type validation_issue = { rule_id : char list; issue_severity : severity;
                          message : char list; loc : (int * int) option;
                          suggested_fix : char list option;
                          rule_owner : char list }

type document_state = { tokens : latex_token list;
                        expanded_tokens : latex_token list option;
                        ast : char list option; semantics : char list option;
                        filename : char list; doc_layer : layer }

val get_expanded_tokens : document_state -> latex_token list

val is_expanded : document_state -> bool

type env_entry =
| EnvBegin of char list * int
| EnvEnd of char list * int

type semantic_context = { env_stack : env_entry list; math_mode : bool;
                          current_line : int;
                          packages_loaded : char list list;
                          labels_defined : char list list;
                          refs_used : char list list; figures_count : 
                          int; tables_count : int; equations_count : 
                          int }

val init_context : semantic_context

val string_contains_substring : char list -> char list -> bool

val update_context : semantic_context -> latex_token -> semantic_context

val build_context : latex_token list -> semantic_context -> semantic_context

val check_brace_balance : latex_token list -> int -> bool

val delim_001_validator_real : document_state -> validation_issue list

val check_extra_closing : latex_token list -> int -> bool

val delim_002_validator_real : document_state -> validation_issue list

val check_left_right_pairs : latex_token list -> int -> bool

val delim_003_validator_real : document_state -> validation_issue list

val check_math_commands_misplaced :
  latex_token list -> bool -> char list list -> validation_issue list

val math_009_validator_real : document_state -> validation_issue list

val extract_ref_labels : latex_token list -> char list list

val ref_001_validator_real : document_state -> validation_issue list

val check_subscripts : latex_token list -> validation_issue list

val script_001_validator_real : document_state -> validation_issue list

val cmd_001_validator_real : document_state -> validation_issue list

val math_010_validator_real : document_state -> validation_issue list

val check_multi_letter_functions :
  latex_token list -> char list list -> validation_issue list

val math_012_validator_real : document_state -> validation_issue list

val math_015_validator_real : document_state -> validation_issue list

val check_nested_subscripts : latex_token list -> validation_issue list

val math_016_validator_real : document_state -> validation_issue list

val math_018_validator_real : document_state -> validation_issue list

val extract_labels : latex_token list -> char list list

val find_duplicates :
  char list list -> char list list -> validation_issue list

val ref_002_validator_real : document_state -> validation_issue list

val check_label_format : latex_token list -> validation_issue list

val ref_003_validator_real : document_state -> validation_issue list

val check_right_without_left :
  latex_token list -> int -> validation_issue list

val delim_004_validator_real : document_state -> validation_issue list

val check_angle_brackets : latex_token list -> int -> validation_issue list

val delim_007_validator_real : document_state -> validation_issue list

val check_empty_left_right : latex_token list -> validation_issue list

val delim_008_validator_real : document_state -> validation_issue list
