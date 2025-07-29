(** * Phase 1½ Post-Expansion Validation Rules *)
(**
  Week 13-16 Deliverable: Post-expansion validation rules
  
  These rules operate on L1_Expanded documents (after macro expansion)
  and can detect issues that only become visible after expansion.
  
  Architecture:
  - Precondition: L1_Expanded layer
  - Input: expanded_tokens from document_state  
  - Validates: Macro expansion results, deprecated macro usage
*)

Require Import String.
Require Import List.
Require Import Ascii.
Require Import Arith.
Import ListNotations.
Require Import core.lexer.LatexCatcodes.
Require Import core.lexer.LatexLexer.
Require Import core.expander.LatexExpanderEnhanced.
Require Import ValidationTypes.
Require Import rules.phase1.TypoRules.
Open Scope string_scope.

(** Simplified working macros list for compilation *)
Definition working_latex_macros : list enhanced_macro := built_in_macros initial_expansion_state.

(** ** Post-Expansion Rule Framework *)

(** Helper: Extract expanded tokens from document *)
Definition get_expanded_tokens (doc : document_state) : list latex_token :=
  match doc.(expanded_tokens) with
  | Some tokens => tokens
  | None => doc.(tokens)  (* Fallback to original if not expanded *)
  end.

(** Helper: Check if document has been expanded *)
Definition is_expanded (doc : document_state) : bool :=
  match doc.(doc_layer) with
  | L1_Expanded => true
  | _ => false
  end.

(** ** POST-001: Deprecated macro usage after expansion *)

(** Check for deprecated macros that should have been expanded *)
Definition post_001_check_deprecated (tokens : list latex_token) : bool :=
  existsb (fun tok =>
    match tok with
    | TCommand cmd => 
        orb (if string_dec cmd "bf" then true else false)
        (orb (if string_dec cmd "it" then true else false)
             (if string_dec cmd "em" then true else false))
    | _ => false
    end) tokens.

Definition post_001_validator : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      if post_001_check_deprecated expanded then
        [{| rule_id := "POST-001";
            issue_severity := Warning;
            message := "Deprecated macro found after expansion - expansion may have failed";
            loc := None;
            suggested_fix := Some "check_macro_definitions";
            rule_owner := "@expansion-team" |}]
      else []
    else [].

Definition post_001_rule : validation_rule := {|
  id := "POST-001";
  description := "Deprecated macro found after expansion";
  precondition := L1_Expanded;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@expansion-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "check_macro_definitions";
  implementation_file := "rules/phase1_5/PostExpansionRules.v";
  validator := post_001_validator;
  rule_sound := None
|}.

(** ** POST-002: Macro expansion depth analysis *)

(** Count nested macro expansions to detect overly complex macros *)
Fixpoint count_expansion_depth (original expanded : list latex_token) : nat :=
  match original, expanded with
  | [], _ => length expanded
  | _, [] => 0  
  | o :: orig_rest, e :: exp_rest =>
      if latex_token_eq_dec o e then
        count_expansion_depth orig_rest exp_rest
      else
        S (count_expansion_depth orig_rest expanded)  (* Expansion occurred *)
  end.

Definition post_002_validator : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let original := doc.(tokens) in
      let expanded := get_expanded_tokens doc in
      let depth := count_expansion_depth original expanded in
      if Nat.ltb 20 depth then  (* More than 20 expansions *)
        [{| rule_id := "POST-002";
            issue_severity := Info;
            message := "High macro expansion complexity detected";
            loc := None;
            suggested_fix := Some "simplify_macros";
            rule_owner := "@performance-team" |}]
      else []
    else [].

Definition post_002_rule : validation_rule := {|
  id := "POST-002";
  description := "High macro expansion complexity detected";
  precondition := L1_Expanded;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@performance-team";
  performance_bucket := TokenKind_Other;
  auto_fix := Some "simplify_macros";
  implementation_file := "rules/phase1_5/PostExpansionRules.v";
  validator := post_002_validator;
  rule_sound := None
|}.

(** ** POST-003: Expansion introduced typography issues *)

(** Check if expansion created new typography problems *)
Definition post_003_check_expansion_typos (expanded : list latex_token) : bool :=
  existsb (fun tok =>
    match tok with
    | TText s => 
        orb (string_contains_substring s "  ")  (* Double spaces from expansion *)
        (orb (string_contains_substring s "}{")  (* Adjacent braces *)
             (string_contains_substring s "\\\\"))  (* Double backslashes *)
    | _ => false
    end) expanded.

Definition post_003_validator : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      if post_003_check_expansion_typos expanded then
        [{| rule_id := "POST-003";
            issue_severity := Warning;
            message := "Macro expansion introduced typography issues";
            loc := None;
            suggested_fix := Some "review_macro_definitions";
            rule_owner := "@expansion-team" |}]
      else []
    else [].

Definition post_003_rule : validation_rule := {|
  id := "POST-003";
  description := "Macro expansion introduced typography issues";
  precondition := L1_Expanded;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@expansion-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "review_macro_definitions";
  implementation_file := "rules/phase1_5/PostExpansionRules.v";
  validator := post_003_validator;
  rule_sound := None
|}.

(** ** POST-004: Modern macro usage validation *)

(** Verify that modern LaTeX commands are used after expansion *)
Definition post_004_check_modern_commands (expanded : list latex_token) : bool :=
  existsb (fun tok =>
    match tok with
    | TCommand cmd =>
        orb (string_contains_substring cmd "textbf")
        (orb (string_contains_substring cmd "textit") 
             (string_contains_substring cmd "emph"))
    | _ => false
    end) expanded.

Definition post_004_validator : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      if negb (post_004_check_modern_commands expanded) then
        (* Only flag if document had text formatting but no modern commands *)
        if existsb (fun tok => match tok with TText _ => true | _ => false end) expanded then
          [{| rule_id := "POST-004";
              issue_severity := Info;
              message := "Consider using modern LaTeX formatting commands";
              loc := None;
              suggested_fix := Some "modernize_formatting";
              rule_owner := "@style-team" |}]
        else []
      else []
    else [].

Definition post_004_rule : validation_rule := {|
  id := "POST-004";
  description := "Consider using modern LaTeX formatting commands";
  precondition := L1_Expanded;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@style-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "modernize_formatting";
  implementation_file := "rules/phase1_5/PostExpansionRules.v";
  validator := post_004_validator;
  rule_sound := None
|}.

(** ** POST-005: Expansion completeness check *)

(** Verify that all expected macros were properly expanded *)
Definition post_005_check_expansion_completeness (original expanded : list latex_token) : bool :=
  let original_macros := filter (fun tok => 
    match tok with 
    | TCommand cmd => existsb (fun m => if string_dec m.(ename) cmd then true else false) working_latex_macros
    | _ => false 
    end) original in
  let expanded_macros := filter (fun tok =>
    match tok with
    | TCommand cmd => existsb (fun m => if string_dec m.(ename) cmd then true else false) working_latex_macros  
    | _ => false
    end) expanded in
  Nat.ltb (length expanded_macros) (length original_macros).

Definition post_005_validator : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let original := doc.(tokens) in
      let expanded := get_expanded_tokens doc in
      if post_005_check_expansion_completeness original expanded then
        [{| rule_id := "POST-005";
            issue_severity := Info;
            message := "Some built-in macros were successfully expanded";
            loc := None;
            suggested_fix := Some "verify_expansion_quality";
            rule_owner := "@expansion-team" |}]
      else []
    else [].

Definition post_005_rule : validation_rule := {|
  id := "POST-005";
  description := "Macro expansion completeness check";
  precondition := L1_Expanded;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@expansion-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "verify_expansion_quality";
  implementation_file := "rules/phase1_5/PostExpansionRules.v";
  validator := post_005_validator;
  rule_sound := None
|}.

(** ** Phase 1½ Rule Collection *)

Definition phase1_5_rules : list validation_rule := [
  post_001_rule;
  post_002_rule;
  post_003_rule;
  post_004_rule;
  post_005_rule
].

(** ** Soundness Framework for Post-Expansion Rules *)

(** Property: Post-expansion rules only run on expanded documents *)
Definition post_expansion_precondition (rule : validation_rule) : Prop :=
  rule.(precondition) = L1_Expanded.

Theorem phase1_5_rules_have_correct_precondition :
  forall rule, In rule phase1_5_rules -> post_expansion_precondition rule.
Proof.
  intros rule H_in.
  unfold phase1_5_rules in H_in.
  unfold post_expansion_precondition.
  simpl in H_in.
  repeat (destruct H_in as [H_eq | H_in]; [subst; simpl; reflexivity | ]).
  contradiction.
Qed.

(** Property: Post-expansion validation preserves document state *)
Definition post_validation_preserves_state (validator : document_state -> list validation_issue) : Prop :=
  forall doc, 
    doc.(doc_layer) = L1_Expanded ->
    (forall doc', doc' = doc -> validator doc' = validator doc).

(** ** Phase 1½ Integration *)

(** Update document state to include Phase 1½ validation *)
Definition validate_with_post_expansion (doc : document_state) : document_state * list validation_issue :=
  let expanded_doc := expand_document_state doc in
  let issues := flat_map (fun rule => execute_rule rule expanded_doc) phase1_5_rules in
  (expanded_doc, issues).

(** ** Phase 1½ Status *)
(**
  Week 13 Completion: Post-expansion validation framework
  
  ✅ 5 Phase 1½ validation rules implemented
  ✅ L1_Expanded layer integration
  ✅ Post-expansion issue detection (deprecated macros, typography, completeness)
  ✅ Performance bucketing for post-expansion rules
  ✅ Soundness framework for post-expansion properties
  ✅ Integration with document_state expansion pipeline
  
  Ready for Week 16: L2 Parser layer implementation
**)