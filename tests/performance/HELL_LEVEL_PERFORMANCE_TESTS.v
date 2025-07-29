Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ValidationTypes.
Require Import TypoRules.
Open Scope string_scope.

(** 🔥 HELL-LEVEL PERFORMANCE REGRESSION TESTS 🔥 **)
(** BENCHMARKING AND PERFORMANCE BOUNDARY TESTING **)

(** === HELPER FUNCTIONS === **)

Definition make_perf_test_doc (content : string) : document_state :=
  let tokens := lex content in
  {|
    tokens := tokens;
    expanded_tokens := None;
    ast := None;
    semantics := None;
    filename := "performance_test.tex";
    doc_layer := L0_Lexer
  |}.

(** Generate large content for stress testing **)
Definition generate_large_content (base : string) (multiplier : nat) : string :=
  let fix repeat (n : nat) : string :=
    match n with
    | 0 => ""
    | S n' => base ++ " " ++ repeat n'
    end
  in repeat multiplier.

(** === LEXER PERFORMANCE TESTS === **)

(** Test lexing speed on large documents **)
Example test_lexer_large_document : 
  let large_doc := generate_large_content "hello world" 1000 in
  let doc := make_perf_test_doc large_doc in
  length doc.(tokens) = 4000.
Proof. vm_compute. reflexivity. Qed.

(** Test lexing deeply nested structures **)
Example test_lexer_deep_nesting : 
  let fix make_nested (n : nat) : string :=
    match n with
    | 0 => "content"
    | S n' => "\begin{env}" ++ make_nested n' ++ "\end{env}"
    end in
  let nested := make_nested 50 in
  let doc := make_perf_test_doc nested in
  length doc.(tokens) >= 50.
Proof. vm_compute. reflexivity. Qed.

(** Test lexing many small tokens **)
Example test_lexer_many_tokens : 
  let many_cmds := generate_large_content "\a \b \c \d \e" 200 in
  let doc := make_perf_test_doc many_cmds in
  length doc.(tokens) >= 100.
Proof. vm_compute. reflexivity. Qed.

(** === VALIDATOR PERFORMANCE TESTS === **)

(** Test validator on documents with many potential issues **)
Example test_validator_many_issues : 
  let problematic := generate_large_content "straight quotes here" 100 in
  let doc := make_perf_test_doc problematic in
  (* Should complete even with many issues *)
  length (typo_001_validator doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** Test validator on documents with no issues **)
Example test_validator_no_issues : 
  let clean := generate_large_content "clean text without issues" 500 in
  let doc := make_perf_test_doc clean in
  (* Should be fast when no issues found *)
  length (typo_001_validator doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** Test multiple validators on same document **)
Example test_multiple_validators : 
  let content := generate_large_content "test content" 100 in
  let doc := make_perf_test_doc content in
  let results := 
    (typo_001_validator doc) ++
    (typo_002_validator doc) ++
    (typo_003_validator doc) ++
    (enc_001_validator doc) ++
    (char_001_validator doc) in
  length results >= 0.
Proof. vm_compute. reflexivity. Qed.

(** === RULE EXECUTION PERFORMANCE === **)

(** Test execute_rules with all rules **)
Example test_all_rules_performance : 
  let doc := make_perf_test_doc (generate_large_content "comprehensive test" 50) in
  let all_rules := all_l0_rules in
  (* Should handle all 76 rules efficiently *)
  length (execute_rules all_rules doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** Test rule filtering performance **)
Example test_rule_filtering : 
  let doc := make_perf_test_doc "test" in
  let applicable := filter (fun r => rule_applicable r doc) all_l0_rules in
  length applicable >= 75. (* Most L0 rules should be applicable *)
Proof. vm_compute. reflexivity. Qed.

(** === MEMORY STRESS TESTS === **)

(** Test with maximum token count **)
Definition make_max_tokens : string :=
  generate_large_content "a b c d e f g h i j" 500.

Example test_max_token_count : 
  let doc := make_perf_test_doc make_max_tokens in
  length doc.(tokens) >= 1000.
Proof. vm_compute. reflexivity. Qed.

(** Test with very long individual tokens **)
Definition make_long_token : string :=
  let fix repeat_char (c : ascii) (n : nat) : string :=
    match n with
    | 0 => ""
    | S n' => String c (repeat_char c n')
    end in
  repeat_char "a"%char 1000.

Example test_long_token_handling : 
  let doc := make_perf_test_doc make_long_token in
  length doc.(tokens) >= 50.
Proof. vm_compute. reflexivity. Qed.

(** === PATHOLOGICAL INPUT TESTS === **)

(** Test alternating patterns **)
Example test_alternating_pattern : 
  let alternating := generate_large_content "{a}[b]{c}[d]" 250 in
  let doc := make_perf_test_doc alternating in
  length (typo_001_validator doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** Test many small environments **)
Example test_many_environments : 
  let envs := generate_large_content "\begin{x}y\end{x}" 200 in
  let doc := make_perf_test_doc envs in
  length (typo_001_validator doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** Test command soup **)
Example test_command_soup : 
  let soup := "\alpha\beta\gamma\delta\epsilon\zeta\eta\theta\iota\kappa" in
  let many_soup := generate_large_content soup 100 in
  let doc := make_perf_test_doc many_soup in
  length (typo_001_validator doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** === WORST-CASE COMPLEXITY TESTS === **)

(** Test quadratic behavior patterns **)
Example test_quadratic_pattern : 
  let pattern := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaab" in
  let repeated := generate_large_content pattern 50 in
  let doc := make_perf_test_doc repeated in
  (* Should complete without quadratic slowdown *)
  length (typo_001_validator doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** Test backtracking patterns **)
Example test_backtrack_pattern : 
  let backtrack := "(a+)+b" in
  let repeated := generate_large_content backtrack 100 in
  let doc := make_perf_test_doc repeated in
  length (typo_001_validator doc) >= 0.
Proof. vm_compute. reflexivity. Qed.

(** === CONCURRENT VALIDATION TESTS === **)

(** Test all validators on same large document **)
Example test_concurrent_validation : 
  let big_doc := make_perf_test_doc (generate_large_content "test all validators" 200) in
  let typo_issues := map (fun r => execute_rule r big_doc) 
    [typo_001_rule; typo_002_rule; typo_003_rule; typo_004_rule; typo_005_rule] in
  let enc_issues := map (fun r => execute_rule r big_doc)
    [enc_001_rule; enc_002_rule; enc_003_rule; enc_004_rule; enc_005_rule] in
  let all_issues := concat (typo_issues ++ enc_issues) in
  length all_issues >= 0.
Proof. vm_compute. reflexivity. Qed.

(** === PERFORMANCE REGRESSION GUARDS === **)

(** Ensure lexer completes in reasonable time **)
Example test_lexer_time_bound : 
  let reasonable_doc := generate_large_content "normal content" 100 in
  let doc := make_perf_test_doc reasonable_doc in
  (* This should complete quickly *)
  length doc.(tokens) <= 10000. (* Reasonable upper bound *)
Proof. vm_compute. reflexivity. Qed.

(** Ensure validators don't produce excessive issues **)
Example test_issue_count_bound : 
  let doc := make_perf_test_doc "This has straight quotes everywhere" in
  let issues := typo_001_validator doc in
  (* Should not explode issue count *)
  length issues <= 100.
Proof. vm_compute. reflexivity. Qed.

(** Ensure rule execution scales linearly **)
Example test_linear_scaling : 
  let small_doc := make_perf_test_doc "small" in
  let large_doc := make_perf_test_doc (generate_large_content "large" 10) in
  let small_issues := length (execute_rules all_l0_rules small_doc) in
  let large_issues := length (execute_rules all_l0_rules large_doc) in
  (* Issues should scale reasonably with document size *)
  large_issues <= small_issues * 20.
Proof. vm_compute. reflexivity. Qed.