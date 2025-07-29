(* Unit tests for MATH (Mathematics) validation rules *)

From Coq Require Import String List Bool.
Import ListNotations.

From LP.Tests Require Import TestFramework.
From LP.Rules.MATH Require Import MATH_001 MATH_002 MATH_003 MATH_004 MATH_005.
From LP Require Import ValidationResult RuleId.

Open Scope string_scope.

(* MATH-001: Inline math delimiter usage *)
Module MATH_001_Tests.
  
  (* Test: Detects single dollar signs *)
  Example test_detects_single_dollar :
    let doc := TestFramework.make_test_doc "The equation $x = y$ is simple." in
    let results := MATH_001.validator doc in
    TestFramework.rule_triggered MATH_001_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts \( \) delimiters *)
  Example test_accepts_parenthesis_delimiters :
    let doc := TestFramework.make_test_doc "The equation \(x = y\) is simple." in
    let results := MATH_001.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Handles nested math correctly *)
  Example test_nested_math :
    let doc := TestFramework.make_test_doc "Given $f(x) = x^2$, we see that $f'(x) = 2x$." in
    let results := MATH_001.validator doc in
    length results = 2. (* Both instances flagged *)
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Ignores escaped dollar signs *)
  Example test_ignores_escaped_dollar :
    let doc := TestFramework.make_test_doc "The price is \$50 dollars." in
    let results := MATH_001.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Handles empty math *)
  Example test_empty_math :
    let doc := TestFramework.make_test_doc "This $$ is problematic." in
    let results := MATH_001.validator doc in
    TestFramework.rule_triggered MATH_002_id results = true. (* Different rule *)
  Proof. vm_compute. reflexivity. Qed.
  
End MATH_001_Tests.

(* MATH-002: Display math delimiter usage *)
Module MATH_002_Tests.
  
  (* Test: Detects double dollar signs *)
  Example test_detects_double_dollar :
    let doc := TestFramework.make_test_doc "$$x = y$$" in
    let results := MATH_002.validator doc in
    TestFramework.rule_triggered MATH_002_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts \[ \] delimiters *)
  Example test_accepts_bracket_delimiters :
    let doc := TestFramework.make_test_doc "\[x = y\]" in
    let results := MATH_002.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts equation environment *)
  Example test_accepts_equation_env :
    let doc := TestFramework.make_test_doc "\begin{equation} x = y \end{equation}" in
    let results := MATH_002.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Detects display math in inline context *)
  Example test_display_math_inline :
    let doc := TestFramework.make_test_doc "The equation $$x = y$$ is in text." in
    let results := MATH_002.validator doc in
    TestFramework.rule_triggered MATH_002_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
End MATH_002_Tests.

(* MATH-003: Math mode command usage *)
Module MATH_003_Tests.
  
  (* Test: Detects math commands outside math mode *)
  Example test_math_command_outside_math :
    let doc := TestFramework.make_test_doc "The variable x_i is important." in
    let results := MATH_003.validator doc in
    TestFramework.rule_triggered MATH_003_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts math commands in math mode *)
  Example test_math_command_in_math :
    let doc := TestFramework.make_test_doc "The variable \(x_i\) is important." in
    let results := MATH_003.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Detects superscript outside math *)
  Example test_superscript_outside_math :
    let doc := TestFramework.make_test_doc "This is the 2^nd attempt." in
    let results := MATH_003.validator doc in
    TestFramework.rule_triggered MATH_003_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Detects Greek letters outside math *)
  Example test_greek_outside_math :
    let doc := TestFramework.make_test_doc "The \alpha particle is dangerous." in
    let results := MATH_003.validator doc in
    TestFramework.rule_triggered MATH_003_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts text mode alternatives *)
  Example test_text_mode_alternatives :
    let doc := TestFramework.make_test_doc "The α particle is dangerous." in
    let results := MATH_003.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
End MATH_003_Tests.

(* MATH-004: Fraction and division notation *)
Module MATH_004_Tests.
  
  (* Test: Detects slash fractions in math mode *)
  Example test_slash_fraction_in_math :
    let doc := TestFramework.make_test_doc "\(a/b\)" in
    let results := MATH_004.validator doc in
    TestFramework.rule_triggered MATH_004_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts \frac command *)
  Example test_accepts_frac :
    let doc := TestFramework.make_test_doc "\(\frac{a}{b}\)" in
    let results := MATH_004.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts slash in text mode *)
  Example test_slash_in_text :
    let doc := TestFramework.make_test_doc "The ratio is 1/2 in this case." in
    let results := MATH_004.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Complex fractions *)
  Example test_complex_fraction :
    let doc := TestFramework.make_test_doc "\(\frac{x + 1}{y - 1}\)" in
    let results := MATH_004.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
End MATH_004_Tests.

(* MATH-005: Math spacing issues *)
Module MATH_005_Tests.
  
  (* Test: Detects missing space after comma in math *)
  Example test_missing_space_after_comma :
    let doc := TestFramework.make_test_doc "\(x,y,z\)" in
    let results := MATH_005.validator doc in
    TestFramework.rule_triggered MATH_005_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts proper spacing *)
  Example test_proper_spacing :
    let doc := TestFramework.make_test_doc "\(x, y, z\)" in
    let results := MATH_005.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Detects operators without space *)
  Example test_operators_without_space :
    let doc := TestFramework.make_test_doc "\(x+y-z\)" in
    let results := MATH_005.validator doc in
    TestFramework.rule_triggered MATH_005_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts operators with proper spacing *)
  Example test_operators_with_space :
    let doc := TestFramework.make_test_doc "\(x + y - z\)" in
    let results := MATH_005.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
End MATH_005_Tests.

(* Comprehensive test suite *)
Definition math_test_suite : test_suite := [
  ({| test_name := "MATH-001: Single dollar math";
      test_doc := "The equation $x = y$ is simple.";
      expected_rules := [MATH_001_id];
      test_description := "Should use \( \) instead of $ $" |}, MATH_001.validator);
      
  ({| test_name := "MATH-002: Double dollar display math";
      test_doc := "$$x = y$$";
      expected_rules := [MATH_002_id];
      test_description := "Should use \[ \] instead of $$ $$" |}, MATH_002.validator);
      
  ({| test_name := "MATH-003: Math command outside math mode";
      test_doc := "The variable x_i is important.";
      expected_rules := [MATH_003_id];
      test_description := "Subscript requires math mode" |}, MATH_003.validator);
      
  ({| test_name := "MATH-004: Slash fraction in math";
      test_doc := "\(a/b\)";
      expected_rules := [MATH_004_id];
      test_description := "Should use \frac{a}{b}" |}, MATH_004.validator);
      
  ({| test_name := "MATH-005: Missing space in math";
      test_doc := "\(x,y,z\)";
      expected_rules := [MATH_005_id];
      test_description := "Should have spaces after commas" |}, MATH_005.validator)
].

(* Run all tests and generate report *)
Definition run_math_tests : string :=
  TestFramework.generate_test_report (TestFramework.run_test_suite math_test_suite).

(* Performance test for math rules *)
Module MATH_Performance.
  
  Definition math_heavy_document : string :=
    String.concat " " (repeat "$x_i$ and $y_j$ where $i,j \in \mathbb{N}$" 100).
  
  Definition benchmark_math_validation : nat :=
    let doc := math_heavy_document in
    length (MATH_001.validator doc) +
    length (MATH_002.validator doc) +
    length (MATH_003.validator doc) +
    length (MATH_004.validator doc) +
    length (MATH_005.validator doc).
  
End MATH_Performance.