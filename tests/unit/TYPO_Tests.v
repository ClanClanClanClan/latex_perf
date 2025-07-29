(* Unit tests for TYPO (Typography) validation rules *)

From Coq Require Import String List Bool.
Import ListNotations.

(* Import test framework and validators *)
From LP.Tests Require Import TestFramework.
From LP.Rules.TYPO Require Import TYPO_001 TYPO_002 TYPO_003 TYPO_004 TYPO_005.
From LP Require Import ValidationResult RuleId.

Open Scope string_scope.

(* TYPO-001: Straight quotes detection *)
Module TYPO_001_Tests.
  
  (* Test: Detects double straight quotes *)
  Example test_detects_double_quotes :
    let doc := TestFramework.make_test_doc "She said \"hello\" to him." in
    let results := TYPO_001.validator doc in
    TestFramework.rule_triggered TYPO_001_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Detects single straight quotes *)
  Example test_detects_single_quotes :
    let doc := TestFramework.make_test_doc "It's a 'nice' day." in
    let results := TYPO_001.validator doc in
    TestFramework.rule_triggered TYPO_001_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts curly quotes *)
  Example test_accepts_curly_quotes :
    let doc := TestFramework.make_test_doc "She said "hello" to him." in
    let results := TYPO_001.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts smart apostrophes *)
  Example test_accepts_smart_apostrophes :
    let doc := TestFramework.make_test_doc "It's a 'nice' day." in
    let results := TYPO_001.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Handles mixed quotes correctly *)
  Example test_mixed_quotes :
    let doc := TestFramework.make_test_doc "She said \"hello\" but meant "goodbye"." in
    let results := TYPO_001.validator doc in
    length results = 1. (* Only the straight quotes are flagged *)
  Proof. vm_compute. reflexivity. Qed.
  
End TYPO_001_Tests.

(* TYPO-002: Incorrect ellipsis detection *)
Module TYPO_002_Tests.
  
  (* Test: Detects three periods *)
  Example test_detects_three_periods :
    let doc := TestFramework.make_test_doc "And so on..." in
    let results := TYPO_002.validator doc in
    TestFramework.rule_triggered TYPO_002_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Detects spaced periods *)
  Example test_detects_spaced_periods :
    let doc := TestFramework.make_test_doc "And so on. . ." in
    let results := TYPO_002.validator doc in
    TestFramework.rule_triggered TYPO_002_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts proper ellipsis character *)
  Example test_accepts_ellipsis_char :
    let doc := TestFramework.make_test_doc "And so on…" in
    let results := TYPO_002.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts LaTeX \ldots *)
  Example test_accepts_ldots :
    let doc := TestFramework.make_test_doc "And so on\ldots" in
    let results := TYPO_002.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Doesn't flag two periods *)
  Example test_ignores_two_periods :
    let doc := TestFramework.make_test_doc "U.S. is an abbreviation." in
    let results := TYPO_002.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
End TYPO_002_Tests.

(* TYPO-003: Hyphen/dash confusion *)
Module TYPO_003_Tests.
  
  (* Test: Detects hyphen used as em dash *)
  Example test_detects_hyphen_as_em_dash :
    let doc := TestFramework.make_test_doc "This is wrong - very wrong." in
    let results := TYPO_003.validator doc in
    TestFramework.rule_triggered TYPO_003_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Detects double hyphen *)
  Example test_detects_double_hyphen :
    let doc := TestFramework.make_test_doc "This is wrong--very wrong." in
    let results := TYPO_003.validator doc in
    TestFramework.rule_triggered TYPO_003_id results = true.
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts proper em dash *)
  Example test_accepts_em_dash :
    let doc := TestFramework.make_test_doc "This is right—very right." in
    let results := TYPO_003.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts LaTeX --- *)
  Example test_accepts_latex_em_dash :
    let doc := TestFramework.make_test_doc "This is right---very right." in
    let results := TYPO_003.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
  (* Test: Accepts hyphen in compound words *)
  Example test_accepts_compound_words :
    let doc := TestFramework.make_test_doc "This is a well-known fact." in
    let results := TYPO_003.validator doc in
    results = [].
  Proof. vm_compute. reflexivity. Qed.
  
End TYPO_003_Tests.

(* Test suite aggregation *)
Definition typo_test_cases : list test_case := [
  {| test_name := "TYPO-001: Detects double straight quotes";
     test_doc := "She said \"hello\" to him.";
     expected_rules := [TYPO_001_id];
     test_description := "Straight quotes should be replaced with curly quotes" |};
     
  {| test_name := "TYPO-001: Accepts curly quotes";
     test_doc := "She said "hello" to him.";
     expected_rules := [];
     test_description := "Curly quotes should not trigger the rule" |};
     
  {| test_name := "TYPO-002: Detects three periods";
     test_doc := "And so on...";
     expected_rules := [TYPO_002_id];
     test_description := "Three periods should be replaced with ellipsis" |};
     
  {| test_name := "TYPO-002: Accepts ellipsis character";
     test_doc := "And so on…";
     expected_rules := [];
     test_description := "Proper ellipsis should not trigger the rule" |};
     
  {| test_name := "TYPO-003: Detects spaced hyphen as dash";
     test_doc := "This is wrong - very wrong.";
     expected_rules := [TYPO_003_id];
     test_description := "Spaced hyphen should be em dash" |};
     
  {| test_name := "TYPO-003: Accepts proper em dash";
     test_doc := "This is right—very right.";
     expected_rules := [];
     test_description := "Em dash should not trigger the rule" |}
].

(* Performance benchmarks *)
Module TYPO_Performance.
  
  Definition large_doc_test : string :=
    (* Generate a 30KB document with various typography issues *)
    TestFramework.make_test_doc (
      String.concat " " (repeat "She said \"hello\" to him. " 1000)
    ).
  
  (* Measure validation time *)
  Definition benchmark_typo_rules (doc : string) : nat :=
    let t1 := TYPO_001.validator doc in
    let t2 := TYPO_002.validator doc in
    let t3 := TYPO_003.validator doc in
    length t1 + length t2 + length t3.
  
End TYPO_Performance.

(* Property-based tests *)
Module TYPO_Properties.
  
  (* Property: No quotes means no TYPO-001 issues *)
  Definition prop_no_quotes_no_issues : Prop :=
    forall s : string,
      (forall c, In c (string_to_list s) -> 
        c <> """" /\ c <> """" /\ c <> "'" /\ c <> "'") ->
      TYPO_001.validator s = [].
  
  (* Property: Validator is deterministic *)
  Definition prop_deterministic : Prop :=
    forall s : string,
      TYPO_001.validator s = TYPO_001.validator s.
  
End TYPO_Properties.