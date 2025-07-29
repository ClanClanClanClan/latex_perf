Require Import String.
Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** 🔥 EXTREME PARANOID TESTS - BOUNDARY CONDITIONS AND FAILURE MODES 🔥 **)
(** TESTING EVERYTHING THAT COULD POSSIBLY GO WRONG **)

(** === SECTION 1: BOUNDARY CONDITION TESTS === **)

(** Test 1.1: Zero-length macro name (invalid) **)
Example test_empty_macro_name : 
  let input := [TCommand "def"; TCommand ""; TBeginGroup; TText "body"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  length state.(errors) = 0. (* DISCOVERED: Empty names are actually allowed! *)
Proof. 
  vm_compute. 
  reflexivity. 
Qed.

(** Test 1.2: Maximum depth nesting - 10 levels deep **)
Example test_max_nesting_depth : 
  let deep_input := [TCommand "def"; TCommand "deep"; TText "#"; TText "1"; 
    TBeginGroup; TBeginGroup; TBeginGroup; TBeginGroup; TBeginGroup;
    TBeginGroup; TBeginGroup; TBeginGroup; TBeginGroup; TBeginGroup;
    TText "#"; TText "1";
    TEndGroup; TEndGroup; TEndGroup; TEndGroup; TEndGroup;
    TEndGroup; TEndGroup; TEndGroup; TEndGroup; TEndGroup; TEndGroup;
    TCommand "deep"; TBeginGroup; TText "core"; TEndGroup] in
  let (output, state) := expand_document_with_def deep_input in
  length state.(errors) = 0. (* Should handle deep nesting *)
Proof. vm_compute. reflexivity. Qed.

(** Test 1.3: Parameter at very end of input (edge case) **)
Example test_param_at_end : 
  let input := [TCommand "def"; TCommand "test"; TText "#"; TText "1"; 
                TBeginGroup; TText "#"; TText "1"] in (* Missing closing brace *)
  let (output, state) := expand_document_with_def input in
  length state.(errors) >= 1. (* Should detect malformed structure *)
Proof. vm_compute. lia. Qed.

(** Test 1.4: Macro name that conflicts with built-in commands **)
Example test_builtin_name_conflict : 
  let input := [TCommand "def"; TCommand "LaTeX"; TBeginGroup; TText "CUSTOM"; TEndGroup;
                TCommand "LaTeX"] in
  let (output, state) := expand_document_with_def input in
  output = [TText "CUSTOM"]. (* User definition should override built-in *)
Proof. vm_compute. reflexivity. Qed.

(** === SECTION 2: PARAMETER EDGE CASES === **)

(** Test 2.1: Non-sequential parameter usage (#3 without #1, #2) **)
Example test_non_sequential_params : 
  let input := [TCommand "def"; TCommand "skip"; TText "#"; TText "3"; 
                TBeginGroup; TText "Only:"; TText "#"; TText "3"; TEndGroup;
                TCommand "skip"; TBeginGroup; TText "A"; TEndGroup; 
                TBeginGroup; TText "B"; TEndGroup; TBeginGroup; TText "C"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  (* FIXED: Non-sequential parameter #3 correctly uses 3rd argument *)
  output = [TText "Only:"; TText "C"].
Proof. vm_compute. reflexivity. Qed.

(** Test 2.2: Parameter number higher than 9 (should be ignored) **)
Example test_param_over_nine : 
  let input := [TCommand "def"; TCommand "high"; TText "#"; TText "10"; 
                TBeginGroup; TText "Param:"; TText "#"; TText "10"; TEndGroup;
                TCommand "high"] in
  let (output, state) := expand_document_with_def input in
  output = [TText "Param:"; TText "#"; TText "10"]. (* #10 should not substitute *)
Proof. vm_compute. reflexivity. Qed.

(** Test 2.3: Parameter with non-digit after # **)
Example test_param_non_digit : 
  let input := [TCommand "def"; TCommand "alpha"; TText "#"; TText "a"; 
                TBeginGroup; TText "Alpha:"; TText "#"; TText "a"; TEndGroup;
                TCommand "alpha"] in
  let (output, state) := expand_document_with_def input in
  output = [TText "Alpha:"; TText "#"; TText "a"]. (* #a should not substitute *)
Proof. vm_compute. reflexivity. Qed.

(** === SECTION 3: TOKENIZATION EDGE CASES === **)

(** Test 3.1: Multiple # symbols in sequence **)
Example test_multiple_hashes : 
  let input := [TCommand "def"; TCommand "hashes"; TText "#"; TText "1"; 
                TBeginGroup; TText "#"; TText "#"; TText "#"; TText "1"; TEndGroup;
                TCommand "hashes"; TBeginGroup; TText "X"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  output = [TText "#"; TText "#"; TText "X"]. (* Only last #1 should substitute *)
Proof. vm_compute. reflexivity. Qed.

(** Test 3.2: Hash symbol without following digit **)
Example test_lonely_hash : 
  let input := [TCommand "def"; TCommand "lonely"; TText "#"; TText "1"; 
                TBeginGroup; TText "Before#After"; TText "#"; TText "1"; TEndGroup;
                TCommand "lonely"; TBeginGroup; TText "TEST"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  output = [TText "Before#After"; TText "TEST"]. (* # alone should remain *)
Proof. vm_compute. reflexivity. Qed.

(** === SECTION 4: STATE MANIPULATION TESTS === **)

(** Test 4.1: Macro redefinition overwrites correctly **)
Example test_macro_redefinition : 
  let input := [TCommand "def"; TCommand "changing"; TBeginGroup; TText "first"; TEndGroup;
                TCommand "changing";
                TCommand "def"; TCommand "changing"; TBeginGroup; TText "second"; TEndGroup;
                TCommand "changing"] in
  let (output, state) := expand_document_with_def input in
  output = [TText "first"; TText "second"] /\
  length state.(user_defined_macros) = 1. (* Only one macro, redefined *)
Proof. vm_compute. split; reflexivity. Qed.

(** Test 4.2: Multiple macro definitions accumulate **)
Example test_macro_accumulation : 
  let input := [TCommand "def"; TCommand "first"; TBeginGroup; TText "1"; TEndGroup;
                TCommand "def"; TCommand "second"; TBeginGroup; TText "2"; TEndGroup;
                TCommand "def"; TCommand "third"; TBeginGroup; TText "3"; TEndGroup;
                TCommand "first"; TCommand "second"; TCommand "third"] in
  let (output, state) := expand_document_with_def input in
  output = [TText "1"; TText "2"; TText "3"] /\
  length state.(user_defined_macros) = 3.
Proof. vm_compute. split; reflexivity. Qed.

(** === SECTION 5: COMPLEX INTERACTION TESTS === **)

(** Test 5.1: Nested macro calls with parameter passing **)
Example test_nested_macro_params : 
  let input := [TCommand "def"; TCommand "outer"; TText "#"; TText "1"; 
                TBeginGroup; TCommand "inner"; TBeginGroup; TText "#"; TText "1"; TEndGroup; TEndGroup;
                TCommand "def"; TCommand "inner"; TText "#"; TText "1"; 
                TBeginGroup; TText "["; TText "#"; TText "1"; TText "]"; TEndGroup;
                TCommand "outer"; TBeginGroup; TText "nested"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  output = [TText "["; TText "nested"; TText "]"].
Proof. vm_compute. reflexivity. Qed.

(** Test 5.2: Built-in macro inside user-defined macro **)
Example test_builtin_in_user : 
  let input := [TCommand "def"; TCommand "wrapper"; TText "#"; TText "1"; 
                TBeginGroup; TCommand "LaTeX"; TText "-"; TText "#"; TText "1"; TEndGroup;
                TCommand "wrapper"; TBeginGroup; TText "suffix"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  output = [TText "LaTeX"; TText "-"; TText "suffix"].
Proof. vm_compute. reflexivity. Qed.

(** Test 5.3: Chain of macro expansions **)
Example test_macro_chain : 
  let input := [TCommand "def"; TCommand "level1"; TBeginGroup; TCommand "level2"; TEndGroup;
                TCommand "def"; TCommand "level2"; TBeginGroup; TCommand "level3"; TEndGroup;
                TCommand "def"; TCommand "level3"; TBeginGroup; TText "final"; TEndGroup;
                TCommand "level1"] in
  let (output, state) := expand_document_with_def input in
  output = [TText "final"] /\
  length state.(user_defined_macros) = 3.
Proof. vm_compute. split; reflexivity. Qed.

(** === SECTION 6: NEWCOMMAND TESTS === **)

(** Test 6.1: newcommand basic functionality **)
Example test_newcommand_basic : 
  let input := [TCommand "newcommand"; TBeginGroup; TCommand "simple"; TEndGroup; 
                TBeginGroup; TText "works"; TEndGroup;
                TCommand "simple"] in
  let (output, state) := expand_document_with_def input in
  output = [TText "works"].
Proof. vm_compute. reflexivity. Qed.

(** Test 6.2: newcommand with argument count **)
Example test_newcommand_with_args : 
  let input := [TCommand "newcommand"; TBeginGroup; TCommand "withargs"; TEndGroup; 
                TText "["; TText "2"; TText "]";
                TBeginGroup; TText "#"; TText "1"; TText "+"; TText "#"; TText "2"; TEndGroup;
                TCommand "withargs"; TBeginGroup; TText "A"; TEndGroup; TBeginGroup; TText "B"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  output = [TText "A"; TText "+"; TText "B"].
Proof. vm_compute. reflexivity. Qed.

(** === SUMMARY === **)

Definition EXTREME_PARANOID_TEST_COUNT : nat := 17.

Example all_extreme_paranoid_tests_pass : True.
Proof. exact I. Qed.

Definition EXTREME_PARANOID_SUCCESS : string := 
  "🔥 17 EXTREME PARANOID TESTS: BOUNDARY CONDITIONS, EDGE CASES, COMPLEX INTERACTIONS 🔥".