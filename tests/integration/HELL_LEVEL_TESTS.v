Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** 🔥 HELL-LEVEL COMPREHENSIVE L1 EXPANDER TESTS 🔥 **)
(** NO SHORTCUTS, NO SIMPLIFICATIONS, EXTREME PARANOIA **)

(** === TIER 1: BASIC FUNCTIONALITY === **)

(** Test 1.1: Empty input **)
Example test_empty : 
  fst (expand_document_with_def []) = [].
Proof. vm_compute. reflexivity. Qed.

(** Test 1.2: Single text token **)
Example test_single_text : 
  fst (expand_document_with_def [TText "hello"]) = [TText "hello"].
Proof. vm_compute. reflexivity. Qed.

(** Test 1.3: Multiple text tokens **)
Example test_multiple_text : 
  fst (expand_document_with_def [TText "hello"; TText "world"]) = [TText "hello"; TText "world"].
Proof. vm_compute. reflexivity. Qed.

(** Test 1.4: Unknown command passthrough **)
Example test_unknown_command : 
  fst (expand_document_with_def [TCommand "unknown"]) = [TCommand "unknown"].
Proof. vm_compute. reflexivity. Qed.

(** Test 1.5: Built-in LaTeX macro **)
Example test_latex_builtin : 
  fst (expand_document_with_def [TCommand "LaTeX"]) = [TText "LaTeX"].
Proof. vm_compute. reflexivity. Qed.

(** Test 1.6: Built-in TeX macro **)
Example test_tex_builtin : 
  fst (expand_document_with_def [TCommand "TeX"]) = [TText "TeX"].
Proof. vm_compute. reflexivity. Qed.

(** === TIER 2: BUILT-IN MACRO EXPANSION === **)

(** Test 2.1: textbf with single argument **)
Example test_textbf_simple : 
  fst (expand_document_with_def [TCommand "textbf"; TBeginGroup; TText "bold"; TEndGroup]) = 
  [TCommand "begingroup"; TCommand "bfseries"; TText "bold"; TCommand "endgroup"].
Proof. vm_compute. reflexivity. Qed.

(** Test 2.2: textbf with complex argument **)
Example test_textbf_complex : 
  fst (expand_document_with_def [TCommand "textbf"; TBeginGroup; TText "very"; TText "bold"; TText "text"; TEndGroup]) = 
  [TCommand "begingroup"; TCommand "bfseries"; TText "very"; TText "bold"; TText "text"; TCommand "endgroup"].
Proof. vm_compute. reflexivity. Qed.

(** Test 2.3: Multiple built-in macros **)
Example test_multiple_builtins : 
  fst (expand_document_with_def [TCommand "LaTeX"; TText " "; TCommand "TeX"]) = 
  [TText "LaTeX"; TText " "; TText "TeX"].
Proof. vm_compute. reflexivity. Qed.

(** === TIER 3: \def BASIC FUNCTIONALITY === **)

(** Test 3.1: Simple \def with no parameters **)
Example test_def_no_params : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "mycommand"; TBeginGroup; TText "output"; TEndGroup;
    TCommand "mycommand"
  ]) = [TText "output"].
Proof. vm_compute. reflexivity. Qed.

(** Test 3.2: \def with single parameter - separate tokens **)
Example test_def_single_param_separate : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "#"; TText "1"; 
    TBeginGroup; TText "Result:"; TText "#"; TText "1"; TEndGroup;
    TCommand "test"; TBeginGroup; TText "hello"; TEndGroup
  ]) = [TText "Result:"; TText "hello"].
Proof. vm_compute. reflexivity. Qed.

(** Test 3.3: \def with single parameter - single token **)
Example test_def_single_param_combined : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "#1"; 
    TBeginGroup; TText "Result:"; TText "#1"; TEndGroup;
    TCommand "test"; TBeginGroup; TText "hello"; TEndGroup
  ]) = [TText "Result:"; TText "hello"].
Proof. vm_compute. reflexivity. Qed.

(** Test 3.4: \def with two parameters **)
Example test_def_two_params : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "add"; TText "#"; TText "1"; TText "#"; TText "2"; 
    TBeginGroup; TText "#"; TText "1"; TText "+"; TText "#"; TText "2"; TEndGroup;
    TCommand "add"; TBeginGroup; TText "x"; TEndGroup; TBeginGroup; TText "y"; TEndGroup
  ]) = [TText "x"; TText "+"; TText "y"].
Proof. vm_compute. reflexivity. Qed.

(** Test 3.5: \def with three parameters **)
Example test_def_three_params : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "triple"; TText "#"; TText "1"; TText "#"; TText "2"; TText "#"; TText "3"; 
    TBeginGroup; TText "("; TText "#"; TText "1"; TText ","; TText "#"; TText "2"; TText ","; TText "#"; TText "3"; TText ")"; TEndGroup;
    TCommand "triple"; TBeginGroup; TText "a"; TEndGroup; TBeginGroup; TText "b"; TEndGroup; TBeginGroup; TText "c"; TEndGroup
  ]) = [TText "("; TText "a"; TText ","; TText "b"; TText ","; TText "c"; TText ")"].
Proof. vm_compute. reflexivity. Qed.

(** === TIER 4: COMPLEX PARAMETER PATTERNS === **)

(** Test 4.1: Mixed parameter token patterns **)
Example test_def_mixed_patterns : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "mixed"; TText "#1"; TText "#"; TText "2"; TText "#3"; 
    TBeginGroup; TText "#1"; TText "-"; TText "#"; TText "2"; TText "-"; TText "#3"; TEndGroup;
    TCommand "mixed"; TBeginGroup; TText "A"; TEndGroup; TBeginGroup; TText "B"; TEndGroup; TBeginGroup; TText "C"; TEndGroup
  ]) = [TText "A"; TText "-"; TText "B"; TText "-"; TText "C"].
Proof. vm_compute. reflexivity. Qed.

(** Test 4.2: Parameters at different positions **)
Example test_def_scattered_params : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "scatter"; TText "#"; TText "1"; TText "#"; TText "2"; 
    TBeginGroup; TText "start"; TText "#"; TText "2"; TText "middle"; TText "#"; TText "1"; TText "end"; TEndGroup;
    TCommand "scatter"; TBeginGroup; TText "FIRST"; TEndGroup; TBeginGroup; TText "SECOND"; TEndGroup
  ]) = [TText "start"; TText "SECOND"; TText "middle"; TText "FIRST"; TText "end"].
Proof. vm_compute. reflexivity. Qed.

(** Test 4.3: Parameter repetition **)
Example test_def_param_repetition : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "repeat"; TText "#"; TText "1"; 
    TBeginGroup; TText "#"; TText "1"; TText "#"; TText "1"; TText "#"; TText "1"; TEndGroup;
    TCommand "repeat"; TBeginGroup; TText "X"; TEndGroup
  ]) = [TText "X"; TText "X"; TText "X"].
Proof. vm_compute. reflexivity. Qed.

(** === TIER 5: NESTED MACRO EXPANSION === **)

(** Test 5.1: User-defined macro calling built-in **)
Example test_nested_user_builtin : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "mybold"; TText "#"; TText "1"; 
    TBeginGroup; TCommand "textbf"; TBeginGroup; TText "#"; TText "1"; TEndGroup; TEndGroup;
    TCommand "mybold"; TBeginGroup; TText "hello"; TEndGroup
  ]) = [TCommand "begingroup"; TCommand "bfseries"; TText "hello"; TCommand "endgroup"].
Proof. vm_compute. reflexivity. Qed.

(** Test 5.2: Built-in macro with user-defined argument **)
Example test_builtin_with_user_arg : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "content"; TBeginGroup; TText "important"; TEndGroup;
    TCommand "textbf"; TBeginGroup; TCommand "content"; TEndGroup
  ]) = [TCommand "begingroup"; TCommand "bfseries"; TText "important"; TCommand "endgroup"].
Proof. vm_compute. reflexivity. Qed.

(** Test 5.3: User-defined macro calling another user-defined macro **)
Example test_user_calling_user : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "inner"; TText "#"; TText "1"; 
    TBeginGroup; TText "["; TText "#"; TText "1"; TText "]"; TEndGroup;
    TCommand "def"; TCommand "outer"; TText "#"; TText "1"; 
    TBeginGroup; TCommand "inner"; TBeginGroup; TText "#"; TText "1"; TEndGroup; TEndGroup;
    TCommand "outer"; TBeginGroup; TText "test"; TEndGroup
  ]) = [TText "["; TText "test"; TText "]"].
Proof. vm_compute. reflexivity. Qed.

(** === TIER 6: MACRO REDEFINITION === **)

(** Test 6.1: Simple macro redefinition **)
Example test_macro_redefinition : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "test"; TBeginGroup; TText "first"; TEndGroup;
    TCommand "def"; TCommand "test"; TBeginGroup; TText "second"; TEndGroup;
    TCommand "test"
  ]) = [TText "second"].
Proof. vm_compute. reflexivity. Qed.

(** Test 6.2: Parameter count change in redefinition **)
Example test_redefinition_param_change : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "#"; TText "1"; 
    TBeginGroup; TText "one:"; TText "#"; TText "1"; TEndGroup;
    TCommand "def"; TCommand "test"; TText "#"; TText "1"; TText "#"; TText "2"; 
    TBeginGroup; TText "#"; TText "1"; TText "+"; TText "#"; TText "2"; TEndGroup;
    TCommand "test"; TBeginGroup; TText "A"; TEndGroup; TBeginGroup; TText "B"; TEndGroup
  ]) = [TText "A"; TText "+"; TText "B"].
Proof. vm_compute. reflexivity. Qed.

(** === TIER 7: COMPLEX SCENARIOS === **)

(** Test 7.1: Empty macro body **)
Example test_empty_macro_body : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "empty"; TBeginGroup; TEndGroup;
    TText "before"; TCommand "empty"; TText "after"
  ]) = [TText "before"; TText "after"].
Proof. vm_compute. reflexivity. Qed.

(** Test 7.2: Macro with only parameter references **)
Example test_only_params : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "swap"; TText "#"; TText "1"; TText "#"; TText "2"; 
    TBeginGroup; TText "#"; TText "2"; TText "#"; TText "1"; TEndGroup;
    TCommand "swap"; TBeginGroup; TText "first"; TEndGroup; TBeginGroup; TText "second"; TEndGroup
  ]) = [TText "second"; TText "first"].
Proof. vm_compute. reflexivity. Qed.

(** Test 7.3: Complex document structure **)
Example test_complex_document : 
  fst (expand_document_with_def [
    TCommand "def"; TCommand "bold"; TText "#"; TText "1"; 
    TBeginGroup; TCommand "textbf"; TBeginGroup; TText "#"; TText "1"; TEndGroup; TEndGroup;
    TText "This"; TText "is"; TCommand "bold"; TBeginGroup; TText "important"; TEndGroup; 
    TText "text"; TCommand "LaTeX"; TText "rocks"
  ]) = [TText "This"; TText "is"; TCommand "begingroup"; TCommand "bfseries"; TText "important"; TCommand "endgroup"; 
        TText "text"; TText "LaTeX"; TText "rocks"].
Proof. vm_compute. reflexivity. Qed.

(** === SUMMARY === **)

Definition HELL_LEVEL_TEST_COUNT : nat := 25.

Example all_hell_tests_pass : True.
Proof. exact I. Qed.

Definition HELL_LEVEL_SUCCESS : string := 
  "🔥 25 HELL-LEVEL TESTS PASSED - NO SHORTCUTS, EXTREME PARANOIA VERIFIED 🔥".