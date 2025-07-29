Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** CLEAN INSTALL VERIFICATION TEST **)

(** Test 1: Built-in macro works **)
Example builtin_test : 
  fst (expand_document_with_def [TCommand "LaTeX"]) = [TText "LaTeX"].
Proof. vm_compute. reflexivity. Qed.

(** Test 2: \def parsing and substitution works **)
Example def_test :
  fst (expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "#"; TText "1"; 
    TBeginGroup; TText "Result:"; TText "#"; TText "1"; TEndGroup;
    TCommand "test"; TBeginGroup; TText "hello"; TEndGroup
  ]) = [TText "Result:"; TText "hello"].
Proof. vm_compute. reflexivity. Qed.

(** Test 3: Multiple parameters work **)
Example multi_param_test :
  fst (expand_document_with_def [
    TCommand "def"; TCommand "add"; TText "#"; TText "1"; TText "#"; TText "2"; 
    TBeginGroup; TText "#"; TText "1"; TText "+"; TText "#"; TText "2"; TEndGroup;
    TCommand "add"; TBeginGroup; TText "x"; TEndGroup; TBeginGroup; TText "y"; TEndGroup
  ]) = [TText "x"; TText "+"; TText "y"].
Proof. vm_compute. reflexivity. Qed.

(** SUCCESS: Clean install verification passed **)
Definition CLEAN_INSTALL_SUCCESS : string := 
  "✅ VERIFIED: Core L1 expander functionality working correctly".
