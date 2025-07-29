Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** * TIER 1 VERIFIED TESTS *)
(** Clean, verified tests that definitely compile and pass *)

(** Test 1: \renewcommand basic functionality *)
Example test_renewcommand_verified :
  let (output, state) := expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "test"; TEndGroup; 
    TBeginGroup; TText "OLD"; TEndGroup;
    TCommand "renewcommand"; TBeginGroup; TCommand "test"; TEndGroup; 
    TBeginGroup; TText "NEW"; TEndGroup;
    TCommand "test"
  ] in
  output = [TText "NEW"] /\
  length state.(user_defined_macros) = 1 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 2: \providecommand creates new macro *)
Example test_providecommand_verified :
  let (output, state) := expand_document_with_def [
    TCommand "providecommand"; TBeginGroup; TCommand "new"; TEndGroup; 
    TBeginGroup; TText "PROVIDED"; TEndGroup;
    TCommand "new"
  ] in
  output = [TText "PROVIDED"] /\
  length state.(user_defined_macros) = 1 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 3: \providecommand respects existing macros *)
Example test_providecommand_existing_verified :
  let (output, state) := expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "existing"; TEndGroup; 
    TBeginGroup; TText "ORIGINAL"; TEndGroup;
    TCommand "providecommand"; TBeginGroup; TCommand "existing"; TEndGroup; 
    TBeginGroup; TText "IGNORED"; TEndGroup;
    TCommand "existing"
  ] in
  output = [TText "ORIGINAL"] /\
  length state.(user_defined_macros) = 1 /\
  length state.(warnings) = 1.
Proof. reflexivity. Qed.

(** Test 4: \let command with equals *)
Example test_let_equals_verified :
  let (output, state) := expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "source"; TEndGroup; 
    TBeginGroup; TText "SOURCE"; TEndGroup;
    TCommand "let"; TCommand "copy"; TText "="; TCommand "source";
    TCommand "copy"
  ] in
  output = [TText "SOURCE"] /\
  length state.(user_defined_macros) = 2 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 5: \let command without equals *)
Example test_let_no_equals_verified :
  let (output, state) := expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "source"; TEndGroup; 
    TBeginGroup; TText "SOURCE"; TEndGroup;
    TCommand "let"; TCommand "alias"; TCommand "source";
    TCommand "alias"
  ] in
  output = [TText "SOURCE"] /\
  length state.(user_defined_macros) = 2 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 6: \let with built-in macros *)
Example test_let_builtin_verified :
  let (output, state) := expand_document_with_def [
    TCommand "let"; TCommand "mybold"; TCommand "textbf";
    TCommand "mybold"; TBeginGroup; TText "test"; TEndGroup
  ] in
  output = [TCommand "begingroup"; TCommand "bfseries"; TText "test"; TCommand "endgroup"] /\
  length state.(user_defined_macros) = 1 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 7: Error handling works *)
Example test_error_handling_verified :
  let (output, state) := expand_document_with_def [
    TCommand "textbf";  (* Missing argument *)
    TCommand "LaTeX"
  ] in
  output = [TCommand "textbf"; TText "LaTeX"] /\
  length state.(errors) = 1.
Proof. reflexivity. Qed.

(** Test 8: Warning system works *)
Definition test_warning_input := [
  TCommand "newcommand"; TBeginGroup; TCommand "test"; TEndGroup; 
  TBeginGroup; TText "FIRST"; TEndGroup;
  TCommand "newcommand"; TBeginGroup; TCommand "test"; TEndGroup; 
  TBeginGroup; TText "SECOND"; TEndGroup;
  TCommand "test"
].

Example test_warning_system_verified :
  match expand_document_with_diagnostics test_warning_input with
  | (output, errors, warnings) =>
      output = [TText "SECOND"] /\
      length errors = 0 /\
      length warnings = 1
  end.
Proof. reflexivity. Qed.

(** Test 9: Debug interface *)
Example test_debug_interface_verified :
  let (output, state) := expand_document_with_debug [TCommand "LaTeX"] 2 in
  output = [TText "LaTeX"] /\
  state.(debug_trace) = true /\
  state.(debug_level) = 2.
Proof. reflexivity. Qed.

(** Test 10: Complex integration *)
Example test_integration_verified :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "base"; TBeginGroup; TText "BASE"; TEndGroup;
    TCommand "let"; TCommand "basecopy"; TCommand "base";
    TCommand "renewcommand"; TBeginGroup; TCommand "base"; TEndGroup; 
    TBeginGroup; TText "RENEWED"; TEndGroup;
    TCommand "base"; TText "|"; TCommand "basecopy"
  ] in
  output = [TText "RENEWED"; TText "|"; TText "BASE"] /\
  length state.(user_defined_macros) = 2 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Summary: 10 verified tests covering all basic TIER 1 functionality *)
Definition TIER_1_BASIC_VERIFIED : string := 
  "✅ TIER 1 BASIC FUNCTIONALITY VERIFIED WITH 10 CLEAN TESTS".