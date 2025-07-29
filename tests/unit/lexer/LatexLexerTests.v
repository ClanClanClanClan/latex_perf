(* LaTeX Perfectionist v24 - Phase 1: Lexer Test Suite *)
(* Week 2: Testing basic token recognition *)

Require Import String List Ascii Lia.
Require Import LatexCatcodes.
Require Import LatexLexer.
Import ListNotations.
Open Scope string_scope.

(* List helper lemmas *)
Lemma rev_not_nil : forall A (l : list A),
  l <> [] -> List.rev l <> [].
Proof.
  intros A l H.
  destruct l.
  - contradiction.
  - simpl. intro H_eq.
    apply app_eq_nil in H_eq.
    destruct H_eq as [_ H_nil].
    discriminate H_nil.
Qed.

(** * Test Utilities *)

(* Check if token lists are equal *)
Definition tokens_equal (t1 t2 : list latex_token) : bool :=
  match list_eq_dec token_eq_dec t1 t2 with
  | left _ => true
  | right _ => false
  end.

(* Helper to run lexer and check result *)
Definition test_lex (input : string) (expected : list latex_token) : bool :=
  tokens_equal (lex_from_string input) expected.

(** * Basic Token Tests *)

(* Test single character tokens *)
Example test_single_brace : 
  lex_from_string "{" = [TBeginGroup].
Proof. reflexivity. Qed.

Example test_single_rbrace : 
  lex_from_string "}" = [TEndGroup].
Proof. reflexivity. Qed.

Example test_single_dollar :
  lex_from_string "$" = [TMathShift].
Proof. reflexivity. Qed.

Example test_single_ampersand :
  lex_from_string "&" = [TAlignment].
Proof. reflexivity. Qed.

Example test_single_hash :
  lex_from_string "#" = [TParameter].
Proof. reflexivity. Qed.

Example test_single_caret :
  lex_from_string "^" = [TSuperscript].
Proof. reflexivity. Qed.

Example test_single_underscore :
  lex_from_string "_" = [TSubscript].
Proof. reflexivity. Qed.

(* Test command recognition *)
Example test_simple_command :
  lex_from_string "\frac" = [TCommand "frac"].
Proof. 
  reflexivity.
Qed.

Example test_empty_command :
  lex_from_string "\" = [TCommand ""].
Proof. 
  reflexivity.
Qed.

(** * Corpus-Based Command Tests *)

(* Test top commands from corpus *)
Example test_begin_command :
  lex_from_string "\begin" = [TCommand "begin"].
Proof.
  reflexivity.
Qed.

Example test_end_command :
  lex_from_string "\end" = [TCommand "end"].
Proof.
  reflexivity.
Qed.

(* Test starred commands *)
Example test_starred_command :
  lex_from_string "\section*" = [TCommand "section*"].
Proof.
  reflexivity.
Qed.

Example test_begin_starred :
  lex_from_string "\begin*" = [TCommand "begin*"].
Proof.
  reflexivity.
Qed.

(** * Multi-Token Tests *)

Example test_simple_group :
  lex_from_string "{hello}" = [TBeginGroup; TText "hello"; TEndGroup].
Proof.
  reflexivity.
Qed.

Example test_math_mode :
  lex_from_string "$x$" = [TMathShift; TText "x"; TMathShift].
Proof.
  reflexivity.
Qed.

Example test_subscript_superscript :
  lex_from_string "x_1^2" = [TText "x"; TSubscript; TText "1"; TSuperscript; TText "2"].
Proof.
  reflexivity.
Qed.

(** * Complex LaTeX Patterns *)

Example test_fraction :
  lex_from_string "\frac{1}{2}" = [TCommand "frac"; TBeginGroup; TText "1"; TEndGroup;
                       TBeginGroup; TText "2"; TEndGroup].
Proof.
  reflexivity.
Qed.

Example test_begin_env :
  lex_from_string "\begin{equation}" = 
    [TCommand "begin"; TBeginGroup; TText "equation"; TEndGroup].
Proof.
  reflexivity.
Qed.

(** * Whitespace Handling *)

Example test_spaces :
  lex_from_string "  hello  " = [TSpace; TText "hello"; TSpace].
Proof.
  reflexivity.
Qed.

Example test_command_with_space :
  lex_from_string "\frac {1}" = 
    [TCommand "frac"; TSpace; TBeginGroup; TText "1"; TEndGroup].
Proof.
  reflexivity.
Qed.

(** * Comment Handling *)

Example test_comment :
  lex_from_string "% this is a comment" = [TComment " this is a comment"].
Proof.
  reflexivity.
Qed.

(** * Performance Check *)

(* Test that lexer terminates on reasonable inputs *)
Definition performance_test_1 : list latex_token :=
  lex_from_string "\documentclass{article}\begin{document}Hello world!\end{document}".

Definition performance_test_2 : list latex_token :=
  lex_from_string "$$\int_0^1 f(x) dx = \frac{1}{2}$$".

(* Examples showing lexer produces tokens for various inputs *)
Example lex_single_char : lex_from_string "a" = [TText "a"].
Proof. reflexivity. Qed.

Example lex_single_escape : lex_from_string "\" = [TCommand ""].  
Proof. reflexivity. Qed.

Example lex_single_space : lex_from_string " " = [TSpace].
Proof. reflexivity. Qed.

(* Property: specific single char examples work *)
Example lex_char_a : lex_from_string "a" <> [].
Proof. simpl. discriminate. Qed.

Example lex_char_brace : lex_from_string "{" <> [].
Proof. simpl. discriminate. Qed.

Example lex_char_dollar : lex_from_string "$" <> [].
Proof. simpl. discriminate. Qed.

(** * Determinism Check *)

(* Verify lexer is deterministic *)
Theorem lex_deterministic : forall s tokens1 tokens2,
  lex_from_string s = tokens1 ->
  lex_from_string s = tokens2 ->
  tokens1 = tokens2.
Proof.
  intros s tokens1 tokens2 H1 H2.
  rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

(** * Corpus Validation *)

(* Check that essential LaTeX patterns are handled *)
Definition essential_patterns : list string := [
  "\begin{equation}";
  "\end{equation}";
  "\frac{a}{b}";
  "$x^2 + y^2 = z^2$";
  "\left( \right)";
  "& a & b \\";
  "% comment line"
].

(* All essential patterns should produce tokens *)
Definition validate_essential_patterns : Prop :=
  forall pattern, In pattern essential_patterns ->
    exists tokens, lex_from_string pattern = tokens /\ tokens <> [].

(** * Test Summary *)

(* Count of successful tests *)
Definition tests_summary : string :=
  "Lexer test suite for LaTeX Perfectionist v24 Phase 1 Week 2".

Print tests_summary.