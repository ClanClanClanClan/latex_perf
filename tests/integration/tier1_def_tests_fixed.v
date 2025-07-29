Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** TIER 1: \def PARANOID TESTS - Using vm_compute to avoid timeouts *)

(** Helper to pre-compute results *)
Ltac test_expansion input expected :=
  let result := eval vm_compute in (fst (expand_document_with_def input)) in
  match result with
  | expected => exact I
  | _ => fail "Expansion did not match expected output"
  end.

(** Test 1: Most basic \def *)
Example def_basic : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "x"; TBeginGroup; TText "hello"; TEndGroup; TCommand "x"]
    [TText "hello"].
Qed.

(** Test 2: \def with empty body *)
Example def_empty_body : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "x"; TBeginGroup; TEndGroup; TCommand "x"]
    (@nil latex_token).
Qed.

(** Test 3: \def with single parameter *)
Example def_single_param : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "x"; TText "#"; TText "1"; 
     TBeginGroup; TText "#"; TText "1"; TEndGroup;
     TCommand "x"; TBeginGroup; TText "TEST"; TEndGroup]
    [TText "TEST"].
Qed.

(** Test 4: \def with parameter used multiple times *)
Example def_param_repeated : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "double"; TText "#"; TText "1"; 
     TBeginGroup; TText "#"; TText "1"; TText "#"; TText "1"; TEndGroup;
     TCommand "double"; TBeginGroup; TText "A"; TEndGroup]
    [TText "A"; TText "A"].
Qed.

(** Test 5: \def with parameters in reverse order *)
Example def_params_reversed : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "rev"; TText "#"; TText "1"; TText "#"; TText "2";
     TBeginGroup; TText "#"; TText "2"; TText "#"; TText "1"; TEndGroup;
     TCommand "rev"; TBeginGroup; TText "FIRST"; TEndGroup; TBeginGroup; TText "SECOND"; TEndGroup]
    [TText "SECOND"; TText "FIRST"].
Qed.

(** Test 6: \def overwriting existing macro *)
Example def_overwrite : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "x"; TBeginGroup; TText "OLD"; TEndGroup;
     TCommand "def"; TCommand "x"; TBeginGroup; TText "NEW"; TEndGroup;
     TCommand "x"]
    [TText "NEW"].
Qed.

(** Test 7: \def with macro expansion in body *)
Example def_expansion_in_body : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "inner"; TBeginGroup; TText "INNER"; TEndGroup;
     TCommand "def"; TCommand "outer"; TBeginGroup; TCommand "inner"; TText "-TEXT"; TEndGroup;
     TCommand "outer"]
    [TText "INNER"; TText "-TEXT"].
Qed.

(** Test 8: \def with parameter at end *)
Example def_param_at_end : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "end"; TText "#"; TText "1";
     TBeginGroup; TText "START-"; TText "#"; TText "1"; TEndGroup;
     TCommand "end"; TBeginGroup; TText "FINISH"; TEndGroup]
    [TText "START-"; TText "FINISH"].
Qed.

(** Test 9: \def with unused parameter *)
Example def_unused_param : True.
Proof.
  test_expansion
    [TCommand "def"; TCommand "ignore"; TText "#"; TText "1";
     TBeginGroup; TText "FIXED"; TEndGroup;
     TCommand "ignore"; TBeginGroup; TText "IGNORED"; TEndGroup]
    [TText "FIXED"].
Qed.

(** Test 10: Built-in macro expansion *)
Example builtin_latex : True.
Proof.
  test_expansion
    [TCommand "LaTeX"]
    [TText "LaTeX"].
Qed.

(** Summary: 10 core \def tests passing *)
Definition DEF_TESTS_VERIFIED : string := 
  "✅ 10 CORE \\def TESTS PASS WITH vm_compute".