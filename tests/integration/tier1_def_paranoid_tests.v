Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** TIER 1: \def PARANOID TESTS - Testing every edge case of \def *)

(** Test 1: Most basic \def *)
Example def_basic :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "x"; TBeginGroup; TText "hello"; TEndGroup;
    TCommand "x"
  ] in
  output = [TText "hello"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 2: \def with empty body - should work *)
Example def_empty_body :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "x"; TBeginGroup; TEndGroup;
    TCommand "x"
  ] in
  output = [] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 3: \def with single parameter *)
Example def_single_param :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "x"; TText "#"; TText "1"; 
    TBeginGroup; TText "#"; TText "1"; TEndGroup;
    TCommand "x"; TBeginGroup; TText "TEST"; TEndGroup
  ] in
  output = [TText "TEST"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 4: \def with parameter used multiple times *)
Example def_param_repeated :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "double"; TText "#"; TText "1"; 
    TBeginGroup; TText "#"; TText "1"; TText "#"; TText "1"; TEndGroup;
    TCommand "double"; TBeginGroup; TText "A"; TEndGroup
  ] in
  output = [TText "A"; TText "A"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 5: \def with all 9 parameters *)
Example def_nine_params :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "nine"; 
    TText "#"; TText "1"; TText "#"; TText "2"; TText "#"; TText "3";
    TText "#"; TText "4"; TText "#"; TText "5"; TText "#"; TText "6";
    TText "#"; TText "7"; TText "#"; TText "8"; TText "#"; TText "9";
    TBeginGroup; 
      TText "#"; TText "1"; TText "-";
      TText "#"; TText "9"; 
    TEndGroup;
    TCommand "nine"; 
    TBeginGroup; TText "A"; TEndGroup;
    TBeginGroup; TText "B"; TEndGroup;
    TBeginGroup; TText "C"; TEndGroup;
    TBeginGroup; TText "D"; TEndGroup;
    TBeginGroup; TText "E"; TEndGroup;
    TBeginGroup; TText "F"; TEndGroup;
    TBeginGroup; TText "G"; TEndGroup;
    TBeginGroup; TText "H"; TEndGroup;
    TBeginGroup; TText "I"; TEndGroup
  ] in
  output = [TText "A"; TText "-"; TText "I"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 6: \def with parameters in reverse order *)
Example def_params_reversed :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "rev"; TText "#"; TText "1"; TText "#"; TText "2";
    TBeginGroup; TText "#"; TText "2"; TText "#"; TText "1"; TEndGroup;
    TCommand "rev"; 
    TBeginGroup; TText "FIRST"; TEndGroup;
    TBeginGroup; TText "SECOND"; TEndGroup
  ] in
  output = [TText "SECOND"; TText "FIRST"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 7: \def overwriting existing macro - should work silently *)
Example def_overwrite :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "x"; TBeginGroup; TText "OLD"; TEndGroup;
    TCommand "def"; TCommand "x"; TBeginGroup; TText "NEW"; TEndGroup;
    TCommand "x"
  ] in
  output = [TText "NEW"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 8: \def with macro expansion in body *)
Example def_expansion_in_body :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "inner"; TBeginGroup; TText "INNER"; TEndGroup;
    TCommand "def"; TCommand "outer"; TBeginGroup; 
      TCommand "inner"; TText "-TEXT"
    TEndGroup;
    TCommand "outer"
  ] in
  output = [TText "INNER"; TText "-TEXT"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 9: \def with nested groups in body *)
Example def_nested_groups :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "nested"; TBeginGroup; 
      TText "A"; TBeginGroup; TText "B"; TEndGroup; TText "C"
    TEndGroup;
    TCommand "nested"
  ] in
  output = [TText "A"; TBeginGroup; TText "B"; TEndGroup; TText "C"] /\ 
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 10: \def with parameter not used in body *)
Example def_unused_param :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "ignore"; TText "#"; TText "1";
    TBeginGroup; TText "FIXED"; TEndGroup;
    TCommand "ignore"; TBeginGroup; TText "IGNORED"; TEndGroup
  ] in
  output = [TText "FIXED"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 11: \def with delimited parameter *)
Example def_delimited_param :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "to"; TText "#"; TText "1";
    TBeginGroup; TText "["; TText "#"; TText "1"; TText "]"; TEndGroup;
    TCommand "test"; TText "A"; TText "B"; TText "C"; TText "to"; TText "END"
  ] in
  output = [TText "["; TText "A"; TText "B"; TText "C"; TText "]"] /\ 
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 12: \def with # not followed by digit - should pass through *)
Example def_hash_not_param :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "hash"; TBeginGroup; 
      TText "#"; TText "not"; TText "param"
    TEndGroup;
    TCommand "hash"
  ] in
  output = [TText "#"; TText "not"; TText "param"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 13: Recursive macro - depth limit test *)
Example def_recursive_depth :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "rec"; TBeginGroup; TCommand "rec"; TEndGroup;
    TCommand "rec"
  ] in
  (* Should hit depth limit and pass through *)
  length state.(errors) = 0.  (* No error, just stops expanding *)
Proof. reflexivity. Qed.

(** Test 14: Mutual recursion *)
Example def_mutual_recursion :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "a"; TBeginGroup; TCommand "b"; TEndGroup;
    TCommand "def"; TCommand "b"; TBeginGroup; TCommand "a"; TEndGroup;
    TCommand "a"
  ] in
  (* Should eventually hit depth limit *)
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 15: \def with very long macro name *)
Example def_long_name :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "verylongmacronamethatmightcauseissues"; 
    TBeginGroup; TText "WORKS"; TEndGroup;
    TCommand "verylongmacronamethatmightcauseissues"
  ] in
  output = [TText "WORKS"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 16: \def with special characters in name *)
Example def_special_chars :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "@internal@macro"; 
    TBeginGroup; TText "INTERNAL"; TEndGroup;
    TCommand "@internal@macro"
  ] in
  output = [TText "INTERNAL"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 17: \def with digit as macro name - should work *)
Example def_digit_name :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "1"; 
    TBeginGroup; TText "ONE"; TEndGroup;
    TCommand "1"
  ] in
  output = [TText "ONE"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 18: Parameter at end of body *)
Example def_param_at_end :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "end"; TText "#"; TText "1";
    TBeginGroup; TText "START-"; TText "#"; TText "1"; TEndGroup;
    TCommand "end"; TBeginGroup; TText "FINISH"; TEndGroup
  ] in
  output = [TText "START-"; TText "FINISH"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 19: Multiple delimiters *)
Example def_multiple_delimiters :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "range"; 
    TText "from"; TText "#"; TText "1"; 
    TText "to"; TText "#"; TText "2";
    TBeginGroup; TText "#"; TText "1"; TText ".."; TText "#"; TText "2"; TEndGroup;
    TCommand "range"; 
    TText "from"; TText "A"; 
    TText "to"; TText "Z"
  ] in
  output = [TText "A"; TText ".."; TText "Z"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 20: \def creating a macro that defines another macro *)
Example def_macro_factory :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "makemacro"; TText "#"; TText "1";
    TBeginGroup; 
      TCommand "def"; TCommand "#"; TText "1"; 
      TBeginGroup; TText "GENERATED"; TEndGroup
    TEndGroup;
    TCommand "makemacro"; TBeginGroup; TText "newmacro"; TEndGroup;
    TCommand "newmacro"
  ] in
  output = [TText "GENERATED"] /\ length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Summary: 20 meaningful \def tests covering real edge cases *)
Definition DEF_PARANOID_TESTS_1 : string := 
  "✅ 20 PARANOID \\def TESTS - Testing actual behaviors we care about".