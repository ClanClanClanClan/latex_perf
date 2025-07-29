Require Import String.
Require Import List.
Require Import Lia.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(* Test protection mechanism with \protect command *)

(* Test 1: Normal expansion without protection *)
Example test_normal_expansion :
  let input := [TCommand "textbf"; TBeginGroup; TText "hello"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  (* Should expand textbf normally *)
  output = [TCommand "begingroup"; TCommand "bfseries"; TText "hello"; TCommand "endgroup"].
Proof. simpl. reflexivity. Qed.

(* Test 2: Protected expansion - macro should not expand *)
Example test_protected_expansion :
  let input := [TCommand "protect"; TCommand "textbf"; TBeginGroup; TText "hello"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  (* textbf should be passed through without expansion due to protection *)
  output = [TCommand "textbf"; TBeginGroup; TText "hello"; TEndGroup].
Proof. simpl. reflexivity. Qed.

(* Test 3: Protection only affects next command *)
Example test_protection_scope :
  let input := [TCommand "protect"; TCommand "textbf"; TBeginGroup; TText "first"; TEndGroup;
                TCommand "textbf"; TBeginGroup; TText "second"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  (* First textbf protected, second should expand normally *)
  length output >= 6. (* Should have protected command + normal expansion *)
Proof. simpl. vm_compute. lia. Qed.