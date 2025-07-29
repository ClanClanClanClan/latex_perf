Require Import String.
Require Import List.
Require Import Lia.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(* Test variable argument parsing with minimum and maximum counts *)

(* Test 1: Variable args with min=1, max=3 *)
Example test_variable_args_1_3 :
  let input := [TCommand "newcommand"; TBeginGroup; TCommand "vartest"; TEndGroup;
                TText "["; TText "1"; TText ","; TText "3"; TText "]";  (* Variable count 1-3 *)
                TBeginGroup; TText "Result:"; TText "#1"; TText "-"; TText "#2"; TText "-"; TText "#3"; TEndGroup;
                TCommand "vartest"; TBeginGroup; TText "A"; TEndGroup; 
                                   TBeginGroup; TText "B"; TEndGroup] in
  let (output, state) := expand_document_with_def input in
  (* Should work with 2 arguments (between min=1 and max=3) *)
  length state.(errors) = 0.
Proof. simpl. reflexivity. Qed.

(* Test 2: Variable args with insufficient arguments *)
Example test_variable_args_insufficient :
  let input := [TCommand "newcommand"; TBeginGroup; TCommand "needtwo"; TEndGroup;
                TText "["; TText "2"; TText ","; TText "4"; TText "]";  (* Variable count 2-4 *)
                TBeginGroup; TText "Got:"; TText "#1"; TText "+"; TText "#2"; TEndGroup;
                TCommand "needtwo"; TBeginGroup; TText "only_one"; TEndGroup] in  (* Only 1 arg, need 2+ *)
  let (output, state) := expand_document_with_def input in
  (* Should generate error for insufficient arguments *)
  length state.(errors) >= 1.
Proof. simpl. vm_compute. lia. Qed.

(* Test 3: Variable args with maximum satisfied *)
Example test_variable_args_maximum :
  let input := [TCommand "newcommand"; TBeginGroup; TCommand "upto3"; TEndGroup;
                TText "["; TText "0"; TText ","; TText "3"; TText "]";  (* Variable count 0-3 *)
                TBeginGroup; TText "Args:"; TText "#1"; TText "#2"; TText "#3"; TEndGroup;
                TCommand "upto3"; TBeginGroup; TText "A"; TEndGroup; 
                                 TBeginGroup; TText "B"; TEndGroup;
                                 TBeginGroup; TText "C"; TEndGroup;
                                 TBeginGroup; TText "D"; TEndGroup] in  (* 4 args, max is 3 *)
  let (output, state) := expand_document_with_def input in
  (* Should take first 3 arguments and leave 4th *)
  length state.(errors) = 0.
Proof. simpl. reflexivity. Qed.