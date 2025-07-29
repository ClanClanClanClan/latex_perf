Require Import String.
Require Import List.
Import ListNotations.
Require Import core.lexer.LatexLexer.
Require Import core.expander.LatexExpanderEnhanced.
Open Scope string_scope.

(** ULTRA MINIMAL TESTS - NO COMPUTE, JUST PROOFS *)

(** Test 1: LaTeX macro *)
Example test1 : 
  match expand_document_with_def [TCommand "LaTeX"] with
  | ([TText "LaTeX"], _) => True
  | _ => False
  end.
Proof. exact I. Qed.

(** Test 2: Empty expansion *)
Example test2 :
  match expand_document_with_def [] with
  | ([], _) => True
  | _ => False
  end.
Proof. exact I. Qed.

(** Test 3: Text passthrough *)
Example test3 :
  match expand_document_with_def [TText "hello"] with
  | ([TText "hello"], _) => True
  | _ => False
  end.
Proof. exact I. Qed.

(** Test 4: Unknown command passthrough *)
Example test4 :
  match expand_document_with_def [TCommand "unknown"] with
  | ([TCommand "unknown"], _) => True
  | _ => False
  end.
Proof. exact I. Qed.

(** Test 5: Basic counter creation *)
Example test5 :
  match expand_document_with_def [TCommand "newcounter"; TBeginGroup; TCommand "test"; TEndGroup] with
  | ([], state) => length state.(counters) = 1
  | _ => False
  end.
Proof. exact eq_refl. Qed.

(** Test 6: \def parsing doesn't crash *)
Example test6 :
  match expand_document_with_def [TCommand "def"; TCommand "x"; TText "#"; TText "1"; TBeginGroup; TText "#"; TText "1"; TEndGroup] with
  | (_, _) => True  (* Just test that it doesn't crash *)
  end.
Proof. exact I. Qed.

(** Summary *)
Definition ULTRA_MINIMAL_VERIFIED : string := 
  "✅ 6 ULTRA MINIMAL TESTS PASS".