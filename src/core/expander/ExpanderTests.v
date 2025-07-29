From Coq Require Import String List Bool.
Require Import lexer.LatexLexer.
Require Import ExpanderTypes MacroCatalog ExpanderAlgorithm.
Import ListNotations.
Open Scope string_scope.

(** * LaTeX Perfectionist v24 - Expander Tests
    
    Basic tests to verify the L1 Expander implementation works correctly.
    Following IMPLEMENTATION_GUIDE.md Step 5.
    
    Status: 0 axioms, 0 admits required
*)

(** ** Test basic LaTeX macro *)
Example test_latex_expansion :
  expand init_exp_state (TCommand "LaTeX" :: nil) = 
  ExpandSuccess (TText "LaTeX" :: nil).
Proof. simpl. reflexivity. Qed.

(** ** Test TeX macro *)
Example test_tex_expansion :
  expand init_exp_state (TCommand "TeX" :: nil) = 
  ExpandSuccess (TText "TeX" :: nil).
Proof. simpl. reflexivity. Qed.

(** ** Test unknown macro *)  
Example test_unknown_macro :
  expand init_exp_state (TCommand "unknown" :: nil) =
  ExpandError (MacroNotFound "unknown").
Proof. simpl. reflexivity. Qed.

(** ** Test mixed content *)
Example test_mixed_content :
  expand init_exp_state (TText "Hello " :: TCommand "LaTeX" :: TText " world" :: nil) =
  ExpandSuccess (TText "Hello " :: TText "LaTeX" :: TText " world" :: nil).
Proof. simpl. reflexivity. Qed.

(** ** Test mathematical symbols *)
Example test_alpha_expansion :
  expand init_exp_state (TCommand "alpha" :: nil) = 
  ExpandSuccess (TText "α" :: nil).
Proof. simpl. reflexivity. Qed.

Example test_infty_expansion :
  expand init_exp_state (TCommand "infty" :: nil) = 
  ExpandSuccess (TText "∞" :: nil).
Proof. simpl. reflexivity. Qed.

(** ** Test empty input *)
Example test_empty_input :
  expand init_exp_state nil = ExpandSuccess nil.
Proof. simpl. reflexivity. Qed.

(** ** Test non-command tokens pass through *)
Example test_passthrough :
  expand init_exp_state (TText "hello" :: TSpace :: TNewline :: nil) =
  ExpandSuccess (TText "hello" :: TSpace :: TNewline :: nil).
Proof. simpl. reflexivity. Qed.

(** ** Test cycle detection (artificial case) *)
(* Note: This test may need adjustment based on actual cycle detection implementation *)
Example test_cycle_detection_example :
  let st := {| macro_definitions := init_exp_state.(macro_definitions);
               expansion_depth   := init_exp_state.(expansion_depth);
               call_stack       := "test" :: nil;
               max_expansions   := init_exp_state.(max_expansions);
               token_growth     := init_exp_state.(token_growth);
               macro_calls      := init_exp_state.(macro_calls) |} in
  expand st (TCommand "test" :: nil) = ExpandError (RecursionLimit "test").
Proof. simpl. reflexivity. Qed.

(** ** Test call limit (simplified) *)
Example test_call_limit_check :
  let st := {| macro_definitions := init_exp_state.(macro_definitions);
               expansion_depth   := init_exp_state.(expansion_depth);
               call_stack       := init_exp_state.(call_stack);
               max_expansions   := init_exp_state.(max_expansions);
               token_growth     := init_exp_state.(token_growth);
               macro_calls      := 512 |} in
  expand st (TCommand "LaTeX" :: nil) = ExpandError MacroCallLimit.
Proof. simpl. reflexivity. Qed.