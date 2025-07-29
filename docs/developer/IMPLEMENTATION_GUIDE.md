# L1 Expander Implementation Guide

**Purpose**: Step-by-step coding instructions for implementing the L1 Verified Macro Expander  
**Target**: Developers continuing the LaTeX Perfectionist v24 project  
**Prerequisites**: Understanding of Coq, LaTeX tokenization, and project architecture  
**Last Updated**: 2025-07-21  

---

## QUICK START CHECKLIST

Before you begin:
- [ ] Read `docs/MASTER_ARCHITECTURE.md` 
- [ ] Read `docs/LAYER_L1_SPECIFICATION.md`
- [ ] Verify L0 Lexer is working: `make -C src/core/lexer test`
- [ ] Check current working directory is `/src/core/expander`
- [ ] Confirm you understand the three proof targets

---

## STEP 1: SET UP FILE STRUCTURE

### Create Required Files
```bash
# From project root
cd src/core/expander
touch Layer02Verified.v
touch MacroCatalog.v  
touch ExpanderTypes.v
touch ExpanderAlgorithm.v
touch ExpanderProofs.v
touch ExpanderTests.v
```

### Update Build Configuration
Add to `_CoqProject`:
```
src/core/expander/ExpanderTypes.v
src/core/expander/MacroCatalog.v
src/core/expander/ExpanderAlgorithm.v
src/core/expander/ExpanderTests.v
src/core/expander/ExpanderProofs.v
src/core/expander/Layer02Verified.v
```

---

## STEP 2: IMPLEMENT EXPANDERTYPES.V

This file defines all data types used by the expander.

### Required Imports
```coq
From Coq Require Import String List Bool Arith.
From LaTeX Require Import LatexLexer.  (* for latex_token *)
```

### Core Data Types
```coq
(* Macro definition storage *)
Record macro_definition := {
  macro_name : string;
  macro_body : list latex_token;
  is_builtin : bool
}.

(* Expansion state *)
Record exp_state := {
  macro_definitions : list macro_definition;
  expansion_depth   : nat;
  call_stack       : list string;
  max_expansions   : nat;
  token_growth     : nat;
  macro_calls      : nat
}.

(* Expansion results *)
Inductive expand_error :=
  | MacroNotFound : string -> expand_error
  | RecursionLimit : string -> expand_error
  | MalformedMacro : string -> expand_error
  | TokenGrowthLimit : expand_error  
  | MacroCallLimit : expand_error.

Inductive expand_result := 
  | ExpandSuccess : list latex_token -> expand_result
  | ExpandError   : expand_error -> expand_result.
```

### Helper Functions
```coq
(* Initial state *)
Definition init_exp_state : exp_state := {|
  macro_definitions := [];
  expansion_depth   := 0;
  call_stack       := [];
  max_expansions   := 32;
  token_growth     := 0;
  macro_calls      := 0
|}.

(* State update functions *)
Definition increment_depth (st : exp_state) : exp_state :=
  {| st with expansion_depth := S st.(expansion_depth) |}.

Definition push_call (st : exp_state) (cmd : string) : exp_state :=
  {| st with call_stack := cmd :: st.(call_stack) |}.

Definition increment_calls (st : exp_state) : exp_state :=
  {| st with macro_calls := S st.(macro_calls) |}.

(* Limit checking *)
Definition exceeds_depth_limit (st : exp_state) : bool :=
  st.(expansion_depth) >=? st.(max_expansions).

Definition exceeds_token_limit (st : exp_state) (new_tokens : nat) : bool :=
  (st.(token_growth) + new_tokens) >? 8192.

Definition exceeds_call_limit (st : exp_state) : bool :=
  st.(macro_calls) >=? 512.
```

**Critical**: Compile and test this file before proceeding:
```bash
coqc -I ../lexer -I . ExpanderTypes.v
```

---

## STEP 3: IMPLEMENT MACROCATALOG.V

This file contains the 76 built-in macro definitions.

### Structure
```coq
From Coq Require Import String List.
From LaTeX Require Import LatexLexer ExpanderTypes.

(* Typography macros *)
Definition latex_macro : macro_definition := {|
  macro_name := "LaTeX";
  macro_body := [TText "LaTeX"];
  is_builtin := true
|}.

Definition tex_macro : macro_definition := {|
  macro_name := "TeX";  
  macro_body := [TText "TeX"];
  is_builtin := true
|}.

Definition ldots_macro : macro_definition := {|
  macro_name := "ldots";
  macro_body := [TText "…"];
  is_builtin := true
|}.

(* Mathematical macros *)
Definition alpha_macro : macro_definition := {|
  macro_name := "alpha";
  macro_body := [TText "α"];
  is_builtin := true
|}.

Definition beta_macro : macro_definition := {|
  macro_name := "beta";
  macro_body := [TText "β"];
  is_builtin := true
|}.

(* Continue for all 76 macros... *)

(* Complete catalog *)
Definition builtin_macros : list macro_definition := [
  latex_macro; tex_macro; ldots_macro; alpha_macro; beta_macro;
  (* Add all 76 macros here *)
].

(* Lookup function *)
Fixpoint lookup_builtin (name : string) : option (list latex_token) :=
  match builtin_macros with
  | [] => None
  | m :: rest => 
      if String.eqb name m.(macro_name) then
        Some m.(macro_body)
      else
        lookup_builtin name rest
  end.
```

**Implementation Strategy**: Start with 5-10 macros, test compilation, then incrementally add the rest.

---

## STEP 4: IMPLEMENT EXPANDERALGORITHM.V

This is the core expansion logic.

### Core Expansion Function
```coq
From Coq Require Import String List Bool Arith.
From LaTeX Require Import LatexLexer ExpanderTypes MacroCatalog.

(* Cycle detection *)
Fixpoint in_call_stack (stack : list string) (cmd : string) : bool :=
  match stack with
  | [] => false
  | x :: rest => String.eqb cmd x || in_call_stack rest cmd
  end.

(* Main expansion with fuel for termination *)
Program Fixpoint expand_with_fuel (fuel : nat) (st : exp_state) 
  (tokens : list latex_token) {measure fuel} : expand_result :=
  match fuel with
  | O => ExpandError (RecursionLimit "fuel exhausted")
  | S fuel' =>
      match tokens with
      | [] => ExpandSuccess []
      | TCommand cmd :: rest =>
          if exceeds_call_limit st then
            ExpandError MacroCallLimit
          else if in_call_stack st.(call_stack) cmd then
            ExpandError (RecursionLimit cmd)
          else
            match lookup_builtin cmd with
            | Some body =>
                let new_st := increment_calls (push_call st cmd) in
                if exceeds_token_limit new_st (length body) then
                  ExpandError TokenGrowthLimit
                else
                  match expand_with_fuel fuel' new_st (body ++ rest) with
                  | ExpandSuccess result => ExpandSuccess result
                  | err => err
                  end
            | None => ExpandError (MacroNotFound cmd)
            end
      | tok :: rest =>
          match expand_with_fuel fuel' st rest with
          | ExpandSuccess expanded => ExpandSuccess (tok :: expanded)
          | err => err
          end
      end
  end.

(* Main expansion function *)
Definition expand (st : exp_state) (tokens : list latex_token) : expand_result :=
  expand_with_fuel 1000 st tokens.
```

### Required Fuel Calculation
```coq
(* Calculate minimum fuel needed *)
Fixpoint count_commands (tokens : list latex_token) : nat :=
  match tokens with
  | [] => 0
  | TCommand _ :: rest => S (count_commands rest)  
  | _ :: rest => count_commands rest
  end.

Definition required_fuel (st : exp_state) (tokens : list latex_token) : nat :=
  (count_commands tokens) * st.(max_expansions).
```

---

## STEP 5: IMPLEMENT BASIC TESTS

Create `ExpanderTests.v` to verify your implementation works:

```coq
From Coq Require Import String List Bool.
From LaTeX Require Import LatexLexer ExpanderTypes MacroCatalog ExpanderAlgorithm.

(* Test basic LaTeX macro *)
Example test_latex_expansion :
  expand init_exp_state [TCommand "LaTeX"] = 
  ExpandSuccess [TText "LaTeX"].
Proof. simpl. reflexivity. Qed.

(* Test unknown macro *)  
Example test_unknown_macro :
  expand init_exp_state [TCommand "unknown"] =
  ExpandError (MacroNotFound "unknown").
Proof. simpl. reflexivity. Qed.

(* Test mixed content *)
Example test_mixed_content :
  expand init_exp_state [TText "Hello "; TCommand "LaTeX"; TText " world"] =
  ExpandSuccess [TText "Hello "; TText "LaTeX"; TText " world"].
Proof. simpl. reflexivity. Qed.
```

**Critical**: Verify tests pass before continuing:
```bash
coqc -I ../lexer -I . ExpanderTests.v
```

---

## STEP 6: IMPLEMENT THE THREE PROOF TARGETS

Create `ExpanderProofs.v`:

### Proof 1: expand_fuel_insensitive

```coq
(* Helper lemmas first *)
Lemma expand_fuel_monotonic : forall fuel1 fuel2 st tokens result,
  fuel1 <= fuel2 ->
  expand_with_fuel fuel1 st tokens = ExpandSuccess result ->
  expand_with_fuel fuel2 st tokens = ExpandSuccess result.
Proof.
  (* Proof by strong induction on fuel1 *)
  induction fuel1 as [fuel1 IH] using lt_wf_ind.
  intros fuel2 st tokens result Hle Hexp.
  (* Cases on fuel1 *)
  destruct fuel1 as [|fuel1'].
  - (* fuel1 = 0 *)
    simpl in Hexp. discriminate.
  - (* fuel1 = S fuel1' *)
    destruct fuel2 as [|fuel2'].
    + (* fuel2 = 0, but fuel1 > 0 and fuel1 <= fuel2 *)
      simpl in Hle. omega.
    + (* Both > 0, analyze expansion step *)
      simpl in Hexp |- *.
      (* Continue with case analysis... *)
Admitted. (* Complete this proof *)

(* Main theorem *)
Theorem expand_fuel_insensitive : forall st tokens fuel1 fuel2 result,
  fuel1 >= required_fuel st tokens ->
  fuel2 >= required_fuel st tokens ->
  expand_with_fuel fuel1 st tokens = ExpandSuccess result ->
  expand_with_fuel fuel2 st tokens = ExpandSuccess result.
Proof.
  intros st tokens fuel1 fuel2 result Hf1 Hf2 Hexp.
  apply expand_fuel_monotonic with fuel1.
  - omega.
  - exact Hexp.
Qed.
```

### Proof 2: expand_terminates_acyclic

```coq
(* Define acyclic predicate *)
Definition acyclic_macros (st : exp_state) : Prop :=
  forall cmd body, 
    lookup_builtin cmd = Some body ->
    ~ In (TCommand cmd) body.

(* LaTeX epsilon validity *)
Definition valid_latex_epsilon (tokens : list latex_token) : Prop :=
  forall cmd, In (TCommand cmd) tokens -> cmd <> cmd. (* Placeholder - refine this *)

Theorem expand_terminates_acyclic : forall st tokens,
  acyclic_macros st ->
  valid_latex_epsilon tokens ->
  exists result, expand st tokens = result /\ 
                 match result with ExpandError (RecursionLimit _) => False | _ => True end.
Proof.
  intros st tokens Hacyclic Hvalid.
  exists (expand st tokens).
  split.
  - reflexivity.
  - (* Prove no recursion limit error *)
    unfold expand.
    (* Use well-founded induction on expansion depth *)
Admitted. (* Complete this proof *)
```

### Proof 3: expand_no_teof  

```coq
(* Helper: builtin macros don't produce TEOF *)
Lemma builtins_no_teof : forall cmd body,
  lookup_builtin cmd = Some body ->
  ~ In TEOF body.
Proof.
  intros cmd body Hlookup.
  (* Examine all builtin macro bodies *)
  unfold lookup_builtin in Hlookup.
  (* Case analysis on builtin_macros list *)
Admitted. (* Complete by checking each builtin *)

Theorem expand_no_teof : forall st tokens result,
  expand st tokens = ExpandSuccess result ->
  ~ In TEOF tokens ->
  ~ In TEOF result.
Proof.
  intros st tokens result Hexp Hno_teof.
  unfold expand in Hexp.
  (* Induction on expansion steps *)
  (* Use builtins_no_teof lemma *)
Admitted. (* Complete this proof *)
```

---

## STEP 7: CREATE MAIN LAYER02VERIFIED.V

This file ties everything together:

```coq
From Coq Require Import String List Bool Arith.
From LaTeX Require Import LatexLexer.

(* Re-export all components *)
From LaTeX Require Export ExpanderTypes MacroCatalog ExpanderAlgorithm ExpanderProofs.

(* Main interface for other layers *)
Definition expand_tokens := expand.

(* Verification summary *)
Check expand_fuel_insensitive.
Check expand_terminates_acyclic. 
Check expand_no_teof.

(* Usage example *)
Example usage_example :
  let tokens := [TCommand "LaTeX"; TText " is great!"] in
  expand init_exp_state tokens = ExpandSuccess [TText "LaTeX"; TText " is great!"].
Proof. simpl. reflexivity. Qed.
```

---

## STEP 8: INTEGRATION AND TESTING

### Compile Everything
```bash
# From src/core/expander
make clean
make all

# Should show:
# - 0 axioms
# - 0 admits  
# - All files compile successfully
```

### Integration Test with L0
```coq
(* In a test file *)
From LaTeX Require Import LatexLexer Layer02Verified.

Example full_pipeline_test :
  let input := "Hello \LaTeX\ world!" in
  let tokens := lex input in
  match expand init_exp_state tokens with
  | ExpandSuccess result => 
      result = [TText "Hello "; TText "LaTeX"; TText " world!"]
  | ExpandError _ => False
  end.
Proof. simpl. reflexivity. Qed.
```

---

## COMMON IMPLEMENTATION ISSUES

### Issue 1: "Nothing to inject" Error
**Cause**: Complex pattern matching in match statements  
**Solution**: Break complex matches into separate functions:
```coq
(* Instead of complex nested match *)
Definition handle_command (st : exp_state) (cmd : string) : expand_result :=
  if exceeds_call_limit st then ExpandError MacroCallLimit
  else match lookup_builtin cmd with
       | Some body => (* handle expansion *)
       | None => ExpandError (MacroNotFound cmd)
       end.
```

### Issue 2: Termination Issues
**Cause**: Coq can't prove termination automatically  
**Solution**: Use Program Fixpoint with explicit measure:
```coq
Program Fixpoint my_function (input : list A) {measure (length input)} : result :=
  match input with
  | [] => base_case
  | x :: xs => (* recursive case with xs *)
  end.
```

### Issue 3: Import/Module Issues  
**Cause**: Circular dependencies or missing imports  
**Solution**: Check dependency order in `_CoqProject`, use qualified imports:
```coq
From LaTeX Require Import LatexLexer.
From LaTeX Require ExpanderTypes.  (* Import without adding to namespace *)
```

---

## DEBUGGING CHECKLIST

When compilation fails:
1. [ ] Check all files compile individually
2. [ ] Verify import statements are correct
3. [ ] Ensure `_CoqProject` lists files in dependency order
4. [ ] Check for typos in function/type names
5. [ ] Verify all `match` statements are exhaustive
6. [ ] Check that all `Fixpoint` functions have proper termination

When proofs fail:
1. [ ] Use `Check` commands to verify theorem statements
2. [ ] Add intermediate lemmas for complex proofs
3. [ ] Use `simpl`, `unfold`, `destruct` to explore proof state
4. [ ] Check that helper functions have needed properties
5. [ ] Verify examples work before attempting proofs

---

## SUCCESS CRITERIA

Your implementation is ready when:
- [ ] All files compile with 0 errors, 0 warnings
- [ ] `Check expand_fuel_insensitive.` succeeds
- [ ] `Check expand_terminates_acyclic.` succeeds  
- [ ] `Check expand_no_teof.` succeeds
- [ ] No `Axiom` or `Admit` commands anywhere
- [ ] Test examples all pass
- [ ] Integration with L0 lexer works
- [ ] Performance limits are enforced

---

*This guide provides step-by-step implementation instructions. Follow each step carefully and test frequently. When you encounter issues, refer to the debugging section and the complete specifications in `LAYER_L1_SPECIFICATION.md`.*