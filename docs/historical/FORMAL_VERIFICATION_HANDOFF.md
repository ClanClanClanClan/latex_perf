# LaTeX Perfectionist v24 - Layer-02 Formal Verification Handoff

## CRITICAL MISSION: Complete 3 Formal Verification Targets with 0 Axioms, 0 Admits

### **Current Status: 95% Complete - Blocked on Proof Infrastructure**

The Layer-02 Verified Macro Expander implementation is **functionally complete** but requires completion of **3 critical formal verification theorems** without any admits or axioms.

---

## 📋 **IMPLEMENTATION STATUS**

### ✅ **COMPLETED (Functional Implementation)**
- **6 core Coq files** implementing L1 Expander:
  - `src/core/expander/ExpanderTypes.v` - Data types, exp_state, expand_result
  - `src/core/expander/MacroCatalog.v` - All 76 built-in macros (LaTeX, TeX, α, β, etc.)
  - `src/core/expander/ExpanderAlgorithm.v` - Core expansion logic with fuel-based termination
  - `src/core/expander/ExpanderTests.v` - 10 test cases, all passing
  - `src/core/expander/Layer02Verified.v` - Main integration file
  - `src/core/expander/ExpanderProofs.v` - Initial proof attempts (contains admits)

### ⚠️ **BLOCKING ISSUES (Formal Verification)**
- **`src/core/expander/ExpanderProofsComplete.v`** - Contains 3 theorems with admits that MUST be completed

---

## 🎯 **EXACT PROOF TARGETS (MISSION CRITICAL)**

**YOU MUST COMPLETE THESE 3 THEOREMS WITHOUT ANY ADMITS:**

### **1. expand_fuel_insensitive** 
```coq
Theorem expand_fuel_insensitive : forall st tokens fuel1 fuel2 result,
  fuel1 >= required_fuel st tokens ->
  fuel2 >= required_fuel st tokens ->
  expand_with_fuel fuel1 st tokens = ExpandSuccess result ->
  expand_with_fuel fuel2 st tokens = ExpandSuccess result.
```

### **2. expand_terminates_acyclic**
```coq
Theorem expand_terminates_acyclic : forall st tokens,
  acyclic_macros st ->
  valid_latex_epsilon tokens ->
  exists result, expand st tokens = result /\
                 match result with ExpandError (RecursionLimit _) => False | _ => True end.
```

### **3. expand_no_teof**
```coq
Theorem expand_no_teof : forall st tokens result,
  expand st tokens = ExpandSuccess result ->
  ~ In TEOF tokens ->
  ~ In TEOF result.
```

---

## 🚨 **KEY TECHNICAL CHALLENGES**

### **Challenge 1: builtins_no_teof Lemma**
**PROBLEM:** The `expand_no_teof` theorem requires proving that builtin macro bodies don't contain `TEOF`.

**WHAT WAS TRIED:**
- Attempted structural case analysis on lookup_builtin results
- Tried to prove all 76 builtin macros have form `TText s :: nil`
- Got blocked on complex conditional tree expansion in Coq

**WHAT NEEDS TO BE DONE:**
```coq
Lemma builtins_no_teof : forall cmd body,
  lookup_builtin cmd = Some body ->
  ~ In TEOF body.
```

**APPROACH NEEDED:**
1. Prove that `lookup_builtin_aux` only returns macro bodies from `builtin_macros`
2. Prove that every macro in `builtin_macros` has body = `TText s :: nil`  
3. Use the fact that `TEOF ≠ TText s` (different constructors)

**KEY INSIGHT:** All 76 macros in `MacroCatalog.v` are defined as:
```coq
Definition macro_name_macro : macro_definition := {|
  macro_name := "name";
  macro_body := TText "output" :: nil;
  is_builtin := true
|}.
```

### **Challenge 2: Fuel Monotonicity**
**PROBLEM:** `expand_fuel_insensitive` requires proving fuel monotonicity.

**WHAT NEEDS TO BE PROVEN:**
```coq
Lemma expand_fuel_monotonic : forall fuel1 fuel2 st tokens result,
  fuel1 <= fuel2 ->
  expand_with_fuel fuel1 st tokens = ExpandSuccess result ->
  expand_with_fuel fuel2 st tokens = ExpandSuccess result.
```

**APPROACH NEEDED:**
1. Strong induction on `fuel1` using `lt_wf_ind`
2. Case analysis on the expansion algorithm structure
3. Handle recursive calls with proper fuel decrements

### **Challenge 3: Termination Under Acyclic Conditions**
**PROBLEM:** Proving that acyclic macros + valid input guarantees termination.

**KEY INSIGHT:** 
- `acyclic_macros st` ensures no infinite cycles
- `valid_latex_epsilon tokens` ensures bounded input
- Together should guarantee termination within finite fuel

---

## 💻 **CURRENT FILE STATE**

### **Main Proof File: `src/core/expander/ExpanderProofsComplete.v`**
```coq
(* Current status: 3 theorems with admits *)
admit. (* Requires full fuel monotonicity proof *)
admit. (* This case should be impossible with acyclic_macros *)  
admit. (* This case is impossible by construction *)
```

### **Working Algorithm Files:**
- `ExpanderAlgorithm.v` defines `expand_with_fuel` with this structure:
```coq
Fixpoint expand_with_fuel (fuel : nat) (st : exp_state) (tokens : list latex_token) : expand_result :=
  match fuel with
  | 0 => ExpandError FuelExhausted
  | S fuel' =>
      match tokens with
      | nil => ExpandSuccess nil
      | tok :: rest =>
          match tok with
          | TCommand cmd =>
              if exceeds_call_limit st then ExpandError MacroCallLimit
              else if in_call_stack (call_stack st) cmd then ExpandError (RecursionLimit cmd)
              else match lookup_builtin cmd with
                   | Some body =>
                       if exceeds_token_limit (increment_calls (push_call st cmd)) (length body)
                       then ExpandError TokenGrowthLimit
                       else expand_with_fuel fuel' (increment_calls (push_call st cmd)) (body ++ rest)
                   | None => ExpandError (MacroNotFound cmd)
                   end
          | _ => match expand_with_fuel fuel' st rest with
                 | ExpandSuccess expanded => ExpandSuccess (tok :: expanded)
                 | err => err
                 end
          end
  end.
```

---

## 🛠️ **CONCRETE ACTION PLAN**

### **Step 1: Complete builtins_no_teof**
```coq
(* In MacroCatalog.v, prove this helper lemma first *)
Lemma all_builtin_bodies_safe : forall m,
  In m builtin_macros ->
  exists s, macro_body m = TText s :: nil.
  
(* Then use it to prove *)
Lemma builtins_no_teof : forall cmd body,
  lookup_builtin cmd = Some body ->
  ~ In TEOF body.
```

**SPECIFIC APPROACH:**
1. Use systematic case analysis on the 76 macros in `builtin_macros`
2. Each case: `destruct Hin as [Heq | Hin]; [subst m; simpl; eexists; reflexivity | ]`
3. After 76 cases, `destruct Hin` gives contradiction

### **Step 2: Complete Fuel Monotonicity**
```coq
Lemma expand_fuel_monotonic : forall fuel1 fuel2 st tokens result,
  fuel1 <= fuel2 ->
  expand_with_fuel fuel1 st tokens = ExpandSuccess result ->
  expand_with_fuel fuel2 st tokens = ExpandSuccess result.
```

**SPECIFIC APPROACH:**
1. Induction on `fuel1` using `lt_wf_ind`
2. Case analysis on `tokens`: empty vs `tok :: rest`
3. For `TCommand` case: handle recursive call with `fuel'` and `fuel2 - 1`
4. Use induction hypothesis with `lia` to handle fuel arithmetic

### **Step 3: Complete Termination Proof**
```coq
(* Prove that acyclic + valid input bounds the required fuel *)
Lemma acyclic_bounds_fuel : forall st tokens,
  acyclic_macros st ->
  valid_latex_epsilon tokens ->
  required_fuel st tokens <= 1000.
  
(* Then use it in the main theorem *)
```

---

## ⚡ **COMPILATION COMMANDS**
```bash
cd /Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/src/core/expander
coqc ExpanderProofsComplete.v
```

**Expected Clean Output:**
```
(no output - successful compilation)
```

---

## 🎯 **SUCCESS CRITERIA**

### **VERIFICATION COMMANDS (Must All Pass):**
```coq
Check expand_fuel_insensitive.
Check expand_terminates_acyclic. 
Check expand_no_teof.
Print Assumptions expand_fuel_insensitive.  (* Must show: Closed under the global context *)
Print Assumptions expand_terminates_acyclic. (* Must show: Closed under the global context *)
Print Assumptions expand_no_teof.           (* Must show: Closed under the global context *)
```

### **FINAL REQUIREMENT:**
- **0 axioms, 0 admits** in entire codebase
- All 3 theorems must compile and verify
- `Print Assumptions` must show "Closed under the global context"

---

## 📚 **CONTEXT & BACKGROUND**

### **Project:** LaTeX Perfectionist v24 - Formally Verified LaTeX Processing Pipeline
### **Component:** Layer-02 (L1 Verified Macro Expander) 
### **Timeline:** Months 3-4 deliverable per `/latex‑perfectionist‑v24‑R3.yaml`
### **Integration:** Enables V1½ post-expansion validation rules

### **Key Specifications:**
- Interface: `expand : exp_state -> list latex_token -> expand_result`
- Built-in Macros: 76 macros (typography, mathematical, structural, formatting)
- Proof Targets: 3 formal verification requirements
- Standards: 0 axioms, 0 admits achieved

### **Architecture Context:**
- **VSNA Layers:** L0 (Lexer) → **L1 (Expander)** → L2 (Parser) → L3 (Validator) → L4 (Renderer)
- **Validation Layers:** V1 → **V1½ (Post-expansion)** → V2 → V3 → V4
- **LaTeX ε Constraint:** acyclic_bodies = true (prevents infinite recursion)

---

## 🔗 **ESSENTIAL FILES TO EXAMINE**

1. **`/src/core/expander/ExpanderProofsComplete.v`** - The main target file
2. **`/src/core/expander/MacroCatalog.v`** - All 76 builtin macro definitions  
3. **`/src/core/expander/ExpanderAlgorithm.v`** - The expand_with_fuel function
4. **`/src/core/expander/ExpanderTypes.v`** - Data type definitions
5. **`/latex‑perfectionist‑v24‑R3.yaml`** - Project roadmap and requirements

---

## ⚠️ **CRITICAL WARNINGS**

1. **NO ADMITS ALLOWED** - The user has emphasized this repeatedly
2. **MECHANICAL VERIFICATION REQUIRED** - All 76 builtin macros must be verified
3. **COMPILATION MUST SUCCEED** - Use `coqc ExpanderProofsComplete.v` to test
4. **STRONG INDUCTION NEEDED** - Use `lt_wf_ind` for well-founded recursion
5. **CASE ANALYSIS ESSENTIAL** - Systematic examination of all constructor cases

---

## 🚀 **YOUR MISSION**

**Complete the 3 formal verification theorems in `ExpanderProofsComplete.v` with 0 axioms, 0 admits.**

The functional implementation is complete. The project depends on these proofs to achieve the rigorous formal verification standards required for LaTeX Perfectionist v24.

**Focus on the lemmas first (builtins_no_teof, fuel monotonicity), then use them to complete the main theorems.**

Good luck! 🎯