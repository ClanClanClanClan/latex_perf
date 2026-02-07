# Coq Proof Status – Detailed Expert Handoff

This memo supersedes earlier notes and documents the precise state of the Coq proof tree after partially applying the recommended "fix pack". The build is currently broken; several files now diverge from `origin/fix-math-strip`. The sections below capture everything an expert needs to resume work.

---

## 1. Workspace Snapshot (branch `fix-math-strip`)

```
$ git status -sb
## fix-math-strip...origin/fix-math-strip
 M proofs/L0Smallstep.v
 M proofs/L0SmallstepControl.v
 M proofs/LexerIncremental.v
 M proofs/dune
?? proofs/ListWindow.v
?? docs/expert/
?? _opam/
```

- `_opam/` is from the local switch; ignore it.
- `docs/expert/` contains the expert’s instructions and this handoff file.
- `proofs/ListWindow.v` is new (helper lemmas).
- The three main Coq modules and the Dune file have pending modifications.

Before building, always clean artefacts left by earlier `coqc` runs:
```bash
rm -f proofs/*.glob proofs/*.vo proofs/*.vok proofs/*.vos
```

---

## 2. Current Build Failure

Running the full proof build: 
```bash
opam exec -- dune build proofs
```
produces the following errors (after cleaning `.glob` files):

```
File "./proofs/LexerIncremental.v", line 38, characters 2-15:
Error: No such goal.

File "./proofs/L0Smallstep.v", line 71, characters 38-58:
Error: Unable to find an instance for the variable A.

File "./proofs/L0SmallstepControl.v", line 67, characters 57-58:
Error:
In environment
s : list byte * list token
Hnf2 : forall t : list byte * list token, ~ rstep s t
s', s'' : list byte * list token
H : rstep s s'
Hr1 : rrun s' s''
Hnf1 : forall t : list byte * list token, ~ rstep s'' t
The term "H" has type "rstep s s'" while it is expected to have type
 "rstep s'' ?t" (cannot unify "s" and "s''").
```

Each error corresponds to partially-integrated changes described below.

---

## 3. Summary of Applied Changes

### 3.1 `proofs/ListWindow.v` (new file)
- Introduces polymorphic helper lemmas:
  - `firstn_length_append`
  - `skipn_length_append`
  - `firstn_skipn_length`
- Proofs were rewritten using `firstn_app` / `skipn_app`. The concluding rewrites still assume exact subterm shapes; Coq reduces them before the final tactic sees them, yielding the "No such goal" message. They need to be restored to the simple inductive proofs the expert suggested.

### 3.2 `proofs/L0SmallstepControl.v`
- Replaced the original segmented scanner with the simplified `map classify` version from the expert’s answer.
- Added `Open Scope nat_scope`, `Open Scope bool_scope`, and the `Nat.leb`-based `is_letter` definition.
- Updated relational lemmas to use `map classify`. However, `rrun_nf_unique` still uses the old elimination pattern and now mismatches the new structure (`H` vs `rstep` expectation).

### 3.3 `proofs/L0Smallstep.v`
- Added `Require Import ListWindow`, opened nat/bool scopes, and refactored `is_letter` to the `Nat.leb` form.
- Defined helper lemmas (`length_run`, etc.) near the top.
- Rewrote the window lemma to rely on the new helper lemmas by creating `pre_tokens`, `rest_tokens`, etc. Because those helper lemmas currently fail (and because the wrappers `firstn_length_append_token`/`skipn_length_append_token` were removed), Coq cannot infer `A:=token`, hence the error.

### 3.4 `proofs/LexerIncremental.v`
- Added `Require Import ListWindow` and the helper lemmas (`length_tokenize`, etc.).
- Replaced the old `tokenize_window_equivalence` with the version from the expert. It now uses `set (...)` before invoking the helper lemmas; due to this, `rewrite` no longer finds the necessary subterm, giving "No such goal".
- Length lemmas were hoisted earlier; later normalisation lemmas still use them correctly.

### 3.5 `proofs/dune`
- Module list now starts with `ListWindow` so other modules can `Require Import` it.

---

## 4. Root Cause of Remaining Errors

1. **ListWindow helper lemmas** – rewriting with `firstn_app` / `skipn_app` replaced the target with `xs ++ ?`, so a subsequent `rewrite` sees nothing to act on. Reverting to the inductive proofs shown by the expert will restore them:
   ```coq
   Lemma firstn_length_append ...
   Proof. induction xs; simpl; auto. now rewrite IHxs. Qed.
   ```
   Likewise for `skipn_length_append`.

2. **`L0SmallstepControl.v`** – after reintroducing the simplified semantics, `rrun_nf_unique` still pattern matches on the old shape. The fix is to copy the complete proof from the expert answer, which restructures the induction appropriately.

3. **`L0Smallstep.v`** – `run_window_equivalence` needs to call the helper lemmas without the `set` indirection or by reinstating thin wrappers (`firstn_length_append_token`). Once the helper module is consistent, the final version from the expert works.

4. **`LexerIncremental.v`** – same issue as above: the helper lemmas must match the term literally. Removing `set` and calling `rewrite skipn_length_append` / `rewrite firstn_length_append` directly (as in the expert snippet) resolves it.

5. **`.glob` artefacts** – always clean them before building (already noted).

---

## 5. Suggested Recovery Path

1. **Decide whether to revert or finish the fix pack.** If you prefer a clean slate, run:
   ```bash
   git checkout -- proofs/L0Smallstep.v proofs/L0SmallstepControl.v proofs/LexerIncremental.v proofs/dune
   rm -f proofs/ListWindow.v
   ```
   Then reapply the expert’s diffs carefully.

2. **If you keep the current edits:**
   - Restore the inductive proofs in `ListWindow.v`.
   - Update the Coq files to use the helper lemmas exactly as provided (no `set` indirections).
   - Complete the refactor in `L0SmallstepControl.v` so the relational lemmas align with `map classify`.

3. **Rebuild iteratively** after each change:
   ```bash
   rm -f proofs/*.glob proofs/*.vo proofs/*.vok proofs/*.vos
   opam exec -- dune build proofs
   ```

4. **Update Dune** only after the helpers and core files compile.

5. **Once everything builds**, run any project-specific tests or `dune runtest` to confirm nothing else regressed.

---

## 6. Reference Snippets (from expert answer)

- `is_letter` (Nat.leb form) – already applied.
- `tokenize_window_equivalence` (stable proof):
  ```coq
  rewrite tokenize_app with (a:=pre) (b:=mid ++ suf).
  rewrite skipn_length_append with (xs:=tokenize pre).
  rewrite tokenize_app with (a:=mid) (b:=suf).
  rewrite firstn_length_append with (xs:=tokenize mid).
  reflexivity.
  ```
- Simplified `L0SmallstepControl` with `rstep`/`rrun` lemmas – see `docs/expert/coq-proof-handoff-answer.md` for the full block.

---

## 7. Files Added or Modified

| File | Status | Notes |
|------|--------|-------|
| `proofs/ListWindow.v` | new | helper lemmas; proofs need repair. |
| `proofs/L0SmallstepControl.v` | modified | now uses map-based semantics; proofs partially updated. |
| `proofs/L0Smallstep.v` | modified | new helper usage; window lemmas need cleanup. |
| `proofs/LexerIncremental.v` | modified | window lemma rewired but proof mismatched. |
| `proofs/dune` | modified | includes new module ordering. |
| `docs/expert/coq-proof-handoff-answer.md` | new | expert instructions. |
| `docs/expert/coq-proof-current-status.md` | new | this handoff. |

---

## 8. Next Actions for the Expert

1. Decide whether to reset to the pre-modified files or fix the current partial integration.
2. Either way, ensure `ListWindow.v`’s lemmas compile before touching the dependent modules.
3. Rebuild with `dune` after each logical change, cleaning artefacts every time.
4. Once `dune build proofs` succeeds, push the minimal set of patches (and drop the intermediate experiments).

If any clarification is required, feel free to reach out. Ieu left things in the best possible state for an expert to resume without wading through failed experiments.
