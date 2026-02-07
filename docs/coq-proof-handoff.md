# Coq Proof Handoff (Current State)

This document replaces the earlier handoff notes and captures the exact state of the proof tree after partially applying the expert’s “fix pack”.  The build is still failing; the repository now contains additional helper modules and refactored definitions that diverge from `origin/fix-math-strip`.  An expert picking the work up should start from the information below.

---

## 1. Repository Snapshot (branch `fix-math-strip`)

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

Key points:
- New file `proofs/ListWindow.v` has the generic `firstn/skipn` helper lemmas suggested by the expert.
- `proofs/L0Smallstep.v`, `proofs/L0SmallstepControl.v`, and `proofs/LexerIncremental.v` have been modified (but the proof scripts do **not** yet compile).
- `proofs/dune` now lists `ListWindow` ahead of the other modules.
- `_opam/` is still untracked; ignore it.

---

## 2. Reproducing the Failure

1. Remove stale artefacts (important because earlier `coqc` runs leave `.glob` files under `proofs/`).
   ```bash
   rm -f proofs/*.glob proofs/*.vo proofs/*.vok proofs/*.vos
   ```
2. Build the Coq proofs.
   ```bash
   opam exec -- dune build proofs
   ```

The command currently fails with:

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

These errors stem from partially applying the new helper lemmas and simplified definitions without completing all dependent updates.

---

## 3. Summary of Applied Changes

### 3.1 New helper module
- `proofs/ListWindow.v` now provides:
  - `firstn_length_append`
  - `skipn_length_append`
  - `firstn_skipn_length`
  with `Set Implicit Arguments`.  The statements are correct, but the proofs were rewritten using `firstn_app`/`skipn_app`.  They currently fail because the terminating tactics try to match a subterm that no longer exists (the “No such goal” error).  Remedy: restructure the proof using `remember … as` or revert to the original (inductive) proof strategy.

### 3.2 `L0SmallstepControl.v`
- Completely replaced with the expert’s simplified `map classify` model (instead of the original segmented scanner).  The file now uses the re-exported helper lemmas and `Nat.leb` form of `is_letter`.
- Impact: dependent lemmas (e.g., `rrun_nf_unique`) need the new matching style; the refactor is halfway through and the proof script is not consistent yet.

### 3.3 `L0Smallstep.v`
- Added `Require Import ListWindow`, switched `is_letter` to the `Nat.leb` form, defined `run` at the top, and inserted helper lemmas (`length_run`, `skipn_length_append_token`, …).
- The window lemma now rewrites using `set (...)` plus the helper lemmas, but the helper lemmas themselves are not fully general (they were removed later) and Coq cannot resolve the implicit `A` in `skipn_length_append`/`firstn_length_append` (hence the “Unable to find an instance for the variable A” error).

### 3.4 `LexerIncremental.v`
- Switch to `Require Import ListWindow`, introduced an early `length_tokenize` lemma, and rewrote `tokenize_window_equivalence` to use `skipn_length_append`/`firstn_length_append` via `set` notation.  The new proof tries to `replace` with `skipn_length_append`/`firstn_length_append`, but because of the intermediate `set`, Coq does not see the pattern (resulting in the “No such goal” message).
- Later lemmas still reference `length_tokenize` (now located earlier in the file).  The rewrite is consistent, but the tactic arguments need to use the specialised lemmas or supply `A:=token` explicitly.

### 3.5 `proofs/dune`
- Updated to `(modules ListWindow CoreProofs …)` so the new helper file builds first.
- This is correct but currently untested because the earlier errors abort the build.

---

## 4. Open Issues Requiring Attention

1. **Helper lemmas (ListWindow.v) are broken.**  The current proofs using `firstn_app`/`skipn_app` don’t reduce to `reflexivity` because the subterm rewriting removes the exact form Coq expects.  A simple fix is to revert to the inductive proofs:
   ```coq
   Lemma firstn_length_append : forall (xs ys : list A),
     firstn (length xs) (xs ++ ys) = xs.
   Proof.
     induction xs; simpl; auto.
     now rewrite IHxs.
   Qed.
   ```
   Repeat for `skipn_length_append`.

2. **`L0SmallstepControl.v` proof alignment.**  After copying the simplified `map classify` model, the inductive reasoning in `rrun_nf_unique` still expects the original segmented semantics.  Either finish porting the relational lemmas to the new definition or revert the file to the previous version before reapplying the expert’s diff.

3. **`L0Smallstep.v` window lemma** needs the helper lemmas reinstated or adapted.  Currently it calls the polymorphic lemmas directly, which still works once `ListWindow` is fixed, but you must also ensure `Arguments` is set properly or supply the `A:=token` parameter.

4. **`LexerIncremental.v` window lemma** should follow the exact snippet from the expert document.  The easiest path: reinsert the two helper lemmas locally (or rely on `ListWindow` once fixed) and copy the proof verbatim:
   ```coq
   rewrite tokenize_app with (a:=pre) (b:=mid ++ suf).
   rewrite skipn_length_append with (xs:=tokenize pre) (ys:=tokenize (mid ++ suf)).
   rewrite tokenize_app with (a:=mid) (b:=suf).
   rewrite firstn_length_append with (xs:=tokenize mid) (ys:=tokenize suf).
   reflexivity.
   ```
   This must occur after restoring correct proofs of the helper lemmas.

5. **`.glob` artefacts**: continue to delete them (see §2) whenever rebuilding.

6. **Documentation**: The original handoff (`docs/coq-proof-handoff.md`) has been superseded by this file.  The expert answer is stored under `docs/expert/coq-proof-handoff-answer.md` for reference.

---

## 5. Recommended Recovery Plan

1. **Reset the modified Coq sources to HEAD** (if you prefer a clean slate) *or* fix the partial edits described above.  Reset can be done with:
   ```bash
   git checkout -- proofs/L0Smallstep.v proofs/L0SmallstepControl.v proofs/LexerIncremental.v proofs/dune
   rm -f proofs/ListWindow.v
   ```
   Then reapply the expert’s patches carefully.

2. **If you keep the current edits**, follow these steps:
   - Repair the helper lemmas in `ListWindow.v` (revert to inductive proofs).
   - Update `LexerIncremental.v` and `L0Smallstep.v` so they call those lemmas without `set` indirections or missing `A:=token` arguments.
   - Ensure `is_letter` definitions are the `Nat.leb` form (already done) and re-run the proofs to confirm.
   - Finish migrating the relational proof in `L0SmallstepControl.v` to the simplified `map classify` semantics (or revert to the previous segment-based model).

3. **Rebuild** after each logical step:
   ```bash
   rm -f proofs/*.glob proofs/*.vo proofs/*.vok proofs/*.vos
   opam exec -- dune build proofs
   ```

4. **Once proofs compile**, clean up the helper module ordering in `proofs/dune` and add any new files to version control.

---

## 6. Quick Reference: Expert Patch Snippets

For convenience, here are the key transformations (all quoted in `docs/expert/coq-proof-handoff-answer.md`).  Apply them exactly after aligning the files:

- Update `is_letter` in both `L0Smallstep*.v`.
- Add `proofs/ListWindow.v` and `Require Import ListWindow.` in files that need it.
- Rewrite `tokenize_window_equivalence` using `skipn_length_append` and `firstn_length_append`.
- Replace the segmented scanner in `L0SmallstepControl.v` if you intend to adopt the simplified semantics.


---

## 7. Contact Notes

If anything remains unclear or additional context is needed, feel free to ping me.  I stopped short of further edits to avoid diverging farther from `origin/fix-math-strip` without a clean compile.  The next expert should decide whether to finish porting the new helper-led approach or reset to the original files and reapply the patch set from scratch.
