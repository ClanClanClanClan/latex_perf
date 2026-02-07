# Coq Proof Handoff

This document collects everything an expert will need to pick up the failing Coq proof work in this repository. It captures the current state, reproduces the errors, explains the root causes, and outlines the proposed fixes. All information is current as of the latest run on branch `fix-math-strip`.

---

## 1. Repository Status Snapshot

- Branch: `fix-math-strip`
- `git status`: clean (only `_opam/` is untracked; the Coq source files match `HEAD`).
- No uncommitted changes exist; exploratory edits were reverted before preparing this document.

> **Important:** Running `coqc` on individual files creates `.glob` artefacts under `proofs/`. These conflict with Dune’s build rules. Delete them with `rm proofs/*.glob` before invoking `dune`.

---

## 2. How to Reproduce the Failures

```bash
cd /Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts
rm -f proofs/*.glob            # remove stale artefacts from earlier runs
opam exec -- dune build proofs # current failing command
```

---

## 3. Current Build Failures

The build stops with three blocking errors:

1. `proofs/L0SmallstepControl.v`, line 18: boolean expression misuse (type `byte` used where `bool` is required).
2. `proofs/L0Smallstep.v`, line 18: same issue as above.
3. `proofs/LexerIncremental.v`, line 40: lemma `tokenize_window_equivalence` proof script tries to rewrite with `app_assoc`, but the generated term no longer matches the required pattern.

Full compiler output excerpt:

```
File "./proofs/L0SmallstepControl.v", line 18, characters 10-11:
Error:
In environment
b : byte
The term "b" has type "byte" while it is expected to have type "bool".

File "./proofs/L0Smallstep.v", line 18, characters 10-11:
Error:
In environment
b : byte
The term "b" has type "byte" while it is expected to have type "bool".

File "./proofs/LexerIncremental.v", line 40, characters 2-19:
Error:
Found no subterm matching "?M1387 ++ ?M1388 ++ ?M1389" in the current goal.
```

---

## 4. Root Cause Analysis

### 4.1 `is_letter` in `L0SmallstepControl.v`

```coq
Definition is_letter (b:byte) : bool :=
  (65 <=? b && b <=? 90) || (97 <=? b && b <=? 122).
```

Without parentheses, Coq parses the first conjunct as `((65 <=? b && b) <=? 90)`, so the second argument of `&&` is `b : nat`. Hence the “expected type bool” error. Any arithmetic using `<=?` must be wrapped.

**Fix:** insert parentheses or use `Nat.leb` explicitly. Example:

```coq
Definition is_letter (b:byte) : bool :=
  orb (andb (Nat.leb 65 b) (Nat.leb b 90))
      (andb (Nat.leb 97 b) (Nat.leb b 122)).
```

### 4.2 `is_letter` in `L0Smallstep.v`

Identical issue and identical fix. (Both modules define their own copy.)

### 4.3 `tokenize_window_equivalence` in `LexerIncremental.v`

The current proof unfolds to:

```coq
intros pre mid suf.
rewrite tokenize_app.
rewrite app_assoc.
rewrite tokenize_app.
...
```

After the first `rewrite tokenize_app`, the term is `(tokenize pre ++ tokenize mid) ++ tokenize suf`. Rewriting `app_assoc` now seeks `(X ++ Y) ++ Z`, but Coq no longer sees this pattern because of the inserted conversions. That produces the “Found no subterm matching …” error.

**Fix:** introduce simple append lemmas for `firstn`/`skipn` and avoid `app_assoc` entirely. Recommended supporting lemmas:

```coq
Lemma firstn_length_append_token : forall (xs ys:list token),
  firstn (length xs) (xs ++ ys) = xs.
Proof.
  induction xs; intros ys; simpl; auto.
  now rewrite IHxs.
Qed.

Lemma skipn_length_append_token : forall (xs ys:list token),
  skipn (length xs) (xs ++ ys) = ys.
Proof.
  induction xs; intros ys; simpl; auto.
  now rewrite IHxs.
Qed.
```

Then rewrite the main proof as:

```coq
intros pre mid suf.
rewrite tokenize_app with (a:=pre) (b:=mid ++ suf).
rewrite skipn_length_append_token.
rewrite tokenize_app with (a:=mid) (b:=suf).
rewrite firstn_length_append_token.
reflexivity.
```

Remember to rewrite lengths via `length_tokenize` where needed so the `length` arguments line up (`length mid` vs `length (tokenize mid)`).

---

## 5. Suggested Patch Snippets

Below are minimal diffs the expert can apply directly (or translate into their preferred style).

### 5.1 Update `is_letter`

Apply the same edit in both `proofs/L0SmallstepControl.v` and `proofs/L0Smallstep.v`.

```diff
-Definition is_letter (b:byte) : bool :=
-  (65 <=? b && b <=? 90) || (97 <=? b && b <=? 122).
+Definition is_letter (b:byte) : bool :=
+  orb (andb (Nat.leb 65 b) (Nat.leb b 90))
+      (andb (Nat.leb 97 b) (Nat.leb b 122)).
```

### 5.2 Helper Lemmas for `LexerIncremental`

Insert near the top (after `tokenize` or in the helper section):

```coq
Lemma firstn_length_append_token : forall (xs ys:list token),
  firstn (length xs) (xs ++ ys) = xs.
Proof.
  induction xs; intros ys; simpl; auto.
  now rewrite IHxs.
Qed.

Lemma skipn_length_append_token : forall (xs ys:list token),
  skipn (length xs) (xs ++ ys) = ys.
Proof.
  induction xs; intros ys; simpl; auto.
  now rewrite IHxs.
Qed.
```

### 5.3 Rewrite the Window Lemma in `LexerIncremental`

```diff
 Lemma tokenize_window_equivalence : forall pre mid suf,
       firstn (length mid) (skipn (length pre) (tokenize (pre ++ mid ++ suf))) = tokenize mid.
 Proof.
   intros pre mid suf.
-  rewrite tokenize_app.
-  rewrite app_assoc.
-  rewrite tokenize_app.
-  rewrite skipn_app.
-  rewrite firstn_app.
-  rewrite firstn_all.
-  replace (skipn (length pre) (tokenize pre)) with (@nil token).
-  2:{ rewrite <- firstn_all with (l:=tokenize pre) at 1.
-      rewrite firstn_skipn. reflexivity. }
-  simpl. rewrite app_nil_l.
-  rewrite firstn_all. reflexivity.
+  rewrite tokenize_app with (a:=pre) (b:=mid ++ suf).
+  rewrite skipn_length_append_token.
+  rewrite tokenize_app with (a:=mid) (b:=suf).
+  rewrite firstn_length_append_token.
+  reflexivity.
 Qed.
```

### 5.4 Optional: Offsets Helpers in `L0Smallstep`

Should you wish to streamline later proofs (e.g., `normalized_offsets_window`), the identities below generalise the reasoning:

```coq
Lemma map_seq_shift : forall k r m,
  map (fun o => o - k) (seq (k + r) m) = seq r m.
Proof.
  intros k r m.
  revert k r.
  induction m as [|m IH]; intros k r; simpl; auto.
  replace (k + r - k) with r by lia.
  replace (S (k + r)) with (k + S r) by lia.
  rewrite IH.
  reflexivity.
Qed.

Lemma map_seq_sub : forall k m,
  map (fun o => o - k) (seq k m) = seq 0 m.
Proof.
  intros k m.
  change k with (k + 0) at 1.
  apply map_seq_shift.
Qed.
```

`map_seq_sub` is simply `map_seq_shift` with `r = 0`. Incorporating them avoids re-proving small arithmetic facts by hand.

---

## 6. Additional Practical Notes

- **.glob artefacts:** `coqc proofs/*.v` leaves `.glob` files under `proofs/`. Delete them before running Dune or it will abort with “Multiple rules generated for … .glob”.
- **File resets:** The working tree currently matches `HEAD`. Feel free to apply the minimal patches above; you won’t be fighting local diffs.
- **Future work:** After `is_letter` and the window lemma are fixed, revisit the offset lemmas. The helper functions suggested above can simplify that section if you decide to refactor.

---

## 7. Recommendation Summary

1. Apply the parenthesised `is_letter` definition in both small-step modules.
2. Add the two list helper lemmas to `LexerIncremental.v` and simplify `tokenize_window_equivalence` as shown.
3. Delete stale `proofs/*.glob` artefacts before rebuilding.
4. Re-run `opam exec -- dune build proofs` to confirm all three errors are resolved.
5. Proceed with any broader proof refactors (offset window lemmas, etc.) using the helper lemmas as desired.

With these changes in place the immediate build blockers should disappear, leaving the rest of the proof development ready for detailed expert attention.
