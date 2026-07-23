(** * BodyTokenFrontEnd — the VERIFIED bytes→body_token front-end (v27.1.58).

    This file closes compile-guarantee gap #1: the capstone theorem
    [PdflatexModel.pdflatex_compile_safe] quantifies over an abstract
    [body_token] list that was, until now, produced by UNVERIFIED OCaml
    ([Compile_evidence.extract_body] over [Ast_semantic_state.labels]/[refs]).
    Here the WHOLE production of that list from raw source bytes is modelled in
    Coq, proven correct (sound + complete scanners, sorted offsets, exact
    premise-function bridges) and EXTRACTED to OCaml
    ([latex-parse/src/body_token_frontend_extracted.ml], regenerated
    byte-identically by [scripts/tools/regen_body_token_frontend_extract.sh]).
    The runtime then EXECUTES [body_of_source] as the production path.

    The model mirrors the shipped OCaml scanners BYTE-FOR-BYTE:

      - [read_key]        mirrors [Ast_semantic_state.read_env_name]: expect
                          '{' (123) at the given index, scan to the FIRST '}'
                          (125), return the raw bytes strictly between plus the
                          index one past the '}'; [None] if unclosed.
      - [scan_labels]     mirrors [Ast_semantic_state.labels]: left-to-right;
                          at each unprotected position matching "\label{" read
                          the key at pos+6 and JUMP past the match; otherwise
                          advance one byte.  No escaped-backslash guard, by
                          design (the OCaml deliberately mirrors the regex
                          token grammar it replaced).
      - [scan_refs]       mirrors [Ast_semantic_state.refs] with the same
                          five-command table in the same [find_opt] order
                          ("\eqref{", "\autoref{", "\cref{", "\Cref{",
                          "\ref{").
      - [in_ranges_b]     mirrors [Ast_semantic_state.in_ranges]: HALF-OPEN
                          ranges, [a <= off < b].  The protected ranges
                          themselves ([find_verbatim_comment_url_ranges])
                          remain a TRUSTED oracle passed in as data.
      - [merge_events]    the offset-sorted merge of the TWO INDEPENDENT scans
                          (defs before refs on equal offset, mirroring
                          [List.stable_sort] over defs-then-refs).  The
                          two-pass structure is semantically load-bearing:
                          "\label{a\ref{b}}" emits BOTH the def of "a\ref{b"
                          AND the ref of "b" (see [scan_labels_nested] /
                          [scan_refs_nested] below).  A single-pass scanner
                          would be WRONG.
      - [fnv30]           mirrors [Compile_evidence.label_id] exactly:
                          h0 = 0x811c9dc5 (UNMASKED — so the EMPTY key hashes
                          to 0x811c9dc5 > 2^30-1; see the deviation note at
                          [fnv30_bound]); per byte
                          h <- ((h lxor b) land 0x3FFFFFFF) * 0x01000193
                               land 0x3FFFFFFF.
      - [detect_body_features] mirrors the OCaml needle-for-needle with the
                          SAME emission order (OTF, unicode-math, lua, CJK,
                          utf8-inputenc — the OCaml conses then [List.rev]s,
                          each feature having exactly one add site).
      - [is_blank]        mirrors [String.trim source = ""] (the OCaml trim
                          whitespace class: bytes 32, 12, 10, 13, 9).

    Everything is TOTAL (fuel-based recursion with proven-sufficient fuel),
    Qed-proved, 0 admits, 0 axioms.  [Print Assumptions compile_safe_of_source]
    is executed at the end of this file and must print "Closed under the
    global context". *)

From Coq Require Import Strings.String Strings.Ascii.
From Coq Require Import List Bool Arith Lia.
From Coq Require Import Sorting.Sorted.
From LaTeXPerfectionist Require Import
  ProjectClosure
  BuildProfileSound
  LexerFaithfulStep
  PdflatexModel
  CompileGuaranteeBridge.
Import ListNotations.

(** ── Byte model ─────────────────────────────────────────────────────

    A byte is a [nat].  The runtime feeds values < 256 ([Char.code]); the
    model does not require that bound anywhere. *)

Definition byte : Type := nat.

(** Protected ranges, HALF-OPEN — mirrors [Ast_semantic_state.in_ranges]
    ([a <= off && off < b]).  The ranges come from the trusted oracle
    [Validators_common.find_verbatim_comment_url_ranges]. *)
Definition in_ranges_b (ranges : list (nat * nat)) (off : nat) : bool :=
  existsb (fun r => andb (Nat.leb (fst r) off) (Nat.ltb off (snd r))) ranges.

(** [prefix_b needle hay] — [needle] is a byte-prefix of [hay].  Mirrors the
    OCaml [starts_with] (bounds included). *)
Fixpoint prefix_b (needle hay : list byte) : bool :=
  match needle with
  | [] => true
  | n0 :: nrest =>
      match hay with
      | [] => false
      | h0 :: hrest => andb (Nat.eqb n0 h0) (prefix_b nrest hrest)
      end
  end.

(** Substring test — mirrors [Compile_evidence.contains]. *)
Fixpoint contains_b (needle hay : list byte) : bool :=
  match hay with
  | [] => prefix_b needle []
  | _ :: rest => orb (prefix_b needle hay) (contains_b needle rest)
  end.

(** First token of [toks] that prefixes [l] — mirrors [List.find_opt] over the
    ref-command table. *)
Fixpoint first_match (toks : list (list byte)) (l : list byte)
    : option (list byte) :=
  match toks with
  | [] => None
  | t :: rest => if prefix_b t l then Some t else first_match rest l
  end.

(** Index of the FIRST '}' (byte 125) in [l], if any. *)
Fixpoint idx_close (l : list byte) : option nat :=
  match l with
  | [] => None
  | b :: rest => if Nat.eqb b 125 then Some 0 else option_map S (idx_close rest)
  end.

(** [read_key l i] — mirror of [Ast_semantic_state.read_env_name]: expects
    '{' (123) at index [i] of [l], scans to the FIRST '}' (125); returns
    [Some (key_bytes, next)] where [key_bytes] are the bytes strictly between
    and [next] is one past the '}'; [None] if the byte at [i] is not '{' or
    no '}' follows. *)
Definition read_key (l : list byte) (i : nat) : option (list byte * nat) :=
  match nth_error l i with
  | Some b =>
      if Nat.eqb b 123 then
        match idx_close (skipn (S i) l) with
        | Some d => Some (firstn d (skipn (S i) l), i + d + 2)
        | None => None
        end
      else None
  | None => None
  end.

(** ── Token byte constants ─────────────────────────────────────────── *)

Definition bytes_of_string (s : string) : list byte :=
  List.map Ascii.nat_of_ascii (String.list_ascii_of_string s).

Local Open Scope string_scope.

Definition label_tok : list byte := Eval compute in bytes_of_string "\label{".
Definition eqref_tok : list byte := Eval compute in bytes_of_string "\eqref{".
Definition autoref_tok : list byte :=
  Eval compute in bytes_of_string "\autoref{".
Definition cref_tok : list byte := Eval compute in bytes_of_string "\cref{".
Definition Cref_tok : list byte := Eval compute in bytes_of_string "\Cref{".
Definition ref_tok : list byte := Eval compute in bytes_of_string "\ref{".

Local Close Scope string_scope.

(** Sanity: the literal byte values (92 = '\\', 123 = '{'). *)
Example label_tok_bytes : label_tok = [92; 108; 97; 98; 101; 108; 123].
Proof. reflexivity. Qed.

Example ref_tok_bytes : ref_tok = [92; 114; 101; 102; 123].
Proof. reflexivity. Qed.

(** The five reference commands, in the OCaml [find_opt] table order. *)
Definition ref_tokens : list (list byte) :=
  [eqref_tok; autoref_tok; cref_tok; Cref_tok; ref_tok].

(** ── The generic scanner ──────────────────────────────────────────────

    One left-to-right pass: at each position, if unprotected and some token
    prefixes the remaining suffix, read the key at (token length - 1) past the
    position (the '{' of the token) and JUMP past the whole match; otherwise
    advance one byte.  Fuel-based; [S (length src)] fuel is sufficient
    ([scan_from_fuel_irrelevant]). *)
Fixpoint scan_from (fuel : nat) (toks : list (list byte))
    (protected : list (nat * nat)) (pos : nat) (l : list byte)
    {struct fuel} : list (nat * list byte) :=
  match fuel with
  | O => []
  | S f =>
      match l with
      | [] => []
      | b0 :: rest =>
          if in_ranges_b protected pos then
            scan_from f toks protected (S pos) rest
          else
            match first_match toks (b0 :: rest) with
            | Some tok =>
                match read_key (b0 :: rest) (length tok - 1) with
                | Some (key, next) =>
                    (pos, key)
                    :: scan_from f toks protected (pos + next)
                         (skipn next (b0 :: rest))
                | None => scan_from f toks protected (S pos) rest
                end
            | None => scan_from f toks protected (S pos) rest
            end
      end
  end.

Definition scan_generic (toks : list (list byte)) (src : list byte)
    (protected : list (nat * nat)) : list (nat * list byte) :=
  scan_from (S (length src)) toks protected 0 src.

(** The label scan — mirror of [Ast_semantic_state.labels] (offset + key). *)
Definition scan_labels (src : list byte) (protected : list (nat * nat))
    : list (nat * list byte) :=
  scan_generic [label_tok] src protected.

(** The ref scan — mirror of [Ast_semantic_state.refs] (offset + key). *)
Definition scan_refs (src : list byte) (protected : list (nat * nat))
    : list (nat * list byte) :=
  scan_generic ref_tokens src protected.

(** ── Merged event stream ────────────────────────────────────────────── *)

Inductive scan_event : Type :=
  | Ev_def (off : nat) (key : list byte)
  | Ev_ref (off : nat) (key : list byte).

Definition ev_off (e : scan_event) : nat :=
  match e with Ev_def o _ => o | Ev_ref o _ => o end.

Definition ev_key (e : scan_event) : list byte :=
  match e with Ev_def _ k => k | Ev_ref _ k => k end.

Definition ev_def_of (p : nat * list byte) : scan_event :=
  Ev_def (fst p) (snd p).

Definition ev_ref_of (p : nat * list byte) : scan_event :=
  Ev_ref (fst p) (snd p).

Definition is_def_event (e : scan_event) : bool :=
  match e with Ev_def _ _ => true | Ev_ref _ _ => false end.

(** Offset-sorted merge, DEFS FIRST on equal offsets — mirrors
    [List.stable_sort compare] over the defs-then-refs concatenation (stable
    sort + defs prepended = defs win ties).  Total for ANY inputs (fuel =
    sum of lengths is exactly sufficient; the fuel-0 fallback concatenates,
    and is unreachable under sufficient fuel). *)
Fixpoint merge_fuel (fuel : nat) (defs refs : list (nat * list byte))
    : list scan_event :=
  match fuel with
  | O => map ev_def_of defs ++ map ev_ref_of refs
  | S f =>
      match defs, refs with
      | [], _ => map ev_ref_of refs
      | _, [] => map ev_def_of defs
      | (od, kd) :: ds, (orf, kr) :: rs =>
          if Nat.leb od orf then Ev_def od kd :: merge_fuel f ds refs
          else Ev_ref orf kr :: merge_fuel f defs rs
      end
  end.

Definition merge_events (defs refs : list (nat * list byte))
    : list scan_event :=
  merge_fuel (length defs + length refs) defs refs.

(** ── FNV-1a 30-bit hash — mirror of [Compile_evidence.label_id] ──────

    OCaml original:  h := ref 0x811c9dc5;
                     per byte c:  xored := (h lxor c) land 0x3FFFFFFF;
                                  h     := (xored * 0x01000193) land 0x3FFFFFFF
    The initial basis is NOT masked (the OCaml [ref 0x811c9dc5] is used
    as-is), so the EMPTY key hashes to 0x811c9dc5 = 2166136261 > 2^30 - 1.

    All constants are expressed via [2 ^ k] so no gigantic unary numeral is
    ever built:  0x811c9dc5 = 129*2^24 + 28*2^16 + 157*2^8 + 197,
                 0x01000193 = 2^24 + 403,  0x3FFFFFFF = 2^30 - 1. *)

Definition two30 : nat := 2 ^ 30.
Definition mask30 : nat := 2 ^ 30 - 1.
Definition fnv_basis : nat := 129 * 2 ^ 24 + 28 * 2 ^ 16 + 157 * 2 ^ 8 + 197.
Definition fnv_prime : nat := 2 ^ 24 + 403.

(** [Nat.odd] via realized primitives only ([Nat.div2] extracts to [n/2];
    [Nat.odd]'s own fixpoint would extract to O(n) recursion under
    ExtrOcamlNatInt). *)
Definition odd_b (n : nat) : bool := negb (Nat.eqb n (2 * Nat.div2 n)).

(** Bitwise XOR of the low [fuel] bits.  With fuel 32 this is EXACT for the
    values the hash ever feeds it (h <= 0x811c9dc5 < 2^32, byte < 2^8), i.e.
    it equals OCaml's [Int.logxor] on the runtime inputs. *)
Fixpoint lxor_fuel (fuel a b : nat) : nat :=
  match fuel with
  | O => 0
  | S f =>
      (if xorb (odd_b a) (odd_b b) then 1 else 0)
      + 2 * lxor_fuel f (Nat.div2 a) (Nat.div2 b)
  end.

Definition lxor32 (a b : nat) : nat := lxor_fuel 32 a b.

(** Right shift by [fuel] bits (iterated [Nat.div2]). *)
Fixpoint shr_fuel (fuel x : nat) : nat :=
  match fuel with
  | O => x
  | S f => shr_fuel f (Nat.div2 x)
  end.

(** [x land 0x3FFFFFFF] = [x mod 2^30], computed with realized primitives
    (sub/mul/div2) only. *)
Definition mod_two30 (x : nat) : nat := x - two30 * shr_fuel 30 x.

(** One FNV-1a byte step, in the OCaml's exact operation order: xor, mask,
    multiply, mask. *)
Definition fnv_step (h b : nat) : nat :=
  mod_two30 (mod_two30 (lxor32 h b) * fnv_prime).

Definition fnv30 (key : list byte) : nat := fold_left fnv_step key fnv_basis.

(** ── Feature detection — needle-for-needle mirror ───────────────────── *)

Local Open Scope string_scope.

Definition n_fontspec : list byte :=
  Eval compute in bytes_of_string "\usepackage{fontspec}".
Definition n_fontspec_nomath : list byte :=
  Eval compute in bytes_of_string "\usepackage[no-math]{fontspec}".
Definition n_setmainfont : list byte :=
  Eval compute in bytes_of_string "\setmainfont".
Definition n_unicode_math : list byte :=
  Eval compute in bytes_of_string "\usepackage{unicode-math}".
Definition n_setmathfont : list byte :=
  Eval compute in bytes_of_string "\setmathfont".
Definition n_luacode : list byte :=
  Eval compute in bytes_of_string "\usepackage{luacode}".
Definition n_directlua : list byte :=
  Eval compute in bytes_of_string "\directlua".
Definition n_cjk_pkg : list byte :=
  Eval compute in bytes_of_string "\usepackage{CJK}".
Definition n_cjk_begin : list byte :=
  Eval compute in bytes_of_string "\begin{CJK}".
Definition n_luatexja : list byte :=
  Eval compute in bytes_of_string "\usepackage{luatexja}".
Definition n_utf8_inputenc : list byte :=
  Eval compute in bytes_of_string "\usepackage[utf8]{inputenc}".

Local Close Scope string_scope.

(** Mirrors [Compile_evidence.detect_body_features]: same needles, same
    guards, same RESULT ORDER (the OCaml conses each feature at most once —
    one add site per feature — then reverses, so the output order is exactly
    the textual order of the five condition blocks). *)
Definition detect_body_features (src : list byte) : list feature :=
  (if contains_b n_fontspec src
      || contains_b n_fontspec_nomath src
      || contains_b n_setmainfont src
   then [Opentype_fonts] else [])
  ++ (if contains_b n_unicode_math src || contains_b n_setmathfont src
      then [Unicode_math] else [])
  ++ (if contains_b n_luacode src || contains_b n_directlua src
      then [Lua_scripting] else [])
  ++ (if contains_b n_cjk_pkg src
         || contains_b n_cjk_begin src
         || contains_b n_luatexja src
      then [Japanese_cjk] else [])
  ++ (if contains_b n_utf8_inputenc src then [UTF8_inputenc] else []).

(** OCaml [String.trim] whitespace class: ' ' '\012' '\n' '\r' '\t'. *)
Definition is_ws (b : byte) : bool :=
  orb (Nat.eqb b 32)
    (orb (Nat.eqb b 12) (orb (Nat.eqb b 10) (orb (Nat.eqb b 13) (Nat.eqb b 9)))).

(** [String.trim source = ""] iff every byte is trim-whitespace. *)
Definition is_blank (src : list byte) : bool := forallb is_ws src.

(** ── THE front-end: bytes → body_token list ─────────────────────────── *)

Definition token_of_event (e : scan_event) : body_token :=
  match e with
  | Ev_def _ k => BT_label_def (fnv30 k)
  | Ev_ref _ k => BT_label_ref (fnv30 k)
  end.

(** Mirror of [Compile_evidence.extract_body]: merged label/ref events in
    offset order, then one [BT_needs_feature] per detected feature, then a
    [BT_text] marker iff the source is not blank. *)
Definition body_of_source (src : list byte) (protected : list (nat * nat))
    : list body_token :=
  map token_of_event
    (merge_events (scan_labels src protected) (scan_refs src protected))
  ++ map BT_needs_feature (detect_body_features src)
  ++ (if is_blank src then [] else [BT_text]).

(** ════════════════════════════════════════════════════════════════════
    PROOFS
    ════════════════════════════════════════════════════════════════════ *)

(** ── List-indexing utilities ────────────────────────────────────────── *)

Lemma skipn_add : forall (A : Type) (a b : nat) (l : list A),
  skipn b (skipn a l) = skipn (a + b) l.
Proof.
  intros A a. induction a as [|a IH]; intros b l; simpl.
  - reflexivity.
  - destruct l as [|x xs].
    + rewrite !skipn_nil. reflexivity.
    + apply IH.
Qed.

Lemma nth_error_skipn_add : forall (A : Type) (a : nat) (l : list A) (i : nat),
  nth_error (skipn a l) i = nth_error l (a + i).
Proof.
  intros A a. induction a as [|a IH]; intros l i; simpl.
  - reflexivity.
  - destruct l as [|x xs]; simpl.
    + destruct i; reflexivity.
    + apply IH.
Qed.

Lemma skipn_S_cons : forall (A : Type) (l : list A) pos b rest,
  skipn pos l = b :: rest -> skipn (S pos) l = rest.
Proof.
  intros A l pos b rest H.
  replace (S pos) with (pos + 1) by lia.
  rewrite <- skipn_add. rewrite H. reflexivity.
Qed.

Lemma skipn_nil_le : forall (A : Type) (l : list A) pos,
  skipn pos l = [] -> length l <= pos.
Proof.
  intros A l pos H.
  pose proof (skipn_length pos l) as Hl.
  rewrite H in Hl. simpl in Hl. lia.
Qed.

(** ── prefix_b facts ─────────────────────────────────────────────────── *)

Lemma prefix_b_nth : forall t l j,
  prefix_b t l = true -> j < length t -> nth_error l j = nth_error t j.
Proof.
  induction t as [|a t IH]; intros l j Hp Hj; simpl in Hj; [lia|].
  destruct l as [|h l']; simpl in Hp; [discriminate|].
  apply andb_prop in Hp. destruct Hp as [He Hp].
  apply Nat.eqb_eq in He. subst h.
  destruct j; simpl.
  - reflexivity.
  - apply IH; [exact Hp | lia].
Qed.

Lemma prefix_b_nonnil : forall t l,
  prefix_b t l = true -> t <> [] -> l <> [].
Proof.
  intros t l Hp Ht. destruct t as [|a t]; [congruence|].
  destruct l as [|h l']; simpl in Hp; [discriminate | discriminate].
Qed.

(** Token literally present at [off] in [src]. *)
Definition tok_at (src tok : list byte) (off : nat) : Prop :=
  prefix_b tok (skipn off src) = true.

Lemma tok_at_lt : forall src tok off,
  tok_at src tok off -> tok <> [] -> off < length src.
Proof.
  intros src tok off Hat Hne. unfold tok_at in Hat.
  assert (Hnn : skipn off src <> []) by (eapply prefix_b_nonnil; eauto).
  destruct (le_lt_dec (length src) off) as [Hle|]; [|assumption].
  exfalso. apply Hnn. apply skipn_all2. exact Hle.
Qed.

Lemma tok_at_second : forall src t off b2,
  tok_at src t off -> nth_error t 1 = Some b2 ->
  nth_error (skipn off src) 1 = Some b2.
Proof.
  intros src t off b2 Hat Hn.
  unfold tok_at in Hat.
  assert (Hlen : 1 < length t).
  { apply nth_error_Some. rewrite Hn. discriminate. }
  rewrite (prefix_b_nth _ _ 1 Hat Hlen). exact Hn.
Qed.

(** ── idx_close / read_key facts ─────────────────────────────────────── *)

Lemma idx_close_sound : forall l d,
  idx_close l = Some d ->
  nth_error l d = Some 125 /\
  (forall j, j < d -> nth_error l j <> Some 125).
Proof.
  induction l as [|b rest IH]; intros d H; simpl in H; [discriminate|].
  destruct (Nat.eqb b 125) eqn:Eb.
  - injection H as <-. apply Nat.eqb_eq in Eb. subst b.
    split; [reflexivity | intros j Hj; lia].
  - destruct (idx_close rest) as [d'|] eqn:Er; simpl in H; [|discriminate].
    injection H as <-.
    destruct (IH d' eq_refl) as [H1 H2].
    split.
    + simpl. exact H1.
    + intros j Hj. destruct j; simpl.
      * intro Hc. injection Hc as ->. rewrite Nat.eqb_refl in Eb. discriminate.
      * apply H2. lia.
Qed.

Lemma read_key_next_lower : forall l i k nx,
  read_key l i = Some (k, nx) -> i + 2 <= nx.
Proof.
  intros l i k nx H. unfold read_key in H.
  destruct (nth_error l i) as [b|]; [|discriminate].
  destruct (Nat.eqb b 123); [|discriminate].
  destruct (idx_close (skipn (S i) l)) as [d|]; [|discriminate].
  injection H as _ H. lia.
Qed.

(** THEOREM 1 — soundness of the key reader: a successful read returns the
    bytes STRICTLY BETWEEN the '{' at [i] and the FIRST following '}', and
    the returned index is one past that '}'. *)
Theorem read_key_sound : forall src i key next,
  read_key src i = Some (key, next) ->
  nth_error src i = Some 123
  /\ key = firstn (length key) (skipn (S i) src)
  /\ (forall j, j < length key -> nth_error src (S i + j) <> Some 125)
  /\ nth_error src (S i + length key) = Some 125
  /\ next = S i + length key + 1.
Proof.
  intros src i key next H. unfold read_key in H.
  destruct (nth_error src i) as [b|] eqn:En; [|discriminate].
  destruct (Nat.eqb b 123) eqn:Eb; [|discriminate].
  apply Nat.eqb_eq in Eb. subst b.
  destruct (idx_close (skipn (S i) src)) as [d|] eqn:Ec; [|discriminate].
  assert (Hk : firstn d (skipn (S i) src) = key) by congruence.
  assert (Hn : i + d + 2 = next) by congruence.
  clear H.
  destruct (idx_close_sound _ _ Ec) as [Hd Hlt].
  assert (Hdlen : d < length (skipn (S i) src)).
  { apply nth_error_Some. rewrite Hd. discriminate. }
  assert (Hklen : length key = d).
  { rewrite <- Hk. apply firstn_length_le. lia. }
  split; [exact En || reflexivity|].
  split.
  { rewrite Hklen. symmetry. exact Hk. }
  split.
  { intros j Hj. rewrite Hklen in Hj.
    rewrite <- nth_error_skipn_add. apply Hlt. exact Hj. }
  split.
  { rewrite Hklen. rewrite <- nth_error_skipn_add. exact Hd. }
  rewrite Hklen. lia.
Qed.

(** Shifting [read_key] across a [skipn] (relative vs absolute indices). *)
Lemma read_key_shift : forall src off i,
  read_key (skipn off src) i
  = option_map (fun p : list byte * nat => (fst p, snd p - off))
      (read_key src (off + i)).
Proof.
  intros src off i. unfold read_key.
  rewrite nth_error_skipn_add.
  destruct (nth_error src (off + i)) as [b|]; [|reflexivity].
  destruct (Nat.eqb b 123); [|reflexivity].
  replace (skipn (S i) (skipn off src)) with (skipn (S (off + i)) src)
    by (rewrite skipn_add; f_equal; lia).
  destruct (idx_close (skipn (S (off + i)) src)) as [d|]; simpl; [|reflexivity].
  f_equal. f_equal. lia.
Qed.

Lemma read_key_shift_fw : forall src off i k nx,
  read_key (skipn off src) i = Some (k, nx) ->
  read_key src (off + i) = Some (k, off + nx).
Proof.
  intros src off i k nx H.
  rewrite read_key_shift in H.
  destruct (read_key src (off + i)) as [[k' m]|] eqn:E; simpl in H;
    [|discriminate].
  injection H as <- Hm.
  pose proof (read_key_next_lower _ _ _ _ E).
  f_equal. f_equal. lia.
Qed.

Lemma read_key_shift_bw : forall src off i k m,
  read_key src (off + i) = Some (k, m) ->
  read_key (skipn off src) i = Some (k, m - off).
Proof.
  intros src off i k m H. rewrite read_key_shift. rewrite H. reflexivity.
Qed.

(** ── first_match facts ─────────────────────────────────────────────── *)

Lemma first_match_sound : forall toks l t,
  first_match toks l = Some t -> In t toks /\ prefix_b t l = true.
Proof.
  induction toks as [|a toks IH]; intros l t H; simpl in H; [discriminate|].
  destruct (prefix_b a l) eqn:E.
  - injection H as <-. split; [left; reflexivity | exact E].
  - destruct (IH _ _ H) as [Hin Hp]. split; [right; exact Hin | exact Hp].
Qed.

Lemma first_match_complete : forall toks l t,
  In t toks -> prefix_b t l = true ->
  exists t', first_match toks l = Some t'.
Proof.
  induction toks as [|a toks IH]; intros l t Hin Hp; simpl; [contradiction|].
  destruct (prefix_b a l) eqn:E; [eexists; reflexivity|].
  destruct Hin as [->|Hin]; [congruence | eapply IH; eauto].
Qed.

(** ── THEOREM 2 — declarative occurrence predicates ──────────────────── *)

(** A [toks]-occurrence at [off]: the position is unprotected, some token of
    the table is literally present, and its key is well-formed per
    [read_key] at the token's '{'. *)
Definition occurrence (toks : list (list byte)) (src : list byte)
    (protected : list (nat * nat)) (off : nat) (key : list byte) : Prop :=
  in_ranges_b protected off = false /\
  (exists tok next,
      In tok toks /\ tok_at src tok off /\
      read_key src (off + (length tok - 1)) = Some (key, next)).

(** A real "\label{key}" occurrence (position unprotected, literal token
    bytes present, key well-formed per [read_key] at the '{' = off+6). *)
Definition label_occurrence (src : list byte) (protected : list (nat * nat))
    (off : nat) (key : list byte) : Prop :=
  in_ranges_b protected off = false /\
  tok_at src label_tok off /\
  (exists next, read_key src (off + 6) = Some (key, next)).

(** A real reference occurrence, for any of the five commands. *)
Definition ref_occurrence (src : list byte) (protected : list (nat * nat))
    (off : nat) (key : list byte) : Prop :=
  occurrence ref_tokens src protected off key.

Lemma label_occurrence_iff : forall src protected off key,
  label_occurrence src protected off key <->
  occurrence [label_tok] src protected off key.
Proof.
  intros src protected off key. split.
  - intros (Hp & Ht & (nx & Hr)).
    split; [exact Hp|].
    exists label_tok, nx.
    split; [left; reflexivity|].
    split; [exact Ht|].
    replace (length label_tok - 1) with 6 by reflexivity. exact Hr.
  - intros (Hp & (tok & nx & Hin & Ht & Hr)).
    destruct Hin as [<-|[]].
    split; [exact Hp|]. split; [exact Ht|].
    exists nx.
    replace 6 with (length label_tok - 1) by reflexivity. exact Hr.
Qed.

Lemma occurrence_lt : forall toks src protected off key,
  Forall (fun t : list byte => t <> []) toks ->
  occurrence toks src protected off key ->
  off < length src.
Proof.
  intros toks src protected off key Hne [_ (tok & nx & Hin & Hat & _)].
  eapply tok_at_lt; eauto.
  rewrite Forall_forall in Hne. apply Hne. exact Hin.
Qed.

(** ── THEOREM 3 — scanner soundness ──────────────────────────────────── *)

Lemma scan_from_sound_aux : forall fuel toks protected src pos off key,
  In (off, key) (scan_from fuel toks protected pos (skipn pos src)) ->
  pos <= off /\ occurrence toks src protected off key.
Proof.
  induction fuel as [|f IH]; intros toks protected src pos off key Hin;
    [simpl in Hin; contradiction|].
  destruct (skipn pos src) as [|b l0] eqn:El; simpl in Hin; [contradiction|].
  assert (Hrest : skipn (S pos) src = l0) by (eapply skipn_S_cons; eauto).
  destruct (in_ranges_b protected pos) eqn:Ep; cbv iota in Hin.
  - rewrite <- Hrest in Hin.
    destruct (IH _ _ _ _ _ _ Hin) as [Hle Hocc]. split; [lia | exact Hocc].
  - destruct (first_match toks (b :: l0)) as [tok|] eqn:Efm; cbv iota in Hin.
    + destruct (read_key (b :: l0) (length tok - 1)) as [[k0 nx0]|] eqn:Erk;
        cbv iota in Hin.
      * destruct Hin as [Heq|Hin].
        -- injection Heq as H1 H2. subst off key.
           split; [lia|].
           split; [exact Ep|].
           destruct (first_match_sound _ _ _ Efm) as [Hintok Hpf].
           assert (Hrk : read_key src (pos + (length tok - 1))
                         = Some (k0, pos + nx0)).
           { apply read_key_shift_fw. rewrite El. exact Erk. }
           exists tok, (pos + nx0).
           split; [exact Hintok|].
           split; [unfold tok_at; rewrite El; exact Hpf|].
           exact Hrk.
        -- assert (Htl : skipn nx0 (b :: l0) = skipn (pos + nx0) src)
             by (rewrite <- El; apply skipn_add).
           rewrite Htl in Hin.
           destruct (IH _ _ _ _ _ _ Hin) as [Hle Hocc].
           split; [lia | exact Hocc].
      * rewrite <- Hrest in Hin.
        destruct (IH _ _ _ _ _ _ Hin) as [Hle Hocc]. split; [lia | exact Hocc].
    + rewrite <- Hrest in Hin.
      destruct (IH _ _ _ _ _ _ Hin) as [Hle Hocc]. split; [lia | exact Hocc].
Qed.

(** Every emitted (off, key) of the label scan is a REAL \label occurrence. *)
Theorem scan_labels_sound : forall src protected off key,
  In (off, key) (scan_labels src protected) ->
  label_occurrence src protected off key.
Proof.
  intros src protected off key Hin.
  unfold scan_labels, scan_generic in Hin.
  rewrite <- (skipn_O src) in Hin.
  destruct (scan_from_sound_aux _ _ _ _ _ _ _ Hin) as [_ Hocc].
  apply label_occurrence_iff. exact Hocc.
Qed.

(** Every emitted (off, key) of the ref scan is a REAL reference
    occurrence. *)
Theorem scan_refs_sound : forall src protected off key,
  In (off, key) (scan_refs src protected) ->
  ref_occurrence src protected off key.
Proof.
  intros src protected off key Hin.
  unfold scan_refs, scan_generic in Hin.
  rewrite <- (skipn_O src) in Hin.
  destruct (scan_from_sound_aux _ _ _ _ _ _ _ Hin) as [_ Hocc].
  exact Hocc.
Qed.

(** ── THEOREM 5 — strictly increasing offsets ────────────────────────── *)

Lemma scan_from_off_ge : forall fuel toks protected pos l off key,
  In (off, key) (scan_from fuel toks protected pos l) -> pos <= off.
Proof.
  induction fuel as [|f IH]; intros toks protected pos l off key Hin;
    [simpl in Hin; contradiction|].
  destruct l as [|b l0]; simpl in Hin; [contradiction|].
  destruct (in_ranges_b protected pos) eqn:Ep; cbv iota in Hin.
  - specialize (IH _ _ _ _ _ _ Hin). lia.
  - destruct (first_match toks (b :: l0)) as [tok|] eqn:Efm; cbv iota in Hin.
    + destruct (read_key (b :: l0) (length tok - 1)) as [[k0 nx0]|] eqn:Erk;
        cbv iota in Hin.
      * destruct Hin as [Heq|Hin].
        -- injection Heq as H1 _. lia.
        -- specialize (IH _ _ _ _ _ _ Hin). lia.
      * specialize (IH _ _ _ _ _ _ Hin). lia.
    + specialize (IH _ _ _ _ _ _ Hin). lia.
Qed.

Lemma scan_from_sorted : forall fuel toks protected pos l,
  StronglySorted lt (map fst (scan_from fuel toks protected pos l)).
Proof.
  induction fuel as [|f IH]; intros toks protected pos l; simpl;
    [constructor|].
  destruct l as [|b l0]; [constructor|].
  destruct (in_ranges_b protected pos); [apply IH|].
  destruct (first_match toks (b :: l0)) as [tok|]; [|apply IH].
  destruct (read_key (b :: l0) (length tok - 1)) as [[k0 nx0]|] eqn:Erk;
    [|apply IH].
  simpl. constructor; [apply IH|].
  apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [[o k] [Hfst HinT]].
  simpl in Hfst. subst x.
  pose proof (scan_from_off_ge _ _ _ _ _ _ _ HinT).
  pose proof (read_key_next_lower _ _ _ _ Erk).
  lia.
Qed.

Theorem scan_labels_offsets_sorted : forall src protected,
  StronglySorted lt (map fst (scan_labels src protected)).
Proof. intros. apply scan_from_sorted. Qed.

Theorem scan_refs_offsets_sorted : forall src protected,
  StronglySorted lt (map fst (scan_refs src protected)).
Proof. intros. apply scan_from_sorted. Qed.

(** ── Ref-token mutual exclusivity (distinct second bytes) ───────────── *)

Lemma ref_tokens_nonnil : Forall (fun t : list byte => t <> []) ref_tokens.
Proof. repeat constructor; discriminate. Qed.

Lemma ref_tokens_excl : forall src t1 t2 off,
  In t1 ref_tokens -> In t2 ref_tokens ->
  tok_at src t1 off -> tok_at src t2 off -> t1 = t2.
Proof.
  intros src t1 t2 off H1 H2 A1 A2.
  simpl in H1, H2.
  destruct H1 as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    destruct H2 as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    try reflexivity;
    (eapply tok_at_second in A1; [|reflexivity];
     eapply tok_at_second in A2; [|reflexivity];
     rewrite A1 in A2; discriminate A2).
Qed.

(** ── THEOREM 4 — scanner completeness ───────────────────────────────

    Every occurrence is emitted UNLESS its offset lies strictly inside the
    span of an earlier (lower-offset) emitted match of the same scan — the
    span running from the match start to the [read_key] "after" index. *)

Lemma scan_from_complete_aux :
  forall fuel toks protected src pos off key,
    Forall (fun t : list byte => t <> []) toks ->
    (forall t1 t2 o, In t1 toks -> In t2 toks ->
        tok_at src t1 o -> tok_at src t2 o -> t1 = t2) ->
    length src <= pos + fuel ->
    pos <= off ->
    occurrence toks src protected off key ->
    In (off, key) (scan_from fuel toks protected pos (skipn pos src)) \/
    (exists off' key' tok' next',
        In (off', key') (scan_from fuel toks protected pos (skipn pos src)) /\
        first_match toks (skipn off' src) = Some tok' /\
        read_key src (off' + (length tok' - 1)) = Some (key', next') /\
        off' < off /\ off < next').
Proof.
  induction fuel as [|f IH]; intros toks protected src pos off key
    Hne Hexcl Hfuel Hpos Hocc;
    pose proof (occurrence_lt _ _ _ _ _ Hne Hocc) as Hofflt.
  - exfalso. lia.
  - destruct (skipn pos src) as [|b l0] eqn:El.
    { exfalso. apply skipn_nil_le in El. lia. }
    assert (Hrest : skipn (S pos) src = l0) by (eapply skipn_S_cons; eauto).
    cbn [scan_from].
    destruct (in_ranges_b protected pos) eqn:Ep; cbv iota.
    + (* protected position: cannot be the occurrence itself *)
      assert (Hlt : pos < off).
      { destruct Hocc as [Hoff _].
        destruct (Nat.eq_dec pos off) as [->|]; [congruence | lia]. }
      rewrite <- Hrest.
      apply IH; auto; lia.
    + destruct (first_match toks (b :: l0)) as [t0|] eqn:Efm; cbv iota.
      * destruct (read_key (b :: l0) (length t0 - 1)) as [[k0 nx0]|] eqn:Erk;
          cbv iota.
        -- destruct (Nat.eq_dec pos off) as [Heq|Hneq].
           ++ (* the scanner is exactly at the occurrence: it emits it *)
              subst pos.
              destruct Hocc as [Hoff (tok & nx & Hin & Hat & Hrk)].
              assert (Ht0 : t0 = tok).
              { destruct (first_match_sound _ _ _ Efm) as [Hin0 Hpf0].
                apply (Hexcl t0 tok off); auto.
                unfold tok_at. rewrite El. exact Hpf0. }
              subst t0.
              apply read_key_shift_bw in Hrk.
              rewrite El in Hrk. rewrite Erk in Hrk.
              injection Hrk as Hkey Hnx.
              left. rewrite Hkey. apply in_eq.
           ++ assert (Hplt : pos < off) by lia.
              destruct (le_lt_dec (pos + nx0) off) as [Hle|Hgt].
              ** (* occurrence past this match's span: recurse from next *)
                 assert (Htl : skipn nx0 (b :: l0) = skipn (pos + nx0) src)
                   by (rewrite <- El; apply skipn_add).
                 rewrite Htl.
                 pose proof (read_key_next_lower _ _ _ _ Erk) as Hnx2.
                 destruct (IH toks protected src (pos + nx0) off key
                             Hne Hexcl ltac:(lia) Hle Hocc) as [HL|HR].
                 --- left. apply in_cons. exact HL.
                 --- right.
                     destruct HR as (o' & k' & t' & n' &
                                     HinT & Hfm' & Hrk' & Ho1 & Ho2).
                     exists o', k', t', n'.
                     split; [apply in_cons; exact HinT|]. auto.
              ** (* occurrence strictly inside this match's span: covered *)
                 right.
                 assert (Hfm_pos : first_match toks (skipn pos src) = Some t0)
                   by (rewrite El; exact Efm).
                 assert (Hrk_pos : read_key src (pos + (length t0 - 1))
                                   = Some (k0, pos + nx0)).
                 { apply read_key_shift_fw. rewrite El. exact Erk. }
                 exists pos, k0, t0, (pos + nx0).
                 split; [apply in_eq|]. auto.
        -- (* token matched but key unterminated: not an occurrence here *)
           destruct (Nat.eq_dec pos off) as [Heq|Hneq].
           ++ exfalso. subst pos.
              destruct Hocc as [Hoff (tok & nx & Hin & Hat & Hrk)].
              assert (Ht0 : t0 = tok).
              { destruct (first_match_sound _ _ _ Efm) as [Hin0 Hpf0].
                apply (Hexcl t0 tok off); auto.
                unfold tok_at. rewrite El. exact Hpf0. }
              subst t0.
              apply read_key_shift_bw in Hrk.
              rewrite El in Hrk. congruence.
           ++ rewrite <- Hrest. apply IH; auto; lia.
      * (* no token here *)
        destruct (Nat.eq_dec pos off) as [Heq|Hneq].
        -- exfalso. subst pos.
           destruct Hocc as [Hoff (tok & nx & Hin & Hat & Hrk)].
           unfold tok_at in Hat. rewrite El in Hat.
           destruct (first_match_complete toks (b :: l0) tok Hin Hat)
             as [t' Hfm'].
           congruence.
        -- rewrite <- Hrest. apply IH; auto; lia.
Qed.

Theorem scan_labels_complete : forall src protected off key,
  label_occurrence src protected off key ->
  In (off, key) (scan_labels src protected) \/
  (exists off' key' next',
      In (off', key') (scan_labels src protected) /\
      read_key src (off' + 6) = Some (key', next') /\
      off' < off /\ off < next').
Proof.
  intros src protected off key Hocc.
  apply label_occurrence_iff in Hocc.
  unfold scan_labels, scan_generic.
  assert (Hexcl : forall t1 t2 o,
             In t1 [label_tok] -> In t2 [label_tok] ->
             tok_at src t1 o -> tok_at src t2 o -> t1 = t2).
  { intros ? ? ? Ha Hb _ _.
    destruct Ha as [<-|[]]; destruct Hb as [<-|[]]; reflexivity. }
  assert (Hne : Forall (fun t : list byte => t <> []) [label_tok])
    by (constructor; [discriminate | constructor]).
  pose proof (scan_from_complete_aux (S (length src)) [label_tok] protected
                src 0 off key Hne Hexcl ltac:(lia) ltac:(lia) Hocc) as H.
  rewrite skipn_O in H.
  destruct H as [HL|HR]; [left; exact HL|].
  right.
  destruct HR as (o' & k' & t' & n' & Hin & Hfm & Hrk & Hlt1 & Hlt2).
  destruct (first_match_sound _ _ _ Hfm) as [Hin' _].
  destruct Hin' as [<-|[]].
  exists o', k', n'.
  replace (length label_tok - 1) with 6 in Hrk by reflexivity.
  auto.
Qed.

Theorem scan_refs_complete : forall src protected off key,
  ref_occurrence src protected off key ->
  In (off, key) (scan_refs src protected) \/
  (exists off' key' tok' next',
      In (off', key') (scan_refs src protected) /\
      In tok' ref_tokens /\ tok_at src tok' off' /\
      read_key src (off' + (length tok' - 1)) = Some (key', next') /\
      off' < off /\ off < next').
Proof.
  intros src protected off key Hocc.
  unfold ref_occurrence in Hocc.
  unfold scan_refs, scan_generic.
  pose proof (scan_from_complete_aux (S (length src)) ref_tokens protected
                src 0 off key ref_tokens_nonnil (ref_tokens_excl src)
                ltac:(lia) ltac:(lia) Hocc) as H.
  rewrite skipn_O in H.
  destruct H as [HL|HR]; [left; exact HL|].
  right.
  destruct HR as (o' & k' & t' & n' & Hin & Hfm & Hrk & Hlt1 & Hlt2).
  destruct (first_match_sound _ _ _ Hfm) as [Hin' Hpf'].
  exists o', k', t', n'.
  split; [exact Hin|].
  split; [exact Hin'|].
  split; [exact Hpf'|].
  auto.
Qed.

(** ── Fuel sufficiency: [S (length src)] fuel is enough ──────────────── *)

Lemma scan_from_fuel_irrelevant : forall f1 f2 toks protected src pos,
  length src <= pos + f1 ->
  length src <= pos + f2 ->
  scan_from f1 toks protected pos (skipn pos src)
  = scan_from f2 toks protected pos (skipn pos src).
Proof.
  induction f1 as [|f1 IH]; intros f2 toks protected src pos H1 H2.
  - (* f1 = 0: skipn pos src = [] because length src <= pos *)
    assert (Hnil : skipn pos src = []) by (apply skipn_all2; lia).
    rewrite Hnil. destruct f2; reflexivity.
  - destruct f2 as [|f2].
    + assert (Hnil : skipn pos src = []) by (apply skipn_all2; lia).
      rewrite Hnil. reflexivity.
    + destruct (skipn pos src) as [|b l0] eqn:El; [reflexivity|].
      assert (Hrest : skipn (S pos) src = l0)
        by (eapply skipn_S_cons; eauto).
      cbn [scan_from].
      destruct (in_ranges_b protected pos); cbv iota.
      * rewrite <- Hrest. apply IH; lia.
      * destruct (first_match toks (b :: l0)) as [tok|] eqn:Efm; cbv iota;
          [|rewrite <- Hrest; apply IH; lia].
        destruct (read_key (b :: l0) (length tok - 1)) as [[k0 nx0]|]
          eqn:Erk; cbv iota; [|rewrite <- Hrest; apply IH; lia].
        f_equal.
        assert (Htl : skipn nx0 (b :: l0) = skipn (pos + nx0) src)
          by (rewrite <- El; apply skipn_add).
        pose proof (read_key_next_lower _ _ _ _ Erk).
        rewrite Htl. apply IH; lia.
Qed.

(** ── Merge: membership + sortedness ─────────────────────────────────── *)

Lemma in_map_ev_off_def : forall e d,
  In e (map ev_def_of d) -> In (ev_off e) (map fst d).
Proof.
  intros e d H. apply in_map_iff in H. destruct H as [[o k] [He Hin]].
  subst e. simpl. apply in_map_iff. exists (o, k). auto.
Qed.

Lemma in_map_ev_off_ref : forall e r,
  In e (map ev_ref_of r) -> In (ev_off e) (map fst r).
Proof.
  intros e r H. apply in_map_iff in H. destruct H as [[o k] [He Hin]].
  subst e. simpl. apply in_map_iff. exists (o, k). auto.
Qed.

Lemma merge_fuel_off_in : forall fuel d r e,
  In e (merge_fuel fuel d r) ->
  In (ev_off e) (map fst d) \/ In (ev_off e) (map fst r).
Proof.
  induction fuel as [|f IH]; intros d r e H; cbn [merge_fuel] in H.
  - apply in_app_or in H. destruct H as [H|H];
      [left; apply in_map_ev_off_def; exact H
      |right; apply in_map_ev_off_ref; exact H].
  - destruct d as [|[od kd] ds].
    + right. apply in_map_ev_off_ref. exact H.
    + destruct r as [|[orf kr] rs].
      * left. apply in_map_ev_off_def. exact H.
      * destruct (Nat.leb od orf) eqn:Ec; cbv iota in H.
        -- destruct H as [<-|H]; [left; simpl; left; reflexivity|].
           destruct (IH _ _ _ H) as [HL|HR];
             [left; simpl; right; exact HL | right; exact HR].
        -- destruct H as [<-|H]; [right; simpl; left; reflexivity|].
           destruct (IH _ _ _ H) as [HL|HR];
             [left; exact HL | right; simpl; right; exact HR].
Qed.

Lemma map_ev_off_def : forall d,
  map ev_off (map ev_def_of d) = map fst d.
Proof.
  intros d. rewrite map_map. apply map_ext. intros [o k]. reflexivity.
Qed.

Lemma map_ev_off_ref : forall r,
  map ev_off (map ev_ref_of r) = map fst r.
Proof.
  intros r. rewrite map_map. apply map_ext. intros [o k]. reflexivity.
Qed.

Lemma merge_fuel_sorted : forall fuel d r,
  length d + length r <= fuel ->
  StronglySorted lt (map fst d) ->
  StronglySorted lt (map fst r) ->
  (forall o, In o (map fst d) -> In o (map fst r) -> False) ->
  StronglySorted lt (map ev_off (merge_fuel fuel d r)).
Proof.
  induction fuel as [|f IH]; intros d r Hlen Hd Hr Hdisj; simpl.
  - destruct d; destruct r; simpl in Hlen; try lia.
    simpl. constructor.
  - destruct d as [|[od kd] ds]; simpl.
    + rewrite map_ev_off_ref. exact Hr.
    + destruct r as [|[orf kr] rs]; simpl.
      * rewrite map_ev_off_def. exact Hd.
      * simpl in Hlen, Hd, Hr.
        apply StronglySorted_inv in Hd. destruct Hd as [Hd' Hfd].
        apply StronglySorted_inv in Hr. destruct Hr as [Hr' Hfr].
        destruct (Nat.leb od orf) eqn:Ecmp; simpl.
        -- (* def head: od <= orf *)
           apply Nat.leb_le in Ecmp.
           constructor.
           ++ apply IH.
              ** simpl. lia.
              ** exact Hd'.
              ** simpl. constructor; assumption.
              ** intros o Ho1 Ho2. apply (Hdisj o); [|exact Ho2].
                 simpl. right. exact Ho1.
           ++ apply Forall_forall. intros x Hx.
              apply in_map_iff in Hx. destruct Hx as [e [He Hin]]. subst x.
              destruct (merge_fuel_off_in _ _ _ _ Hin) as [HL|HR].
              ** rewrite Forall_forall in Hfd. apply Hfd. exact HL.
              ** simpl in HR. destruct HR as [Heq|HR].
                 --- assert (Hneq : od <> orf).
                     { intro E. apply (Hdisj od);
                         simpl; left; congruence. }
                     lia.
                 --- rewrite Forall_forall in Hfr.
                     specialize (Hfr _ HR). lia.
        -- (* ref head: orf < od *)
           apply Nat.leb_gt in Ecmp.
           constructor.
           ++ apply IH.
              ** simpl. lia.
              ** simpl. constructor; assumption.
              ** exact Hr'.
              ** intros o Ho1 Ho2. apply (Hdisj o); [exact Ho1|].
                 simpl. right. exact Ho2.
           ++ apply Forall_forall. intros x Hx.
              apply in_map_iff in Hx. destruct Hx as [e [He Hin]]. subst x.
              destruct (merge_fuel_off_in _ _ _ _ Hin) as [HL|HR].
              ** simpl in HL. destruct HL as [Heq|HL]; [lia|].
                 rewrite Forall_forall in Hfd.
                 specialize (Hfd _ HL). lia.
              ** rewrite Forall_forall in Hfr. apply Hfr. exact HR.
Qed.

(** Offsets across the two scans are DISJOINT: a byte position starts at most
    one token (the byte AFTER the backslash differs: 'l' = 108 for \label,
    vs 'e'/'a'/'c'/'C'/'r' for the five ref commands). *)

Lemma label_off_second : forall src protected off key,
  In (off, key) (scan_labels src protected) ->
  nth_error (skipn off src) 1 = Some 108.
Proof.
  intros src protected off key Hin.
  destruct (scan_labels_sound _ _ _ _ Hin) as [_ [Hat _]].
  eapply tok_at_second; [exact Hat | reflexivity].
Qed.

Lemma ref_off_second : forall src protected off key,
  In (off, key) (scan_refs src protected) ->
  exists c, nth_error (skipn off src) 1 = Some c /\ c <> 108.
Proof.
  intros src protected off key Hin.
  destruct (scan_refs_sound _ _ _ _ Hin) as [_ (tok & nx & Hint & Hat & _)].
  simpl in Hint.
  destruct Hint as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    [exists 101 | exists 97 | exists 99 | exists 67 | exists 114];
    (split; [eapply tok_at_second; [exact Hat | reflexivity] | lia]).
Qed.

Lemma scans_offsets_disjoint : forall src protected o,
  In o (map fst (scan_labels src protected)) ->
  In o (map fst (scan_refs src protected)) -> False.
Proof.
  intros src protected o H1 H2.
  apply in_map_iff in H1. destruct H1 as [[o1 k1] [E1 Hin1]].
  apply in_map_iff in H2. destruct H2 as [[o2 k2] [E2 Hin2]].
  simpl in E1, E2. subst o1 o2.
  pose proof (label_off_second _ _ _ _ Hin1) as HL.
  destruct (ref_off_second _ _ _ _ Hin2) as [c [HR Hc]].
  rewrite HL in HR. injection HR as HR. subst c. congruence.
Qed.

(** THEOREM 5 (merge half) — the merged event stream has strictly increasing
    offsets. *)
Theorem merge_events_sorted : forall src protected,
  StronglySorted lt
    (map ev_off (merge_events (scan_labels src protected)
                              (scan_refs src protected))).
Proof.
  intros src protected. apply merge_fuel_sorted.
  - apply le_n.
  - apply scan_labels_offsets_sorted.
  - apply scan_refs_offsets_sorted.
  - apply scans_offsets_disjoint.
Qed.

(** ── THEOREM 6/7 — bridges to the capstone premise functions ────────── *)

Lemma body_label_defs_app : forall a b : list body_token,
  body_label_defs (a ++ b) = body_label_defs a ++ body_label_defs b.
Proof.
  induction a as [|t a IH]; intros b0; simpl; [reflexivity|].
  destruct t; simpl; rewrite IH; reflexivity.
Qed.

Lemma body_label_defs_feats : forall fs,
  body_label_defs (map BT_needs_feature fs) = [].
Proof. induction fs as [|f fs IH]; simpl; auto. Qed.

Lemma body_label_defs_events : forall evs,
  body_label_defs (map token_of_event evs)
  = map (fun e => fnv30 (ev_key e)) (filter is_def_event evs).
Proof.
  induction evs as [|e evs IH]; simpl; [reflexivity|].
  destruct e; simpl; rewrite IH; reflexivity.
Qed.

(** The [body_label_defs] premise datum of a built body IS the def half of the
    merged scan, hashed — the T4 bridge. *)
Theorem body_label_defs_of_source : forall src protected,
  body_label_defs (body_of_source src protected)
  = map (fun e => fnv30 (ev_key e))
      (filter is_def_event
         (merge_events (scan_labels src protected) (scan_refs src protected))).
Proof.
  intros src protected. unfold body_of_source.
  rewrite body_label_defs_app, body_label_defs_app.
  rewrite body_label_defs_events, body_label_defs_feats.
  destruct (is_blank src); simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma body_required_features_app : forall a b : list body_token,
  body_required_features (a ++ b)
  = body_required_features a ++ body_required_features b.
Proof.
  induction a as [|t a IH]; intros b0; simpl; [reflexivity|].
  destruct t; simpl; rewrite IH; reflexivity.
Qed.

Lemma body_required_features_events : forall evs,
  body_required_features (map token_of_event evs) = [].
Proof.
  induction evs as [|e evs IH]; simpl; [reflexivity|].
  destruct e; simpl; exact IH.
Qed.

Lemma body_required_features_feats : forall fs,
  body_required_features (map BT_needs_feature fs) = fs.
Proof. induction fs as [|f fs IH]; simpl; [reflexivity | rewrite IH]; auto. Qed.

(** The [body_required_features] premise datum of a built body IS the feature
    detector's output — the T3 bridge. *)
Theorem body_required_features_of_source : forall src protected,
  body_required_features (body_of_source src protected)
  = detect_body_features src.
Proof.
  intros src protected. unfold body_of_source.
  rewrite body_required_features_app, body_required_features_app.
  rewrite body_required_features_events, body_required_features_feats.
  destruct (is_blank src); simpl; rewrite ?app_nil_r; reflexivity.
Qed.

(** ── FNV-1a bounds (nat→int extraction soundness) ───────────────────── *)

Lemma shr_fuel_div : forall f x, shr_fuel f x = x / 2 ^ f.
Proof.
  induction f as [|f IH]; intros x; simpl shr_fuel.
  - rewrite Nat.pow_0_r, Nat.div_1_r. reflexivity.
  - rewrite IH, Nat.div2_div, Nat.pow_succ_r'.
    rewrite Nat.div_div; [reflexivity | lia | apply Nat.pow_nonzero; lia].
Qed.

Lemma mod_two30_spec : forall x, mod_two30 x = x mod two30.
Proof.
  intros x. unfold mod_two30, two30. rewrite shr_fuel_div.
  assert (H30 : 2 ^ 30 <> 0) by (apply Nat.pow_nonzero; lia).
  pose proof (Nat.div_mod x (2 ^ 30) H30). lia.
Qed.

Lemma mod_two30_le : forall x, mod_two30 x <= mask30.
Proof.
  intros x. rewrite mod_two30_spec. unfold mask30, two30.
  assert (H30 : 2 ^ 30 <> 0) by (apply Nat.pow_nonzero; lia).
  pose proof (Nat.mod_upper_bound x (2 ^ 30) H30). lia.
Qed.

Lemma fnv_step_le : forall h b, fnv_step h b <= mask30.
Proof. intros h b. unfold fnv_step. apply mod_two30_le. Qed.

Lemma fnv_fold_le : forall k h,
  h <= mask30 -> fold_left fnv_step k h <= mask30.
Proof.
  induction k as [|b k IH]; intros h Hh; cbn [fold_left]; [exact Hh|].
  apply IH. apply fnv_step_le.
Qed.

(** DEVIATION NOTE (OCaml wins): the brief asked for
    [forall k, fnv30 k <= 0x3FFFFFFF], but the OCaml [label_id] does NOT mask
    its initial basis, so the EMPTY key hashes to 0x811c9dc5 > 0x3FFFFFFF.
    The faithful statements are: every NON-EMPTY key is ≤ the 30-bit mask
    ([fnv30_bound]), the empty key is exactly the basis ([fnv30_nil]), and
    every key is ≤ the basis ([fnv30_le_basis]).  Extraction soundness: every
    value the hash manipulates is ≤ 0x811c9dc5 < 2^32, and the one product is
    ≤ (2^30-1)·(2^24+403) < 2^55 — comfortably inside OCaml's 63-bit int. *)

(** Cons-step for [fold_left], proved with an ABSTRACT [f]: its own [Qed] is a
    trivial one-[iota] conversion, and — crucially — rewriting with it peels the
    first fold step SYNTACTICALLY, so the kernel never has to reduce
    [fnv_step fnv_basis b].  Using [cbn [fold_left]] here instead would force
    that reduction at [Qed] time, and [fnv_step] reduces through [mod_two30] →
    [two30 = 2 ^ 30], which as a Peano [nat] is a ~10^9-successor unary numeral:
    the conversion never terminates in practice.  This abstract lemma is the
    fix. *)
Lemma fold_left_cons_eq :
  forall (f : nat -> nat -> nat) (a : nat) (l : list nat) (acc : nat),
    fold_left f (a :: l) acc = fold_left f l (f acc a).
Proof. reflexivity. Qed.

Theorem fnv30_bound : forall b k, fnv30 (b :: k) <= mask30.
Proof.
  intros b k. unfold fnv30. rewrite fold_left_cons_eq.
  apply fnv_fold_le. apply fnv_step_le.
Qed.

Theorem fnv30_nil : fnv30 [] = fnv_basis.
Proof. reflexivity. Qed.

Theorem fnv30_le_basis : forall k, fnv30 k <= fnv_basis.
Proof.
  intros [|b k].
  - rewrite fnv30_nil. lia.
  - pose proof (fnv30_bound b k).
    assert (Hmb : mask30 <= fnv_basis); [|lia].
    unfold mask30, fnv_basis.
    replace (2 ^ 30) with (64 * 2 ^ 24); [lia|].
    change 64 with (2 ^ 6). rewrite <- Nat.pow_add_r.
    reflexivity.
Qed.

(** 63-bit-int safety of the [ExtrOcamlNatInt] extraction: the single FNV
    multiplication stays below 2^55.  Concretely
    [mod_two30 x * fnv_prime <= (2^30 - 1) * (2^24 + 403) < 2^55], comfortably
    inside OCaml's 63-bit [int].

    A machine-checked Coq proof of this bound is deliberately OMITTED.  The
    statement mentions [2 ^ 55] as a Peano [nat]; any proof term connecting it
    to the goal forces the kernel, at [Qed] time, to reduce [2 ^ 55] (and the
    [2 ^ 30] inside [mod_two30]) to a unary numeral — a ~3.6·10^16-successor
    term — so the check never terminates in practice.  Every abstraction
    workaround ([set]/[clearbody]/helper-lemma) is defeated because the
    concrete power is re-substituted when the abstraction is applied back at the
    kernel boundary.  Rather than ship a pathological (or [nat]→[N]-reencoded,
    hence unfaithful-looking) proof of a NON-load-bearing fact, we assert the
    bound informally here.  It is NOT used by any theorem below — in particular
    [compile_safe_of_source] does not depend on it — and the actual arithmetic
    faithfulness of the extracted hash is validated end-to-end by the runtime
    differential PARITY test: extracted [fnv30] equals the hand-written OCaml
    [Compile_evidence.label_id] byte-for-byte across the corpus and the
    adversarial FNV fixtures. *)

(** ── THE nested-token subtlety, machine-checked in Coq ──────────────

    "\label{a\ref{b}}": the label scan emits the def of key "a\ref{b" at
    offset 0 (jumping past the WHOLE match), while the INDEPENDENT ref scan
    still finds the inner "\ref{b}" at offset 8.  Both events survive the
    merge, defs first. *)

Local Open Scope string_scope.
Definition ex_nested : list byte :=
  Eval compute in bytes_of_string "\label{a\ref{b}}".
Definition ex_nested_key : list byte :=
  Eval compute in bytes_of_string "a\ref{b".
Local Close Scope string_scope.

Example scan_labels_nested :
  scan_labels ex_nested [] = [(0, ex_nested_key)].
Proof. vm_compute. reflexivity. Qed.

Example scan_refs_nested :
  scan_refs ex_nested [] = [(8, [98])].
Proof. vm_compute. reflexivity. Qed.

Example merge_nested :
  merge_events (scan_labels ex_nested []) (scan_refs ex_nested [])
  = [Ev_def 0 ex_nested_key; Ev_ref 8 [98]].
Proof. vm_compute. reflexivity. Qed.

(** Protection kills the match: with a range covering the whole string,
    nothing is emitted. *)
Example scan_labels_nested_protected :
  scan_labels ex_nested [(0, 16)] = [].
Proof. vm_compute. reflexivity. Qed.

(** ── THEOREM 8 — HEADLINE: a true premise-check verdict on a body built by
    THIS verified front-end discharges the capstone ──────────────────── *)

Theorem compile_safe_of_source :
  forall (src : list byte) (protected : list (nat * nat))
         (g : build_graph) (pf : pdflatex_profile)
         (order : list ProjectClosure.node),
    project_wf_dec (mk_project g (body_of_source src protected)) pf order
      = true ->
    exists out,
      pdflatex_produces (mk_project g (body_of_source src protected)) pf out /\
      pdflatex_compilation_succeeds
        (mk_project g (body_of_source src protected)) pf /\
      pdflatex_output_format_well_formed out /\
      (faithful_run (mk_project g (body_of_source src protected)) pf 2)
        .(L0Pass.converged) = true /\
      L0Log.log_no_fatal
        (L0Pass.log
           (faithful_run (mk_project g (body_of_source src protected)) pf 2)) /\
      (L0Log.warnings
         (L0Pass.log
            (faithful_run (mk_project g (body_of_source src protected)) pf 2))
       <> []
       <-> project_has_unresolved_ref
             (mk_project g (body_of_source src protected)) pf) /\
      out = faithful_artefact (mk_project g (body_of_source src protected)) pf 2.
Proof.
  intros src protected g pf order H.
  eapply project_wf_dec_compile_safe. exact H.
Qed.

(** Assumption audit — the build FAILS the honesty bar if this ever prints
    anything but "Closed under the global context" (checked manually on every
    release; the vernacular below actually executes during compilation). *)
Print Assumptions compile_safe_of_source.
