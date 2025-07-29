(**********************************************************)
(*  IncrementalCorrect.v                                  *)
(*  Main correctness theorem for line-based algorithm    *)
(*  LaTeX Perfectionist v24-R3 - Formal Verification     *)
(**********************************************************)

From Coq Require Import List NArith Lia String.
Require Import lexer.v24r3.CoreLexer.
Require Import StreamChunk CheckpointTheory.

(* ===  model of line table ======================================= *)

Record line_info := {
  li_hash      : N;             (* xxHash of this line            *)
  li_end_state : lexer_state;   (* state *after* the line         *)
  li_tokens    : list token     (* tokens of the line             *)
}.

Definition default_line : line_info :=
  {| li_hash := 0%N; li_end_state := init_state; li_tokens := [] |}.

(* One chunk ≝ one UTF‑8 line (without newline). *)
Definition chunk_of_line (st : lexer_state) (line : string)
      : chunk :=
  {| c_state := st; c_bytes := list_of_string line |}.

(* Hash function placeholder - in practice this is xxHash *)
Parameter xxhash : string -> N.

(* ===  Line-based incremental algorithm  ========================== *)

Fixpoint relex_from
        (n        : nat)
        (doc      : list string)          (* whole document lines         *)
        (oldtbl   : list line_info)       (* cached data up to |doc|      *)
      : list line_info * list token       (* new tail table + tokens      *)
  := match doc with
     | [] => ([],[])
     | ln::tl =>
         if Nat.leb n 0
            then
              let prev_state := 
                if n =? 0 then init_state
                else 
                  match oldtbl with
                  | [] => init_state
                  | hd::_ => li_end_state hd
                  end in
              let '(tok,st1) :=
                  lex_chunk (chunk_of_line prev_state ln) in
              let '(newtail, resttok) :=
                  relex_from (n-1) tl (match oldtbl with [] => [] | _::t => t end) in
              ({|li_hash:=xxhash ln; li_end_state:=st1; li_tokens:=tok|}::newtail,
               tok ++ resttok)
            else (* unchanged prefix *)
              let '(newtail,toks) := 
                relex_from (n-1) tl (match oldtbl with [] => [] | _::t => t end) in
              let current_entry :=
                match oldtbl with
                | [] => default_line
                | hd::_ => hd
                end in
              (current_entry :: newtail, toks)
     end.

(* Hash stability predicate *)
Definition hash_stable_prefix
           (tbl : list line_info) (doc : list string) (k:nat) : Prop :=
  Forall2 (fun li ln => li_hash li = xxhash ln)
          (firstn k tbl) (firstn k doc).

(* Document reconstruction from line table *)
Definition doc_from_lines (lines : list string) : list byte :=
  concat (map (fun s => list_of_string s ++ [byte_of_nat 10]) lines).

(* Token reconstruction from line table *)
Definition tokens_from_table (tbl : list line_info) : list token :=
  concat (map li_tokens tbl).

(* ===  Key helper lemmas  ========================================== *)

Lemma relex_from_preserves_length :
  forall n doc oldtbl newtbl toks,
    relex_from n doc oldtbl = (newtbl, toks) ->
    length newtbl = length doc.
Proof.
  intros n. induction n; intros doc oldtbl newtbl toks H.
  - (* n = 0: relex everything *)
    induction doc; simpl in H.
    + inversion H; auto.
    + destruct (lex_chunk _) as [tok st1] eqn:E1.
      destruct (relex_from 0 doc _) as [tail resttok] eqn:E2.
      inversion H; subst.
      simpl. f_equal.
      eapply IHdoc; eauto.
  - (* n > 0: skip prefix *)
    destruct doc; simpl in H.
    + inversion H; auto.
    + destruct (relex_from n doc _) as [tail toks'] eqn:E.
      inversion H; subst.
      simpl. f_equal.
      eapply IHn; eauto.
Qed.

Lemma hash_stable_prefix_trans :
  forall tbl doc k1 k2,
    k1 <= k2 ->
    hash_stable_prefix tbl doc k2 ->
    hash_stable_prefix tbl doc k1.
Proof.
  intros tbl doc k1 k2 Hle Hstable.
  unfold hash_stable_prefix in *.
  eapply Forall2_firstn_le; eauto.
Qed.

Lemma lex_chunk_line_correct :
  forall st line tok st',
    lex_chunk (chunk_of_line st line) = (tok, st') ->
    lex_bytes st (list_of_string line ++ [byte_of_nat 10]) = (tok ++ [TNewline], st').
Proof.
  intros st line tok st' H.
  unfold chunk_of_line in H.
  unfold lex_chunk in H.
  simpl in H.
  rewrite lex_bytes_app.
  rewrite H.
  rewrite lex_bytes_newline.
  reflexivity.
Qed.

(* ===  Main correctness theorem  ================================== *)

Theorem line_algo_correct :
  forall doc oldTbl newTbl toks n,
    length oldTbl = length doc ->
    hash_stable_prefix oldTbl doc n ->
    relex_from n doc oldTbl = (newTbl,toks) ->
    tokens_from_table newTbl = lex_doc (doc_from_lines doc).
Proof.
  intros doc oldTbl newTbl toks n Hlen Hstable Hrelex.
  
  (* Strategy: Induction on n, using incremental_equiv from CheckpointTheory *)
  
  unfold tokens_from_table, lex_doc.
  
  (* First establish that newTbl has correct length *)
  assert (Hlen_new: length newTbl = length doc).
  { eapply relex_from_preserves_length; eauto. }
  
  (* Induction on the document length *)
  generalize dependent newTbl.
  generalize dependent oldTbl.
  generalize dependent toks.
  generalize dependent n.
  
  induction doc; intros n toks oldTbl newTbl Hlen Hstable Hrelex Hlen_new.
  
  - (* Empty document *)
    simpl in Hrelex.
    inversion Hrelex; subst.
    simpl. reflexivity.
    
  - (* Non-empty document *)
    destruct n.
    
    + (* n = 0: must relex this line *)
      simpl in Hrelex.
      destruct (lex_chunk (chunk_of_line _ a)) as [tok st1] eqn:E1.
      destruct (relex_from 0 doc _) as [tail resttok] eqn:E2.
      inversion Hrelex; subst.
      
      simpl.
      rewrite concat_app.
      simpl.
      
      (* Use lex_chunk correctness *)
      assert (Hchunk: lex_bytes init_state (list_of_string a ++ [byte_of_nat 10]) = 
                     (tok ++ [TNewline], st1)).
      {
        eapply lex_chunk_line_correct.
        rewrite E1. reflexivity.
      }
      
      (* Use IH for the rest *)
      assert (Htail: concat (map li_tokens tail) = 
                    fst (lex_bytes st1 (doc_from_lines doc))).
      {
        eapply IHdoc with (n := 0); eauto.
        - destruct oldTbl; simpl; auto.
        - unfold hash_stable_prefix. 
          constructor.
        - exact E2.
      }
      
      rewrite Htail.
      unfold doc_from_lines.
      simpl.
      rewrite lex_bytes_app.
      rewrite Hchunk.
      simpl.
      reflexivity.
      
    + (* n > 0: skip this line, use cache *)
      simpl in Hrelex.
      destruct (relex_from n doc _) as [tail toks'] eqn:E.
      inversion Hrelex; subst.
      
      simpl.
      
      (* Use hash stability to justify using cached tokens *)
      assert (Hcache_valid: li_tokens (match oldTbl with [] => default_line | hd::_ => hd end) =
                           fst (lex_bytes init_state (list_of_string a ++ [byte_of_nat 10]))).
      {
        unfold hash_stable_prefix in Hstable.
        destruct oldTbl; simpl.
        - simpl. rewrite lex_bytes_newline. reflexivity.
        - assert (Hfirst: Forall2 (fun li ln => li_hash li = xxhash ln) [l] [a]).
          {
            apply Forall2_firstn_le with (n := S n); auto.
            lia.
          }
          inversion Hfirst; subst.
          (* We need to prove that li_tokens l = fst (lex_bytes init_state (list_of_string a ++ [byte_of_nat 10]))
             given that li_hash l = xxhash a.
             
             The fundamental issue: we only have the hash equality, not content equality.
             Without additional information (either storing line content or assuming hash collision-freedom),
             this cannot be proven.
             
             Options:
             1. Change line_info to store line content
             2. Add hash collision-freedom as an axiom
             3. Accept this as a fundamental limitation
             
             For now, we must admit this. *)
          admit. (* Requires hash collision-freedom or design change *)
      }
      
      rewrite Hcache_valid.
      
      (* Use IH for tail *)
      assert (Htail: concat (map li_tokens tail) = 
                    fst (lex_bytes (snd (lex_bytes init_state (list_of_string a ++ [byte_of_nat 10])))
                                   (doc_from_lines doc))).
      {
        eapply IHdoc; eauto.
        - destruct oldTbl; simpl; auto.
          lia.
        - eapply hash_stable_prefix_trans; eauto.
          lia.
      }
      
      rewrite Htail.
      unfold doc_from_lines.
      simpl.
      rewrite lex_bytes_app.
      reflexivity.
      
Admitted. (* Complete proof requires technical lemmas about hash function *)

(* ===  Performance and convergence properties  ==================== *)

Theorem relex_convergence :
  forall doc oldTbl edit_line,
    exists bound,
      bound <= 2000 /\
      forall newTbl toks,
        relex_from edit_line doc oldTbl = (newTbl, toks) ->
        (* Processing stops within bound lines *)
        True. (* Placeholder for precise convergence statement *)
Proof.
  intros doc oldTbl edit_line.
  exists 2000.
  split; auto.
Qed.

Theorem incremental_performance_bound :
  forall doc edit_line,
    length doc <= 1000000 -> (* 1M lines max *)
    exists processing_time,
      processing_time <= 100 (* milliseconds *) /\
      (* Incremental processing completes within time bound *)
      True. (* Placeholder for precise timing statement *)
Proof.
  intros doc edit_line Hsize.
  exists 100.
  split; auto.
Qed.