(** * Strict.Explain — why a file is outside the fragment (diagnostics only).

    ADR-012, milestone M2 phase 2.  When [DecideBytes.decide_bytes] answers
    [NotStrict], the driver (latex-parse/strict/strict_decide.ml, file mode)
    prints the offset of the first byte that puts the file outside the
    fragment and the construct.  [explain] computes it with the SAME lexer,
    front-matter matcher and kernel membership functions the decider uses.

    It is DIAGNOSTIC, not proved: no theorem rests on it and no verdict is
    computed from it (the verdict is [decide_bytes]'s).  Its agreement with
    the decider ([explain] is [None] exactly on the files [decide_bytes]
    decides) is checked on every document of the byte-level evidence by
    scripts/tools/strict_differential.py. *)

From Coq Require Import List Ascii Bool Arith.
Import ListNotations.
From LaTeXPerfectionist.Strict Require Import Syntax Contract Semantics Decide Lexer Front DecideBytes.

Inductive why_out :=
| WTooBig              (* more than max_file_bytes *)
| WLexBad (k : bad)    (* a byte the reader gives no token of the fragment *)
| WPrologue            (* not \documentclass{article} ... \begin{document} *)
| WToken               (* a token with no rule: another control symbol,
                          \end not followed by {document} *)
| WNotAdmitted         (* a character outside the fragment's set, or a name
                          defined in the configuration without a signature *)
| WScriptArg           (* ^ or _ not followed by a character or { *)
| WBound               (* the kernel's capacity bounds *)
| WEndsDollar          (* the kernel stream ends with $ *)
| WArgForm.            (* step 2, slice A: a one-argument command not
                          followed by the brace of its argument, or an
                          argument that does not close before
                          \end{document} or the end of the file
                          (Decide.wfa) *)

Definition rtok_eqb (a b : rtok) : bool :=
  match a, b with
  | RChar x, RChar y => Ascii.eqb x y
  | RSpace, RSpace | RPar, RPar | RBgroup, RBgroup | REgroup, REgroup
  | RMath, RMath | RSup, RSup | RSub, RSub => true
  | RWord m, RWord n => name_eqb m n
  | RSym x, RSym y => Ascii.eqb x y
  | _, _ => false
  end.

(** Match [exp] at the head of [ts]: the rest, or the first token that
    does not fit ([None]: the file ended). *)
Fixpoint expect (exp : list rtok) (ts : list lt) : option lt + list lt :=
  match exp, ts with
  | [], _ => inr ts
  | e :: exp', t :: r => if rtok_eqb e (lt_tok t) then expect exp' r else inl (Some t)
  | _ :: _, [] => inl None
  end.

Definition cmd_seq (n : name) (w : list ascii) : list rtok :=
  RWord n :: RBgroup :: map RChar w ++ [REgroup].

Definition blame (t : lt) (w : why_out) : nat * why_out :=
  match lt_tok t with
  | RBad k => (lt_off t, WLexBad k)
  | _ => (lt_off t, w)
  end.

Definition explain_prologue (L : lexcon) (eof : nat) (ts : list lt)
  : (nat * why_out) + list lt :=
  match expect (cmd_seq (lx_docclass L) (lx_class L)) (skip_fill L ts) with
  | inl (Some t) => inl (blame t WPrologue)
  | inl None => inl (eof, WPrologue)
  | inr r =>
      match expect (cmd_seq (lx_begin L) (lx_docenv L)) (skip_fill L r) with
      | inl (Some t) => inl (blame t WPrologue)
      | inl None => inl (eof, WPrologue)
      | inr rest => inr rest
      end
  end.

Fixpoint explain_body (L : lexcon) (ts : list lt) : option (nat * why_out) :=
  match ts with
  | [] => None
  | t :: rest =>
      match lt_tok t with
      | RBad k => Some (lt_off t, WLexBad k)
      | RSym c =>
          match sym_tok L c with
          | Some _ => explain_body L rest
          | None => Some (lt_off t, WToken)
          end
      | RWord n =>
          if name_eqb n (lx_par L) then explain_body L rest
          else if name_eqb n (lx_end L) then
            match braced (lx_end L) (lx_docenv L) ts with
            | Some _ => None
            | None => Some (lt_off t, WToken)
            end
          else explain_body L rest
      | _ => explain_body L rest
      end
  end.

Fixpoint first_not_admitted (K : contract) (ks : list ktok) : option ktok :=
  match ks with
  | [] => None
  | k :: r => if tok_ok K (k_tok k) then first_not_admitted K r else Some k
  end.

Fixpoint first_bad_script (ks : list ktok) : option ktok :=
  match ks with
  | [] => None
  | k :: r =>
      match k_tok k with
      | TScript _ =>
          match r with
          | k2 :: _ =>
              match k_tok k2 with
              | TChar _ | TOpen => first_bad_script r
              | _ => Some k
              end
          | [] => Some k
          end
      | _ => first_bad_script r
      end
  end.

(** Where [Decide.wfa] fails, counted as it counts: [Some (Some k)] at the
    token [k] (a one-argument command without its brace, or an
    [\end{document}] inside an argument), [Some None] at the end of the
    file (an argument still open), [None] when the arguments are well
    formed. *)
Fixpoint first_bad_arg (K : contract) (need : nat) (ks : list ktok) : option (option ktok) :=
  match ks with
  | [] => if Nat.eqb need 0 then None else Some None
  | k :: r =>
      match k_tok k with
      | TEnd => if Nat.eqb need 0 then None else Some (Some k)
      | TOpen => first_bad_arg K (if Nat.eqb need 0 then 0 else S need) r
      | TClose => first_bad_arg K (pred need) r
      | TCs n =>
          if is_argcmd K n then
            match r with
            | k2 :: r' =>
                match k_tok k2 with
                | TOpen => first_bad_arg K (S need) r'
                | _ => Some (Some k)
                end
            | [] => Some (Some k)
            end
          else first_bad_arg K need r
      | _ => first_bad_arg K need r
      end
  end.

(** The first token past a capacity bound, counted as [Decide.bounded]
    counts (C-94): a control word longer than [max_name] letters, or the
    token whose step first makes the run hold more than [max_groups] TeX
    groups ([Decide.groups]; for a two-token step, its first token). *)
Fixpoint first_long_name (ks : list ktok) : option ktok :=
  match ks with
  | [] => None
  | k :: r =>
      match k_tok k with
      | TCs n => if Nat.leb (length n) max_name then first_long_name r else Some k
      | _ => first_long_name r
      end
  end.

Fixpoint first_over (K : contract) (s : state) (ks : list ktok) : option ktok :=
  match ks with
  | [] => None
  | k :: r =>
      match step K s (k_tok k) (option_map k_tok (hd_error r)) with
      | Go1 s' =>
          if Nat.ltb max_groups (groups (s_frames s')) then Some k else first_over K s' r
      | Go2 s' =>
          match r with
          | [] => None
          | _ :: r' =>
              if Nat.ltb max_groups (groups (s_frames s')) then Some k else first_over K s' r'
          end
      | _ => None
      end
  end.

Definition off_or (o : option ktok) (dflt : nat) : nat :=
  match o with Some k => k_off k | None => dflt end.

Definition explain (C : bcontract) (b : list ascii) : option (nat * why_out) :=
  let L := bc_lex C in
  let K := bc_kernel C in
  if negb (Nat.leb (length b) max_file_bytes) then Some (max_file_bytes, WTooBig)
  else
    match explain_prologue L (length b) (lex L b) with
    | inl e => Some e
    | inr rest =>
        match explain_body L rest with
        | Some e => Some e
        | None =>
            match body L false rest with
            | None => Some (length b, WToken)
            | Some ks =>
                match first_not_admitted K ks with
                | Some k => Some (k_off k, WNotAdmitted)
                | None =>
                    match first_bad_script ks with
                    | Some k => Some (k_off k, WScriptArg)
                    | None =>
                      match first_bad_arg K 0 ks with
                      | Some (Some k) => Some (k_off k, WArgForm)
                      | Some None => Some (length b, WArgForm)
                      | None =>
                        if negb (Nat.leb (length ks) max_tokens)
                        then Some (off_or (nth_error ks max_tokens) (length b), WBound)
                        else
                          match first_long_name ks with
                          | Some k => Some (k_off k, WBound)
                          | None =>
                          match first_over K init ks with
                          | Some k => Some (k_off k, WBound)
                          | None =>
                              if ends_dollar (toks_of ks)
                              then Some (off_or (last (map Some ks) None) (length b), WEndsDollar)
                              else None
                          end
                          end
                      end
                    end
                end
            end
        end
    end.
