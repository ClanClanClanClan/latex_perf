From Coq Require Import String List Bool Arith Decidable Program Lia.
Require Import LatexLexer.
Import Nat ListNotations.
Open Scope string_scope.
Definition string_dec := String.string_dec.

(** * LaTeX Perfectionist v24 - Expander Data Types
    
    Complete data type definitions for the L1 Verified Macro Expander.
    Follows LAYER_L1_SPECIFICATION.md exactly.
    
    Status: 0 axioms, 0 admits required
*)

(** * Macro definition storage *)
Record macro_definition := {
  macro_name : string;
  macro_body : list latex_token;
  is_builtin : bool
}.

(* ================================================================= *)
(* ==  Resource certificates – comprehensive resource tracking      ==*)
(* ================================================================= *)

(** * Resource-triple certificate system
    
    This system tracks all three resources that expand_with_fuel consumes:
    1. Fuel (expansion steps)
    2. Call stack depth (macro_calls) 
    3. Token growth (additional tokens)
    
    By predicting exact resource consumption, we can provide success guarantees.
**)

Record res_cert := {
  rc_fuel   : nat;      (* strictly positive fuel needed *)
  rc_calls  : nat;      (* upper-bound on additional macro_calls *)
  rc_tokens : nat       (* upper-bound on additional token_growth *)
}.

(** Smart constructor ensuring fuel ≥ 1 **)
Definition mk_cert (fuel calls toks : nat) : res_cert :=
  {| rc_fuel   := max 1 fuel      (* never 0 *)
   ; rc_calls  := calls
   ; rc_tokens := toks |}.

(** Resource addition **)
Definition cert_plus (c1 c2 : res_cert) : res_cert :=
  mk_cert (rc_fuel  c1 + rc_fuel  c2)
          (rc_calls c1 + rc_calls c2)
          (rc_tokens c1 + rc_tokens c2).

(** Resource certificate computation - mirrors expand_with_fuel structure **)
Fixpoint cert_of
        (depth : nat)
        (defs  : string -> option macro_definition)
        (seen  : list string)
        (ts    : list latex_token) : res_cert :=
  match depth with
  | 0 => mk_cert 1 0 0                           (* safety fallback *)
  | S depth' =>
      match ts with
      | nil              => mk_cert 1 0 0
      | TEOF :: _        => mk_cert 1 0 0
      | TCommand c :: r  =>
          match defs c with
          | None      => cert_plus (mk_cert 1 1 0) (cert_of depth' defs seen r)
          | Some md   =>
              if in_dec string_dec c seen
              then mk_cert 1 0 0                    (* cycle -> hard stop *)
              else
                let body := macro_body md in
                cert_plus (mk_cert 1 1 (length body))
                          (cert_plus
                              (cert_of depth' defs (c::seen) body)
                              (cert_of depth' defs seen r))
          end
      | _ :: r           => cert_of depth' defs seen r
      end
  end.

(** Legacy compatibility - deprecated **)
Definition fuel_cert_of (depth : nat) (defs : string -> option macro_definition) 
                       (seen : list string) (ts : list latex_token) : nat :=
  rc_fuel (cert_of depth defs seen ts).

Definition certificate (defs : string -> option macro_definition) (ts : list latex_token) : nat :=
  rc_fuel (cert_of (10 * 100) defs nil ts).

(** * Expansion state *)
Record exp_state := {
  macro_definitions : list macro_definition;
  expansion_depth   : nat;
  call_stack       : list string;
  max_expansions   : nat;
  token_growth     : nat;
  macro_calls      : nat
}.

(** * Expansion results *)
Inductive expand_error :=
  | MacroNotFound : string -> expand_error
  | RecursionLimit : string -> expand_error
  | MalformedMacro : string -> expand_error
  | TokenGrowthLimit : expand_error  
  | MacroCallLimit : expand_error.

Inductive expand_result := 
  | ExpandSuccess : list latex_token -> expand_result
  | ExpandError   : expand_error -> expand_result.

(** * Helper Functions *)

(** Initial state *)
Definition init_exp_state : exp_state := {|
  macro_definitions := nil;
  expansion_depth   := 0;
  call_stack       := nil;
  max_expansions   := 32;
  token_growth     := 0;
  macro_calls      := 0
|}.

(** State update functions *)
Definition increment_depth (st : exp_state) : exp_state :=
  {| macro_definitions := st.(macro_definitions);
     expansion_depth   := S st.(expansion_depth);
     call_stack       := st.(call_stack);
     max_expansions   := st.(max_expansions);
     token_growth     := st.(token_growth);
     macro_calls      := st.(macro_calls) |}.

Definition push_call (st : exp_state) (cmd : string) : exp_state :=
  {| macro_definitions := st.(macro_definitions);
     expansion_depth   := st.(expansion_depth);
     call_stack       := cmd :: st.(call_stack);
     max_expansions   := st.(max_expansions);
     token_growth     := st.(token_growth);
     macro_calls      := st.(macro_calls) |}.

Definition increment_calls (st : exp_state) : exp_state :=
  {| macro_definitions := st.(macro_definitions);
     expansion_depth   := st.(expansion_depth);
     call_stack       := st.(call_stack);
     max_expansions   := st.(max_expansions);
     token_growth     := st.(token_growth);
     macro_calls      := S st.(macro_calls) |}.

(** Limit checking *)
Definition exceeds_depth_limit (st : exp_state) : bool :=
  leb st.(max_expansions) st.(expansion_depth).

Definition exceeds_token_limit (st : exp_state) (new_tokens : nat) : bool :=
  ltb (8 * 1024) (st.(token_growth) + new_tokens).

Definition exceeds_call_limit (st : exp_state) : bool :=
  leb (8 * 64) st.(macro_calls).

(* ================================== *)
(* ===  Auxiliary facts             ==*)
(* ================================== *)

Lemma token_discriminate :
  forall s, TText s <> TEOF.
Proof. intros s H; inversion H. Qed.