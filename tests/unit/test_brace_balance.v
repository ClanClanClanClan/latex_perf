From Coq Require Import String List Bool Arith Lia.
From src.core.lexer Require Import LatexLexer.
Import Nat ListNotations.

Definition test_brace_balance : list latex_token -> bool :=
  fun expanded =>
    let rec check_brace_balance (tokens : list latex_token) (depth : nat) : bool :=
      match tokens with
      | [] => negb (Nat.eqb depth 0)  (* Unmatched if depth != 0 *)
      | TBeginGroup :: rest => check_brace_balance rest (S depth)
      | TEndGroup :: rest => 
          if Nat.eqb depth 0 then true  (* Extra closing brace *)
          else check_brace_balance rest (Nat.pred depth)
      | _ :: rest => check_brace_balance rest depth
      end in
    check_brace_balance expanded 0.