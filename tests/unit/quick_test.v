From Coq Require Import String List.
Require Import ValidationTypes.

(* Ultra-fast compilation test *)
Example quick_test_1 : 1 + 1 = 2.
Proof. reflexivity. Qed.

Example quick_test_2 : length (cons 1 (cons 2 (cons 3 nil))) = 3%nat.
Proof. reflexivity. Qed.

(* Test that ValidationTypes compiles *)
Example validation_test : Error = Error.
Proof. reflexivity. Qed.

(* Simple rule test *)
Definition simple_rule : validation_rule :=
  {|
    id := "QUICK-001";
    description := "Quick test rule";
    precondition := L0_Lexer;
    default_severity := Warning;
    rule_maturity := Draft;
    owner := "test";
    performance_bucket := TokenKind_Text;
    auto_fix := None;
    implementation_file := "quick_test.v";
    validator := (fun _ => nil);
    rule_sound := None
  |}.

Example rule_test : simple_rule.(id) = "QUICK-001".
Proof. reflexivity. Qed.