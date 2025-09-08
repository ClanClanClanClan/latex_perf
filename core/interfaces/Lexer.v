(* Core Lexer interface for Coq proofs *)

Require Import String List Ascii.

(* Basic token types *)
Inductive catcode : Type :=
  | Escape | BeginGrp | EndGrp | Math | AlignTab | Newline
  | Param | Superscr | Subscr | Ignored | Space | Letter
  | Other | Active | Comment | Invalid.

Inductive token : Type :=
  | TChar : ascii -> catcode -> token
  | TMacro : string -> token
  | TParam : nat -> token
  | TGroupOpen : token
  | TGroupClose : token
  | TEOF : token.

(* Located token with position *)
Record location : Type := {
  line : nat;
  column : nat;
  offset : nat
}.

Record located_token : Type := {
  tok : token;
  loc : location
}.

Definition token_list := list located_token.