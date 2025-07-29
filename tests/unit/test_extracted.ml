(* Test program for extracted validators *)

(* OCaml type definitions for extracted code *)
type latex_token = 
  | TCommand of string
  | TBeginGroup
  | TEndGroup
  | TMathShift
  | TAlignment
  | TParameter
  | TSuperscript
  | TSubscript
  | TText of string
  | TSpace
  | TComment of string
  | TNewline
  | TEOF

type severity = Error | Warning | Info

type layer = L0_Lexer | L1_Expanded | L2_Ast | L3_Semantics | L4_Style

type validation_issue = {
  rule_id : string;
  issue_severity : severity;
  message : string;
  loc : (int * int) option;
  suggested_fix : string option;
  rule_owner : string;
}

type document_state = {
  tokens : latex_token list;
  expanded_tokens : latex_token list option;
  ast : string option;
  semantics : string option;
  filename : string;
  doc_layer : layer;
}

(* Include the extracted code *)
#use "extracted_validators.ml";;
#use "validator_runner.ml";;

(* Test function *)
let test_validators () =
  (* Create a test document with some LaTeX tokens *)
  let test_doc = {
    tokens = [
      TCommand "left";
      TText "(";
      TText "x";
      TCommand "right";
      TText ")";
      TCommand "left";  (* Unmatched left *)
      TText "[";
    ];
    expanded_tokens = Some [
      TCommand "left";
      TText "(";
      TText "x";
      TCommand "right";
      TText ")";
      TCommand "left";  (* Unmatched left *)
      TText "[";
    ];
    ast = None;
    semantics = None;
    filename = "test.tex";
    doc_layer = L1_Expanded;
  } in
  
  (* Run validators *)
  let issues = run_all_validators test_doc in
  
  (* Print results *)
  Printf.printf "Found %d validation issues:\n" (List.length issues);
  List.iter (fun issue ->
    Printf.printf "- [%s] %s: %s\n" 
      issue.rule_id 
      (match issue.issue_severity with Error -> "ERROR" | Warning -> "WARN" | Info -> "INFO")
      issue.message
  ) issues;
  
  Printf.printf "\nValidators working correctly!\n"

let () = test_validators ()