(**
 * List all rules with their details
 *)

open Enterprise_validators

(* String conversion *)
let chars_to_string chars =
  match chars with
  | [] -> ""
  | _ ->
    let len = List.length chars in
    let buf = Buffer.create len in
    List.iter (Buffer.add_char buf) (List.rev chars);
    Buffer.contents buf

(* Print rule details *)
let print_rule_details rule =
  Printf.printf "ID: %s | Bucket: %s | Category: %s | Severity: %s\n"
    (chars_to_string rule.id)
    (match rule.performance_bucket with
     | TokenKind_Text -> "TEXT"
     | TokenKind_Command -> "COMMAND"
     | TokenKind_MathShift -> "MATH"
     | TokenKind_BeginGroup -> "BEGIN"
     | TokenKind_EndGroup -> "END"
     | TokenKind_Other -> "OTHER")
    (match rule.category with
     | Typo -> "TYPO"
     | Style -> "STYLE"
     | Math -> "MATH"
     | Env -> "ENV"
     | Struct -> "STRUCT"
     | Ref -> "REF"
     | Char -> "CHAR")
    (match rule.severity with
     | Info -> "INFO"
     | Warning -> "WARNING"
     | Error -> "ERROR")

(* Main *)
let () =
  Printf.printf "Total L0 rules: %d\n\n" (List.length all_l0_rules);
  
  (* Sort by ID *)
  let sorted_rules = List.sort (fun r1 r2 ->
    compare (chars_to_string r1.id) (chars_to_string r2.id)
  ) all_l0_rules in
  
  List.iter print_rule_details sorted_rules;
  
  (* Find the problematic rule *)
  Printf.printf "\n\nSearching for rule with ID containing '200-RAHC' or similar...\n";
  List.iter (fun rule ->
    let id = chars_to_string rule.id in
    if String.contains id '2' && rule.category = Char then
      Printf.printf "Found CHAR rule with '2': %s (bucket %s)\n" id 
        (match rule.performance_bucket with 
         | TokenKind_Text -> "TEXT"
         | TokenKind_Command -> "COMMAND"
         | TokenKind_MathShift -> "MATH"
         | TokenKind_BeginGroup -> "BEGIN"
         | TokenKind_EndGroup -> "END"
         | TokenKind_Other -> "OTHER")
  ) all_l0_rules