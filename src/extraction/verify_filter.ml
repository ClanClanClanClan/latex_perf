(**
 * Verify the filter is working
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

(* Filter out the slow rule *)
let get_optimized_rules () =
  List.filter (fun rule ->
    let id = chars_to_string rule.id in
    id <> "200-RAHC"
  ) all_l0_rules

(* Main *)
let () =
  let all_rules = all_l0_rules in
  let optimized_rules = get_optimized_rules () in
  
  Printf.printf "Total rules: %d\n" (List.length all_rules);
  Printf.printf "Optimized rules: %d\n" (List.length optimized_rules);
  Printf.printf "Rules removed: %d\n\n" 
    (List.length all_rules - List.length optimized_rules);
  
  (* Check if 200-RAHC is in optimized rules *)
  let has_slow_rule = List.exists (fun rule ->
    chars_to_string rule.id = "200-RAHC"
  ) optimized_rules in
  
  Printf.printf "200-RAHC in optimized rules: %b\n" has_slow_rule;
  
  (* List all CHAR rules *)
  Printf.printf "\nCHAR rules in optimized set:\n";
  List.iter (fun rule ->
    let id = chars_to_string rule.id in
    if String.contains id 'R' && String.contains id 'A' && 
       String.contains id 'H' && String.contains id 'C' then
      Printf.printf "  %s\n" id
  ) optimized_rules