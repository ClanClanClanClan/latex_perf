(* Simplified Phase 1 DFA Implementation *)
(* Working OCaml implementation while extracted code is being fixed *)

type validation_result = (int * int * string) list

(* Simple backslash detection *)
let validate_backslashes content =
  let issues = ref [] in
  let pos = ref 0 in
  String.iter (fun c ->
    incr pos;
    if c = '\\' then
      (* Found backslash - check next character *)
      if !pos < String.length content then
        let next_char = content.[!pos] in
        if next_char = ' ' then
          issues := (1, !pos, "Backslash followed by space") :: !issues
  ) content;
  List.rev !issues

(* Placeholder for future DFA compilation *)
let compile_phase1 rules = 
  (* Return simple validator function *)
  validate_backslashes

(* Main validation entry point *)
let validate_phase1 validator document =
  validator document