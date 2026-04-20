(** PR #241 (memo §11): verify Class D (STYLE family) rules do not run on the
    keystroke-critical hot path. They must be reachable only through
    [run_with_policy] with policies that enable Class D. *)

open Latex_parse_lib
open Test_helpers

let style_rule_ids =
  List.map (fun (r : Validators.rule) -> r.id) Validators.rules_class_d

let is_style_id id = String.length id >= 6 && String.sub id 0 6 = "STYLE-"

(* A source that should trigger multiple STYLE validators. Using long sentences
   plus multiple short paragraphs — the classic STYLE-017 / STYLE-042 triggers
   from PR #236 fixture behaviour. *)
let styleful_src =
  "\\documentclass{article}\n\
   \\begin{document}\n\
   This is a very long sentence that keeps going and going and going and going \
   and going and going and going and going and going until it becomes utterly \
   unreasonable.\n\n\
   One.\n\n\
   Two.\n\n\
   Three.\n\
   \\end{document}\n"

let () =
  (* 1. rules_class_d is non-empty and contains only STYLE-* rules. *)
  run "rules_class_d is non-empty and STYLE-only" (fun tag ->
      let n = List.length style_rule_ids in
      expect (n > 0) (tag ^ ": got " ^ string_of_int n ^ " Class D rules");
      let non_style =
        List.filter (fun id -> not (is_style_id id)) style_rule_ids
      in
      expect (non_style = [])
        (tag
        ^ ": "
        ^ string_of_int (List.length non_style)
        ^ " non-STYLE rule(s) in rules_class_d: "
        ^ String.concat "," non_style));

  (* 2. run_all produces zero STYLE-* results. *)
  run "run_all excludes STYLE rules" (fun tag ->
      let results = Validators.run_all styleful_src in
      let style_results =
        List.filter (fun (r : Validators.result) -> is_style_id r.id) results
      in
      expect (style_results = [])
        (tag
        ^ ": "
        ^ string_of_int (List.length style_results)
        ^ " STYLE result(s) leaked into run_all: "
        ^ String.concat ","
            (List.map (fun (r : Validators.result) -> r.id) style_results)));

  (* 3. run_class_d alone produces STYLE-* results. *)
  run "run_class_d produces STYLE results" (fun tag ->
      let results = Validators.run_class_d styleful_src in
      let style_results =
        List.filter (fun (r : Validators.result) -> is_style_id r.id) results
      in
      expect
        (List.length style_results > 0)
        (tag
        ^ ": run_class_d returned "
        ^ string_of_int (List.length style_results)
        ^ " STYLE result(s); expected > 0"));

  (* 4. run_with_policy with default (A+B) excludes STYLE. *)
  run "run_with_policy default excludes STYLE" (fun tag ->
      let results =
        Validators.run_with_policy Execution_policy.default styleful_src
      in
      let style_results =
        List.filter (fun (r : Validators.result) -> is_style_id r.id) results
      in
      expect (style_results = [])
        (tag
        ^ ": "
        ^ string_of_int (List.length style_results)
        ^ " STYLE result(s) in default policy run"));

  (* 5. run_with_policy with_advisory includes STYLE. *)
  run "run_with_policy with_advisory includes STYLE" (fun tag ->
      let results =
        Validators.run_with_policy Execution_policy.with_advisory styleful_src
      in
      let style_results =
        List.filter (fun (r : Validators.result) -> is_style_id r.id) results
      in
      expect
        (List.length style_results > 0)
        (tag
        ^ ": with_advisory returned "
        ^ string_of_int (List.length style_results)
        ^ " STYLE result(s); expected > 0"));

  (* 6. Execution_policy.allows agrees with runtime. *)
  run "Execution_policy.allows matches routing" (fun tag ->
      expect
        (not
           (Execution_policy.allows Execution_policy.default Execution_class.D))
        (tag ^ ": default should NOT allow D");
      expect
        (Execution_policy.allows Execution_policy.with_advisory
           Execution_class.D)
        (tag ^ ": with_advisory should allow D");
      expect
        (Execution_policy.allows Execution_policy.full Execution_class.D)
        (tag ^ ": full should allow D"));

  finalise "class_d_isolation"
