(** Stress tests: Str regression guard + precondition layer mapping. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[stress] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

(* Run validators with a timeout — if Str corruption causes an infinite loop the
   alarm fires and the test fails instead of hanging. *)
let run_with_timeout ?(seconds = 5) label src =
  run label (fun tag ->
      let timed_out = ref false in
      let old_handler =
        Sys.signal Sys.sigalrm
          (Sys.Signal_handle
             (fun _ ->
               timed_out := true;
               failwith "TIMEOUT"))
      in
      let _ = Unix.alarm seconds in
      (try
         let _ = Validators.run_all src in
         ()
       with Failure msg when msg = "TIMEOUT" -> timed_out := true);
      let _ = Unix.alarm 0 in
      Sys.set_signal Sys.sigalrm old_handler;
      expect (not !timed_out) (tag ^ ": timed out (possible Str corruption)"))

let () =
  (* ══════════════════════════════════════════════════════════════════════ Str
     corruption regression guard
     ══════════════════════════════════════════════════════════════════════ *)

  (* Deeply nested math + mhchem — the original CHEM-006 trigger class *)
  run_with_timeout "deeply nested ce in math"
    "$\\ce{H_2O}$ and $\\ce{NaCl}$ and $\\ce{H_2SO_4}$ more $\\ce{CaCO_3}$ end \
     $\\ce{Fe_2O_3}$";

  (* 10KB of repeated verb blocks *)
  run_with_timeout "10KB repeated verb blocks"
    (String.concat "\n"
       (List.init 200 (fun i -> "\\verb|code_block_" ^ string_of_int i ^ "|")));

  (* 1000 inline math segments *)
  run_with_timeout "1000 inline math segments"
    (String.concat " "
       (List.init 1000 (fun i -> "$x_{" ^ string_of_int i ^ "}$")));

  (* Combined adversarial: every L1-triggering pattern *)
  run_with_timeout "combined adversarial patterns"
    "\\begin{minted}{python}\n\
     code\n\
     \\end{minted}\n\
     \\verb|test| $\\frac{1}{2}$ \\ce{H_2O}\n\
     \\begin{align}\n\
     x &= y\n\
     \\end{align}\n\
     \\label{eq:1} \\ref{fig:1} \\cite{key}\n\
     \\newcommand{\\foo}{bar} \\emph{text} \\textbf{bold}\n\
     $\\left( \\right) \\bigl( \\bigr)$\n\
     \\begin{lstlisting}[language=Python]\n\
     code\n\
     \\end{lstlisting}";

  (* Edge: empty string *)
  run_with_timeout "empty string" "";

  (* Edge: single dollar sign *)
  run_with_timeout "single dollar" "$";

  (* Edge: unmatched brace *)
  run_with_timeout "unmatched brace" "{{{";

  (* Edge: very long single line (50KB, no newlines) *)
  run_with_timeout "50KB single line" ~seconds:10 (String.make 50000 'a');

  (* ══════════════════════════════════════════════════════════════════════
     precondition_of_rule_id layer mapping
     ══════════════════════════════════════════════════════════════════════ *)

  (* L0 rules *)
  run "TYPO-001 -> L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "TYPO-001" = Validators.L0)
        (tag ^ ": TYPO prefix => L0"));
  run "ENC-001 -> L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "ENC-001" = Validators.L0)
        (tag ^ ": ENC prefix => L0"));
  run "CHAR-005 -> L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CHAR-005" = Validators.L0)
        (tag ^ ": CHAR prefix => L0"));
  run "SPC-003 -> L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "SPC-003" = Validators.L0)
        (tag ^ ": SPC prefix => L0"));
  run "VERB-001 -> L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "VERB-001" = Validators.L0)
        (tag ^ ": VERB prefix => L0"));

  (* L1 rules *)
  run "CMD-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CMD-001" = Validators.L1)
        (tag ^ ": CMD prefix => L1"));
  run "MOD-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MOD-001" = Validators.L1)
        (tag ^ ": MOD prefix => L1"));
  run "EXP-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "EXP-001" = Validators.L1)
        (tag ^ ": EXP prefix => L1"));
  run "DELIM-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "DELIM-001" = Validators.L1)
        (tag ^ ": DELIM prefix => L1"));
  run "SCRIPT-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "SCRIPT-001" = Validators.L1)
        (tag ^ ": SCRIPT prefix => L1"));
  run "MATH-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-001" = Validators.L1)
        (tag ^ ": MATH prefix => L1"));
  run "REF-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "REF-001" = Validators.L1)
        (tag ^ ": REF prefix => L1"));
  run "CHEM-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CHEM-001" = Validators.L1)
        (tag ^ ": CHEM prefix => L1"));
  run "FONT-001 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "FONT-001" = Validators.L1)
        (tag ^ ": FONT prefix => L1"));
  run "RTL-003 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "RTL-003" = Validators.L1)
        (tag ^ ": RTL prefix => L1"));
  run "CJK-008 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CJK-008" = Validators.L1)
        (tag ^ ": CJK prefix => L1"));
  run "PT-002 -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "PT-002" = Validators.L1)
        (tag ^ ": PT prefix => L1"));

  (* Special cases: specific IDs override generic prefix *)
  run "TYPO-059 -> L1 (special case)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "TYPO-059" = Validators.L1)
        (tag ^ ": TYPO-059 is L1, not L0"));
  run "MATH-083 -> L0 (special case)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-083" = Validators.L0)
        (tag ^ ": MATH-083 is L0, not L1"));

  (* Unknown prefixes default to L0 *)
  run "ZZZZ-001 -> L0 (unknown)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "ZZZZ-001" = Validators.L0)
        (tag ^ ": unknown prefix defaults to L0"));
  run "TAB-001 -> L0 (unknown)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "TAB-001" = Validators.L0)
        (tag ^ ": TAB prefix defaults to L0"));
  run "FIG-001 -> L0 (unknown)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "FIG-001" = Validators.L0)
        (tag ^ ": FIG prefix defaults to L0"));

  (* Empty / short ID *)
  run "empty ID -> L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "" = Validators.L0)
        (tag ^ ": empty ID defaults to L0"));
  run "X -> L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "X" = Validators.L0)
        (tag ^ ": single char defaults to L0"));

  if !fails > 0 then (
    Printf.eprintf "[stress] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[stress] PASS %d cases\n%!" !cases
