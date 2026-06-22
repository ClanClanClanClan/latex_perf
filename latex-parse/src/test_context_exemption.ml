(** Context-exemption regression gate (P3 token-aware variants).

    Asserts that each retrofitted pilot rule fires on a genuine deviation in
    ordinary prose, but stays SILENT when the same deviation is inside a
    protected region (inline/env verbatim, line comment, or math). This is the
    post-pilot-gate property that makes a Draft rule safe to promote to the
    default set: it enforces the project's typographic standard without
    false-positiving on code listings, comments, or math.

    Add a row to [cases] as each rule is made context-aware; the rule's needle
    must appear verbatim in each [plain]/[ctx] string. *)

open Test_helpers

(* (rule id, prose input that MUST fire, [(context label, input that MUST be
   silent)]). Each exempt input embeds the same deviation inside a protected
   region. *)
let cases =
  [
    ( "TYPO-002",
      "ordinary text a -- b here",
      [
        ("inline verbatim", "x \\verb|a -- b| y");
        ("verbatim env", "\\begin{verbatim}\na -- b\n\\end{verbatim}");
        ("line comment", "% a -- b comment\n");
        ("inline math", "$a -- b$");
      ] );
  ]

let () =
  (* Pilot rules are gated behind L0_VALIDATORS; enable for this suite. *)
  Unix.putenv "L0_VALIDATORS" "pilot";
  List.iter
    (fun (id, plain, exempt_cases) ->
      run (Printf.sprintf "%s fires on a prose deviation" id) (fun tag ->
          expect (fires id plain) (tag ^ ": " ^ id ^ " should fire on prose"));
      List.iter
        (fun (ctx, src) ->
          run (Printf.sprintf "%s is exempt inside %s" id ctx) (fun tag ->
              expect (does_not_fire id src)
                (tag ^ ": " ^ id ^ " must not fire inside " ^ ctx)))
        exempt_cases)
    cases;
  Unix.putenv "L0_VALIDATORS" "";
  finalise "context-exemption"
