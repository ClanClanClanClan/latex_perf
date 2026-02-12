(** Unit tests for REF validator rules (L1 cross-referencing / label hygiene).
    REF-001 through REF-009, excluding REF-008 (L3_Semantics). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  incr cases;
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  let tag = Printf.sprintf "case %d: %s" (!cases + 1) msg in
  f tag

let find_result id results =
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let fires id src =
  let results = Validators.run_all src in
  match find_result id results with Some _ -> true | None -> false

let does_not_fire id src =
  let results = Validators.run_all src in
  match find_result id results with Some _ -> false | None -> true

let fires_with_count id src expected_count =
  let results = Validators.run_all src in
  match find_result id results with
  | Some r -> r.count = expected_count
  | None -> false

let () =
  (* ══════════════════════════════════════════════════════════════════════
     REF-001: Undefined \ref/\eqref label after expansion
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-001 fires on undefined ref" (fun tag ->
      expect
        (fires "REF-001" "See \\ref{eq:missing} for details.")
        (tag ^ ": undefined ref"));
  run "REF-001 fires on undefined eqref" (fun tag ->
      expect
        (fires "REF-001" "See \\eqref{eq:missing} for details.")
        (tag ^ ": undefined eqref"));
  run "REF-001 fires count=2" (fun tag ->
      expect
        (fires_with_count "REF-001" "See \\ref{eq:a} and \\ref{eq:b}." 2)
        (tag ^ ": count=2"));
  run "REF-001 clean: ref has matching label" (fun tag ->
      expect
        (does_not_fire "REF-001" "\\label{eq:main} See \\ref{eq:main}.")
        (tag ^ ": matching label"));
  run "REF-001 clean: eqref has matching label" (fun tag ->
      expect
        (does_not_fire "REF-001" "\\label{eq:main} See \\eqref{eq:main}.")
        (tag ^ ": matching eqref"));
  run "REF-001 clean: no refs at all" (fun tag ->
      expect (does_not_fire "REF-001" "No references here.") (tag ^ ": no refs"));
  run "REF-001 partial: one matching, one undefined" (fun tag ->
      expect
        (fires_with_count "REF-001"
           "\\label{eq:ok} See \\ref{eq:ok} and \\ref{eq:bad}." 1)
        (tag ^ ": one undefined"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-002: Duplicate label name
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-002 fires on duplicate labels" (fun tag ->
      expect
        (fires "REF-002" "\\label{eq:main} some text \\label{eq:main}")
        (tag ^ ": duplicate"));
  run "REF-002 fires count=1 (two copies = one dup)" (fun tag ->
      expect
        (fires_with_count "REF-002" "\\label{eq:main} x \\label{eq:main}" 1)
        (tag ^ ": count=1"));
  run "REF-002 fires count=2 (three copies)" (fun tag ->
      expect
        (fires_with_count "REF-002" "\\label{eq:x} \\label{eq:x} \\label{eq:x}"
           2)
        (tag ^ ": count=2 for three copies"));
  run "REF-002 clean: distinct labels" (fun tag ->
      expect
        (does_not_fire "REF-002" "\\label{eq:a} \\label{eq:b} \\label{eq:c}")
        (tag ^ ": distinct labels"));
  run "REF-002 clean: no labels" (fun tag ->
      expect (does_not_fire "REF-002" "No labels here.") (tag ^ ": no labels"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-003: Label contains spaces
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-003 fires on label with space" (fun tag ->
      expect (fires "REF-003" "\\label{eq main}") (tag ^ ": space in label"));
  run "REF-003 fires count=2" (fun tag ->
      expect
        (fires_with_count "REF-003" "\\label{eq main} \\label{fig diagram}" 2)
        (tag ^ ": count=2"));
  run "REF-003 clean: no spaces" (fun tag ->
      expect (does_not_fire "REF-003" "\\label{eq:main}") (tag ^ ": no space"));
  run "REF-003 clean: no labels" (fun tag ->
      expect (does_not_fire "REF-003" "Just text.") (tag ^ ": no labels"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-004: Label contains uppercase letters
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-004 fires on uppercase label" (fun tag ->
      expect (fires "REF-004" "\\label{eq:Main}") (tag ^ ": uppercase"));
  run "REF-004 fires on ALL CAPS" (fun tag ->
      expect (fires "REF-004" "\\label{FIG:DIAGRAM}") (tag ^ ": all caps"));
  run "REF-004 fires count=2" (fun tag ->
      expect
        (fires_with_count "REF-004" "\\label{eq:Main} \\label{sec:Intro}" 2)
        (tag ^ ": count=2"));
  run "REF-004 clean: all lowercase" (fun tag ->
      expect (does_not_fire "REF-004" "\\label{eq:main}") (tag ^ ": lowercase"));
  run "REF-004 clean: digits and colons" (fun tag ->
      expect
        (does_not_fire "REF-004" "\\label{eq:123-test}")
        (tag ^ ": no uppercase"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-005: Label not prefixed fig:/tab:/eq:/sec: etc.
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-005 fires on unprefixed label" (fun tag ->
      expect (fires "REF-005" "\\label{main}") (tag ^ ": no prefix"));
  run "REF-005 fires on numeric label" (fun tag ->
      expect (fires "REF-005" "\\label{1234}") (tag ^ ": numeric"));
  run "REF-005 clean: fig: prefix" (fun tag ->
      expect (does_not_fire "REF-005" "\\label{fig:diagram}") (tag ^ ": fig:"));
  run "REF-005 clean: tab: prefix" (fun tag ->
      expect (does_not_fire "REF-005" "\\label{tab:results}") (tag ^ ": tab:"));
  run "REF-005 clean: eq: prefix" (fun tag ->
      expect (does_not_fire "REF-005" "\\label{eq:main}") (tag ^ ": eq:"));
  run "REF-005 clean: sec: prefix" (fun tag ->
      expect (does_not_fire "REF-005" "\\label{sec:intro}") (tag ^ ": sec:"));
  run "REF-005 clean: thm: prefix" (fun tag ->
      expect (does_not_fire "REF-005" "\\label{thm:main}") (tag ^ ": thm:"));
  run "REF-005 clean: alg: prefix" (fun tag ->
      expect (does_not_fire "REF-005" "\\label{alg:sort}") (tag ^ ": alg:"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-006: Page reference uses \ref not \pageref
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-006 fires on page \\ref" (fun tag ->
      expect (fires "REF-006" "page \\ref{eq:main}") (tag ^ ": page ref"));
  run "REF-006 fires on Page \\ref" (fun tag ->
      expect (fires "REF-006" "Page \\ref{sec:intro}") (tag ^ ": Page ref"));
  run "REF-006 fires with tilde" (fun tag ->
      expect (fires "REF-006" "page~\\ref{eq:main}") (tag ^ ": tilde"));
  run "REF-006 clean: \\pageref" (fun tag ->
      expect
        (does_not_fire "REF-006" "page \\pageref{eq:main}")
        (tag ^ ": pageref"));
  run "REF-006 clean: regular \\ref" (fun tag ->
      expect (does_not_fire "REF-006" "See \\ref{eq:main}.") (tag ^ ": not page"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-007: Cite key contains whitespace
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-007 fires on cite with space" (fun tag ->
      expect (fires "REF-007" "\\cite{jones 2020}") (tag ^ ": space in cite"));
  run "REF-007 fires on cite with tab" (fun tag ->
      expect (fires "REF-007" "\\cite{jones\t2020}") (tag ^ ": tab in cite"));
  run "REF-007 clean: no whitespace" (fun tag ->
      expect (does_not_fire "REF-007" "\\cite{jones2020}") (tag ^ ": clean cite"));
  run "REF-007 clean: no cite" (fun tag ->
      expect (does_not_fire "REF-007" "No citations here.") (tag ^ ": no cite"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-009: Reference appears before label definition (forward ref)
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-009 fires on forward ref" (fun tag ->
      expect
        (fires "REF-009" "See \\ref{eq:main}. \\label{eq:main}")
        (tag ^ ": forward ref"));
  run "REF-009 fires on forward eqref" (fun tag ->
      expect
        (fires "REF-009" "See \\eqref{eq:main}. \\label{eq:main}")
        (tag ^ ": forward eqref"));
  run "REF-009 clean: label before ref" (fun tag ->
      expect
        (does_not_fire "REF-009" "\\label{eq:main} See \\ref{eq:main}.")
        (tag ^ ": backward ref ok"));
  run "REF-009 clean: no refs" (fun tag ->
      expect (does_not_fire "REF-009" "No references.") (tag ^ ": no refs"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "empty input: no REF rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let ref_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 4 && String.sub r.id 0 4 = "REF-")
          results
      in
      expect (ref_fires = []) (tag ^ ": no REF on empty input"));

  run "no label/ref content: no REF fires" (fun tag ->
      let results = Validators.run_all "Plain text with $x + y = 0$." in
      let ref_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 4 && String.sub r.id 0 4 = "REF-")
          results
      in
      expect (ref_fires = []) (tag ^ ": no REF on plain text"));

  (* Registration: verify each REF rule fires on known-bad input *)
  run "registration: REF-001 registered" (fun tag ->
      expect (fires "REF-001" "See \\ref{eq:missing}.") (tag ^ ": registered"));
  run "registration: REF-002 registered" (fun tag ->
      expect
        (fires "REF-002" "\\label{eq:x} \\label{eq:x}")
        (tag ^ ": registered"));
  run "registration: REF-003 registered" (fun tag ->
      expect (fires "REF-003" "\\label{eq main}") (tag ^ ": registered"));
  run "registration: REF-004 registered" (fun tag ->
      expect (fires "REF-004" "\\label{eq:Main}") (tag ^ ": registered"));
  run "registration: REF-005 registered" (fun tag ->
      expect (fires "REF-005" "\\label{main}") (tag ^ ": registered"));
  run "registration: REF-006 registered" (fun tag ->
      expect (fires "REF-006" "page \\ref{eq:x}") (tag ^ ": registered"));
  run "registration: REF-007 registered" (fun tag ->
      expect (fires "REF-007" "\\cite{a b}") (tag ^ ": registered"));
  run "registration: REF-009 registered" (fun tag ->
      expect (fires "REF-009" "\\ref{eq:x} \\label{eq:x}") (tag ^ ": registered"));

  (* Precondition check *)
  run "precondition: REF- maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "REF-001" = L1)
        (tag ^ ": L1 layer"));

  (* Severity checks *)
  run "severity: REF-001 is Error" (fun tag ->
      let results = Validators.run_all "\\ref{missing}" in
      match find_result "REF-001" results with
      | Some r -> expect (r.severity = Error) (tag ^ ": Error severity")
      | None -> expect false (tag ^ ": should fire"));
  run "severity: REF-003 is Warning" (fun tag ->
      let results = Validators.run_all "\\label{eq main}" in
      match find_result "REF-003" results with
      | Some r -> expect (r.severity = Warning) (tag ^ ": Warning severity")
      | None -> expect false (tag ^ ": should fire"));
  run "severity: REF-004 is Info" (fun tag ->
      let results = Validators.run_all "\\label{eq:Main}" in
      match find_result "REF-004" results with
      | Some r -> expect (r.severity = Info) (tag ^ ": Info severity")
      | None -> expect false (tag ^ ": should fire"));

  (* Combined multi-rule test *)
  run "combined: multiple REF rules fire" (fun tag ->
      let src =
        "\\label{eq Main} \\label{eq Main} See page \\ref{eq:missing}."
      in
      expect (fires "REF-001" src) (tag ^ ": REF-001 fires");
      expect (fires "REF-002" src) (tag ^ ": REF-002 fires");
      expect (fires "REF-003" src) (tag ^ ": REF-003 fires");
      expect (fires "REF-004" src) (tag ^ ": REF-004 fires");
      expect (fires "REF-005" src) (tag ^ ": REF-005 fires");
      expect (fires "REF-006" src) (tag ^ ": REF-006 fires"));

  (* Real-document test: proper LaTeX with labels and refs *)
  run "real document: clean labels and refs" (fun tag ->
      let src =
        "\\section{Introduction}\\label{sec:intro}\n\
         As shown in Figure~\\ref{fig:diagram}, the result follows.\n\
         \\begin{figure}\\label{fig:diagram}\n\
         \\end{figure}\n\
         See Equation~\\eqref{eq:main}.\n\
         \\label{eq:main} $E = mc^2$"
      in
      expect (does_not_fire "REF-001" src) (tag ^ ": no undefined refs");
      expect (does_not_fire "REF-002" src) (tag ^ ": no duplicate labels");
      expect (does_not_fire "REF-003" src) (tag ^ ": no spaces in labels"));

  (* Summary *)
  Printf.printf "[ref] %s %d cases\n"
    (if !fails = 0 then "PASS" else "FAIL")
    !cases;
  if !fails > 0 then (
    Printf.eprintf "[ref] %d / %d failures\n" !fails !cases;
    exit 1)
