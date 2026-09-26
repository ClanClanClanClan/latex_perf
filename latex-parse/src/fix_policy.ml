(* Fix policy — see fix_policy.mli for the why.

   The allow-list comes from the meaning audit recorded as OPEN-112. Every
   candidate rule's fix was applied ALONE to real compiling papers, the typeset
   text was diffed against the pristine build, every changed word was
   classified, and every SAFE verdict was then attacked by an independent
   refuter. Of 54 candidates only MATH-106 survived. scripts/tools/
   check_fix_allowlist.py refuses any entry without that evidence.

   TYPO-018 and SPC-031 were listed here provisionally and then REMOVED. They
   change nothing in running text, which is why the first sample showed zero PDF
   differences, but they collapse spaces inside author-defined verbatim and
   listing environments that the exempt layer does not recognise (OPEN-113).
   That was measured on a real paper, 2506.16341v1, whose \lstnewenvironment
   listing came back flattened. Zero differences on a sample only says the
   sample did not contain the hazard. *)
let default_allowlist = [ "MATH-106" ]
let in_default_set id = List.mem id default_allowlist

(* The 24 rules measured in a break repair set by OPEN-109 and OPEN-110. They
   are listed in sorted order so a diff shows exactly what moved. *)
let implicated =
  [
    "CHEM-005";
    "CHEM-009";
    "CJK-001";
    "MATH-009";
    "MATH-014";
    "MATH-029";
    "MATH-043";
    "MATH-044";
    "MATH-078";
    "MATH-097";
    "SCRIPT-006";
    "SCRIPT-016";
    "SCRIPT-019";
    "STRUCT-001";
    "STYLE-024";
    "TYPO-001";
    "TYPO-002";
    "TYPO-005";
    "TYPO-010";
    "TYPO-012";
    "TYPO-013";
    "TYPO-022";
    "TYPO-037";
    "TYPO-062";
  ]
