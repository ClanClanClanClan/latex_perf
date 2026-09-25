(* Fix policy — see fix_policy.mli for the why.

   The allow-list below is PROVISIONAL. It is filled from the meaning audit
   recorded as OPEN-112, and membership is a CLAIM that a gate checks. TYPO-018
   collapses a run of spaces in running text, and SPC-031 collapses the run of
   spaces after a period. Both were measured over thousands of real edits with
   zero change to the words or the layout of the compiled PDF, because TeX
   already treats a run of spaces as one. Do NOT add other ids here without the
   OPEN-112 measurement. *)
let default_allowlist = [ "TYPO-018"; "SPC-031" ]
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
