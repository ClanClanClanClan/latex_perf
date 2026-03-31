(** Unit tests for L4 STYLE text-scannable rules: 25 rules.
    STYLE-004..049 (Phase 1 batch).
    ~125 total test cases. *)

open Test_helpers

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-004: Paragraph exceeds 300 words
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-004 fires: long paragraph" (fun tag ->
      let long_para = String.concat " " (List.init 310 (fun _ -> "word")) in
      expect (fires "STYLE-004" long_para) (tag ^ ": 310 words"));
  run "STYLE-004 clean: short paragraph" (fun tag ->
      expect
        (does_not_fire "STYLE-004" "This is a short paragraph with few words.")
        (tag ^ ": short para"));
  run "STYLE-004 clean: two short paras" (fun tag ->
      let two = "Short paragraph.\n\nAnother short one." in
      expect (does_not_fire "STYLE-004" two) (tag ^ ": two short paras"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-006: Consecutive sentences start with same word
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-006 fires: same start" (fun tag ->
      expect
        (fires "STYLE-006" "The cat sat. The dog ran. The bird flew.")
        (tag ^ ": three The starts"));
  run "STYLE-006 clean: different starts" (fun tag ->
      expect
        (does_not_fire "STYLE-006" "The cat sat. A dog ran. Some bird flew.")
        (tag ^ ": different starts"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-008: Sentence starts with mathematical symbol
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-008 fires: dollar after period" (fun tag ->
      expect (fires "STYLE-008" "We know this. $x$ is important.")
        (tag ^ ": $ after period"));
  run "STYLE-008 clean: no math at sentence start" (fun tag ->
      expect
        (does_not_fire "STYLE-008" "We know that the value is small.")
        (tag ^ ": no math start"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-013: Sentence starts with numeric figure
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-013 fires: digit after period" (fun tag ->
      expect
        (fires "STYLE-013" "We observed this. 42 samples were collected.")
        (tag ^ ": digit after period"));
  run "STYLE-013 clean: word after period" (fun tag ->
      expect
        (does_not_fire "STYLE-013" "We observed this. Many samples were used.")
        (tag ^ ": word after period"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-014: Contraction in formal text
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-014 fires: don't" (fun tag ->
      expect (fires "STYLE-014" "We don't know the answer.")
        (tag ^ ": don't"));
  run "STYLE-014 fires: can't and won't" (fun tag ->
      expect
        (fires_with_count "STYLE-014"
           "We can't do this and won't try." 2)
        (tag ^ ": two contractions"));
  run "STYLE-014 clean: no contractions" (fun tag ->
      expect
        (does_not_fire "STYLE-014"
           "We do not know the answer to this question.")
        (tag ^ ": no contractions"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-015: Double space after period
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-015 fires: double space" (fun tag ->
      expect (fires "STYLE-015" "End of sentence.  Start of next.")
        (tag ^ ": double space"));
  run "STYLE-015 clean: single space" (fun tag ->
      expect
        (does_not_fire "STYLE-015" "End of sentence. Start of next.")
        (tag ^ ": single space"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-016: Latin abbreviation missing comma
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-016 fires: e.g. no comma" (fun tag ->
      expect (fires "STYLE-016" "For example e.g. the first")
        (tag ^ ": e.g. no comma"));
  run "STYLE-016 clean: e.g., with comma" (fun tag ->
      expect
        (does_not_fire "STYLE-016" "For example e.g., the first")
        (tag ^ ": e.g., with comma"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-017: Sentence exceeds 40 words
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-017 fires: long sentence" (fun tag ->
      let long =
        String.concat " " (List.init 45 (fun _ -> "word")) ^ "."
      in
      expect (fires "STYLE-017" long) (tag ^ ": 45-word sentence"));
  run "STYLE-017 clean: short sentence" (fun tag ->
      expect
        (does_not_fire "STYLE-017" "This is a short sentence.")
        (tag ^ ": short sentence"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-019: Multiple consecutive headings without text
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-019 fires: back-to-back sections" (fun tag ->
      expect
        (fires "STYLE-019"
           "\\section{Intro}\n\\subsection{Details}\nSome text here.")
        (tag ^ ": consecutive headings"));
  run "STYLE-019 clean: text between headings" (fun tag ->
      expect
        (does_not_fire "STYLE-019"
           "\\section{Intro}\nSome introductory text.\n\\subsection{Details}")
        (tag ^ ": text between headings"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-023: Percent sign in text not escaped
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-023 fires: bare percent" (fun tag ->
      expect (fires "STYLE-023" "The rate is 50% in 2025.")
        (tag ^ ": bare %"));
  run "STYLE-023 clean: escaped percent" (fun tag ->
      expect
        (does_not_fire "STYLE-023" "The rate is 50\\% in 2025.")
        (tag ^ ": escaped %"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-024: Ampersand in text not escaped
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-024 fires: bare ampersand" (fun tag ->
      expect (fires "STYLE-024" "Smith & Jones wrote the paper.")
        (tag ^ ": bare &"));
  run "STYLE-024 clean: in tabular" (fun tag ->
      expect
        (does_not_fire "STYLE-024"
           "\\begin{tabular}{cc}\na & b\n\\end{tabular}")
        (tag ^ ": in tabular"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-026: Repeated word (the the)
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-026 fires: the the" (fun tag ->
      expect (fires "STYLE-026" "We studied the the effect of light.")
        (tag ^ ": the the"));
  run "STYLE-026 clean: no repeats" (fun tag ->
      expect
        (does_not_fire "STYLE-026" "We studied the effect of light.")
        (tag ^ ": no repeats"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-030: Sub-heading capitalisation inconsistent
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-030 fires: mixed case headings" (fun tag ->
      expect
        (fires "STYLE-030"
           "\\section{The Big Idea}\n\\section{A small concept}")
        (tag ^ ": mixed title/sentence case"));
  run "STYLE-030 clean: consistent case" (fun tag ->
      expect
        (does_not_fire "STYLE-030"
           "\\section{The Big Idea}\n\\section{Another Big Concept}")
        (tag ^ ": consistent title case"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-031: Heading number without title
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-031 fires: number-only heading" (fun tag ->
      expect (fires "STYLE-031" "\\section{3.1}")
        (tag ^ ": number-only heading"));
  run "STYLE-031 clean: real title" (fun tag ->
      expect
        (does_not_fire "STYLE-031" "\\section{Introduction}")
        (tag ^ ": real title"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-033: Space before citation bracket
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-033 fires: space before cite" (fun tag ->
      expect (fires "STYLE-033" "As shown \\cite{smith2020} we see this.")
        (tag ^ ": space before cite"));
  run "STYLE-033 clean: tilde before cite" (fun tag ->
      expect
        (does_not_fire "STYLE-033" "As shown~\\cite{smith2020} we see this.")
        (tag ^ ": tilde before cite"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-034: Orphan word (1-2 letters) at paragraph end
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-034 fires: 2-letter orphan" (fun tag ->
      expect
        (fires "STYLE-034" "This paragraph ends with a short word at")
        (tag ^ ": ends with 'at'"));
  run "STYLE-034 clean: long final word" (fun tag ->
      expect
        (does_not_fire "STYLE-034"
           "This paragraph ends with a longer word here.")
        (tag ^ ": long final word"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-035: Slash used for 'and/or'
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-035 fires: and/or" (fun tag ->
      expect (fires "STYLE-035" "You can use method A and/or method B.")
        (tag ^ ": and/or"));
  run "STYLE-035 clean: no slash" (fun tag ->
      expect
        (does_not_fire "STYLE-035" "You can use method A or method B.")
        (tag ^ ": no and/or"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-036: Latin phrase not italicised
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-036 fires: bare et al." (fun tag ->
      expect (fires "STYLE-036" "Smith et al. showed this result.")
        (tag ^ ": bare et al."));
  run "STYLE-036 clean: italicised et al." (fun tag ->
      expect
        (does_not_fire "STYLE-036"
           "Smith \\emph{et al.} showed this result.")
        (tag ^ ": emph et al."));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-037: Sentence starts with conjunction
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-037 fires: And at sentence start" (fun tag ->
      expect (fires "STYLE-037" "We tested this. And we found results.")
        (tag ^ ": And start"));
  run "STYLE-037 fires: But at sentence start" (fun tag ->
      expect (fires "STYLE-037" "We tested this. But we found nothing.")
        (tag ^ ": But start"));
  run "STYLE-037 clean: no conjunction start" (fun tag ->
      expect
        (does_not_fire "STYLE-037"
           "We tested this. However, we found results.")
        (tag ^ ": no conjunction"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-040: Exclamation mark in academic prose
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-040 fires: exclamation" (fun tag ->
      expect (fires "STYLE-040" "This is amazing!")
        (tag ^ ": exclamation mark"));
  run "STYLE-040 clean: no exclamation" (fun tag ->
      expect
        (does_not_fire "STYLE-040" "This is an important result.")
        (tag ^ ": no exclamation"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-042: Consecutive short paragraphs
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-042 fires: two short paras" (fun tag ->
      expect
        (fires "STYLE-042" "Short one.\n\nAnother short.")
        (tag ^ ": two short paras"));
  run "STYLE-042 clean: normal paras" (fun tag ->
      let normal =
        "This is a sufficiently long paragraph with many words to exceed the fifteen word threshold easily and comfortably by a wide margin.\n\nAnother sufficiently long paragraph with many words that also exceeds the fifteen word threshold comfortably by a margin."
      in
      expect (does_not_fire "STYLE-042" normal) (tag ^ ": normal paras"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-045: Excess parentheses in single sentence
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-045 fires: 4 parens" (fun tag ->
      expect
        (fires "STYLE-045"
           "We (a) tested (b) measured (c) computed (d) verified the result.")
        (tag ^ ": 4 parens"));
  run "STYLE-045 clean: 2 parens" (fun tag ->
      expect
        (does_not_fire "STYLE-045"
           "We tested (alpha) and measured (beta) the effect.")
        (tag ^ ": 2 parens"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-046: Mixed en-dash and em-dash
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-046 fires: mixed dashes" (fun tag ->
      let en = "\xe2\x80\x93" and em = "\xe2\x80\x94" in
      expect
        (fires "STYLE-046"
           ("Pages 1" ^ en ^ "10 and this" ^ em ^ "is important."))
        (tag ^ ": mixed dashes"));
  run "STYLE-046 clean: only en-dash" (fun tag ->
      let en = "\xe2\x80\x93" in
      expect
        (does_not_fire "STYLE-046" ("Pages 1" ^ en ^ "10 in the paper."))
        (tag ^ ": only en-dash"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-048: Word-pair variant mixed
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-048 fires: among/amongst" (fun tag ->
      expect
        (fires "STYLE-048"
           "Among the factors, we found that amongst the results there was consensus.")
        (tag ^ ": among/amongst mix"));
  run "STYLE-048 clean: consistent" (fun tag ->
      expect
        (does_not_fire "STYLE-048" "Among the factors, we found agreement.")
        (tag ^ ": consistent among"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-049: Section heading ends with colon
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-049 fires: heading with colon" (fun tag ->
      expect (fires "STYLE-049" "\\section{Results:}")
        (tag ^ ": colon heading"));
  run "STYLE-049 clean: no colon" (fun tag ->
      expect
        (does_not_fire "STYLE-049" "\\section{Results}")
        (tag ^ ": no colon"));

  finalise "style"
