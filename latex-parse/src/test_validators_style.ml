(** Unit tests for L4 STYLE text-scannable rules: 25 rules. STYLE-004..049
    (Phase 1 batch). ~125 total test cases. *)

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
      expect
        (fires "STYLE-008" "We know this. $x$ is important.")
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
      expect (fires "STYLE-014" "We don't know the answer.") (tag ^ ": don't"));
  run "STYLE-014 fires: can't and won't" (fun tag ->
      expect
        (fires_with_count "STYLE-014" "We can't do this and won't try." 2)
        (tag ^ ": two contractions"));
  run "STYLE-014 clean: no contractions" (fun tag ->
      expect
        (does_not_fire "STYLE-014" "We do not know the answer to this question.")
        (tag ^ ": no contractions"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-015: Double space after period
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-015 fires: double space" (fun tag ->
      expect
        (fires "STYLE-015" "End of sentence.  Start of next.")
        (tag ^ ": double space"));
  run "STYLE-015 clean: single space" (fun tag ->
      expect
        (does_not_fire "STYLE-015" "End of sentence. Start of next.")
        (tag ^ ": single space"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-016: Latin abbreviation missing comma
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-016 fires: e.g. no comma" (fun tag ->
      expect
        (fires "STYLE-016" "For example e.g. the first")
        (tag ^ ": e.g. no comma"));
  run "STYLE-016 clean: e.g., with comma" (fun tag ->
      expect
        (does_not_fire "STYLE-016" "For example e.g., the first")
        (tag ^ ": e.g., with comma"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-017: Sentence exceeds 40 words
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-017 fires: long sentence" (fun tag ->
      let long = String.concat " " (List.init 45 (fun _ -> "word")) ^ "." in
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
      expect (fires "STYLE-023" "The rate is 50% in 2025.") (tag ^ ": bare %"));
  run "STYLE-023 clean: escaped percent" (fun tag ->
      expect
        (does_not_fire "STYLE-023" "The rate is 50\\% in 2025.")
        (tag ^ ": escaped %"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-024: Ampersand in text not escaped
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-024 fires: bare ampersand" (fun tag ->
      expect
        (fires "STYLE-024" "Smith & Jones wrote the paper.")
        (tag ^ ": bare &"));
  run "STYLE-024 clean: in tabular" (fun tag ->
      expect
        (does_not_fire "STYLE-024" "\\begin{tabular}{cc}\na & b\n\\end{tabular}")
        (tag ^ ": in tabular"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-026: Repeated word (the the)
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-026 fires: the the" (fun tag ->
      expect
        (fires "STYLE-026" "We studied the the effect of light.")
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
        (fires "STYLE-030" "\\section{The Big Idea}\n\\section{A small concept}")
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
      expect (fires "STYLE-031" "\\section{3.1}") (tag ^ ": number-only heading"));
  run "STYLE-031 clean: real title" (fun tag ->
      expect
        (does_not_fire "STYLE-031" "\\section{Introduction}")
        (tag ^ ": real title"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-033: Space before citation bracket
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-033 fires: space before cite" (fun tag ->
      expect
        (fires "STYLE-033" "As shown \\cite{smith2020} we see this.")
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
      expect
        (fires "STYLE-035" "You can use method A and/or method B.")
        (tag ^ ": and/or"));
  run "STYLE-035 clean: no slash" (fun tag ->
      expect
        (does_not_fire "STYLE-035" "You can use method A or method B.")
        (tag ^ ": no and/or"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-036: Latin phrase not italicised
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-036 fires: bare et al." (fun tag ->
      expect
        (fires "STYLE-036" "Smith et al. showed this result.")
        (tag ^ ": bare et al."));
  run "STYLE-036 clean: italicised et al." (fun tag ->
      expect
        (does_not_fire "STYLE-036" "Smith \\emph{et al.} showed this result.")
        (tag ^ ": emph et al."));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-037: Sentence starts with conjunction
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-037 fires: And at sentence start" (fun tag ->
      expect
        (fires "STYLE-037" "We tested this. And we found results.")
        (tag ^ ": And start"));
  run "STYLE-037 fires: But at sentence start" (fun tag ->
      expect
        (fires "STYLE-037" "We tested this. But we found nothing.")
        (tag ^ ": But start"));
  run "STYLE-037 clean: no conjunction start" (fun tag ->
      expect
        (does_not_fire "STYLE-037" "We tested this. However, we found results.")
        (tag ^ ": no conjunction"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-040: Exclamation mark in academic prose
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-040 fires: exclamation" (fun tag ->
      expect (fires "STYLE-040" "This is amazing!") (tag ^ ": exclamation mark"));
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
        "This is a sufficiently long paragraph with many words to exceed the \
         fifteen word threshold easily and comfortably by a wide margin.\n\n\
         Another sufficiently long paragraph with many words that also exceeds \
         the fifteen word threshold comfortably by a margin."
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
           "Among the factors, we found that amongst the results there was \
            consensus.")
        (tag ^ ": among/amongst mix"));
  run "STYLE-048 clean: consistent" (fun tag ->
      expect
        (does_not_fire "STYLE-048" "Among the factors, we found agreement.")
        (tag ^ ": consistent among"));

  (* ══════════════════════════════════════════════════════════════════════
     STYLE-049: Section heading ends with colon
     ══════════════════════════════════════════════════════════════════════ *)
  run "STYLE-049 fires: heading with colon" (fun tag ->
      expect (fires "STYLE-049" "\\section{Results:}") (tag ^ ": colon heading"));
  run "STYLE-049 clean: no colon" (fun tag ->
      expect
        (does_not_fire "STYLE-049" "\\section{Results}")
        (tag ^ ": no colon"));

  (* ══════════════════════════════════════════════════════════════════════
     Phase 2 rules
     ══════════════════════════════════════════════════════════════════════ *)

  (* STYLE-001 *)
  run "STYLE-001 fires: mixed oxford comma" (fun tag ->
      expect
        (fires "STYLE-001"
           "We tested cats, dogs, and birds. We also saw lions, tigers and \
            bears.")
        (tag ^ ": mixed oxford"));
  run "STYLE-001 clean: consistent" (fun tag ->
      expect
        (does_not_fire "STYLE-001"
           "We tested cats, dogs, and birds. We saw lions, tigers, and bears.")
        (tag ^ ": consistent oxford"));

  (* STYLE-002 *)
  run "STYLE-002 fires: mixed UK/US" (fun tag ->
      expect
        (fires "STYLE-002" "The colour of the color wheel is nice.")
        (tag ^ ": colour/color mix"));
  run "STYLE-002 clean: UK only" (fun tag ->
      expect
        (does_not_fire "STYLE-002" "The colour of the favour is good.")
        (tag ^ ": UK only"));

  (* STYLE-005 *)
  run "STYLE-005 fires: mixed we/I" (fun tag ->
      expect
        (fires "STYLE-005"
           "In this paper, we tested this method. I think the results are good.")
        (tag ^ ": we and I"));
  run "STYLE-005 clean: we only" (fun tag ->
      expect
        (does_not_fire "STYLE-005" "We tested and we measured the results.")
        (tag ^ ": we only"));

  (* STYLE-007 *)
  run "STYLE-007 fires: mixed item punct" (fun tag ->
      expect
        (fires "STYLE-007"
           "\\begin{itemize}\n\
            \\item First item.\n\
            \\item Second item\n\
            \\end{itemize}")
        (tag ^ ": mixed item punct"));
  run "STYLE-007 clean: consistent item punct" (fun tag ->
      expect
        (does_not_fire "STYLE-007"
           "\\begin{itemize}\n\
            \\item First item.\n\
            \\item Second item.\n\
            \\end{itemize}")
        (tag ^ ": consistent punct"));

  (* STYLE-009 *)
  run "STYLE-009 fires: mixed cite styles" (fun tag ->
      expect
        (fires "STYLE-009" "As shown \\cite{a} and also \\citep{b}.")
        (tag ^ ": cite + citep"));
  run "STYLE-009 clean: single style" (fun tag ->
      expect
        (does_not_fire "STYLE-009" "As shown \\citep{a} and \\citep{b}.")
        (tag ^ ": citep only"));

  (* STYLE-010 *)
  run "STYLE-010 fires: I in multi-author" (fun tag ->
      expect
        (fires "STYLE-010"
           "\\author{Alice and Bob}\nIn this paper, I present results.")
        (tag ^ ": I + multi author"));
  run "STYLE-010 clean: single author" (fun tag ->
      expect
        (does_not_fire "STYLE-010"
           "\\author{Alice}\nIn this paper, I present results.")
        (tag ^ ": single author"));

  (* STYLE-011 *)
  run "STYLE-011 fires: mixed ranges" (fun tag ->
      expect
        (fires "STYLE-011" "Pages 1-10 and also pages 20--30.")
        (tag ^ ": mixed range dashes"));
  run "STYLE-011 clean: consistent" (fun tag ->
      expect
        (does_not_fire "STYLE-011" "Pages 1--10 and pages 20--30.")
        (tag ^ ": consistent endash"));

  (* STYLE-018 *)
  run "STYLE-018 fires: dangling this" (fun tag ->
      expect
        (fires "STYLE-018" "This is important for our work.")
        (tag ^ ": this is"));
  run "STYLE-018 clean: this + noun" (fun tag ->
      expect
        (does_not_fire "STYLE-018" "This method improves performance.")
        (tag ^ ": this method"));

  (* STYLE-020 *)
  run "STYLE-020 fires: unused acronym" (fun tag ->
      expect
        (fires "STYLE-020"
           "The Machine Learning (ML) approach. The Deep Learning (DL) method.")
        (tag ^ ": DL never used again"));
  run "STYLE-020 clean: acronym used" (fun tag ->
      expect
        (does_not_fire "STYLE-020"
           "The Machine Learning (ML) approach. ML is powerful.")
        (tag ^ ": ML used"));

  (* STYLE-021 *)
  run "STYLE-021 fires: acronym before def" (fun tag ->
      expect
        (fires "STYLE-021"
           "We use CNN for classification. Convolutional Neural Network (CNN) \
            is defined here.")
        (tag ^ ": CNN before def"));
  run "STYLE-021 clean: def before use" (fun tag ->
      expect
        (does_not_fire "STYLE-021"
           "Convolutional Neural Network (CNN) is powerful. CNN excels.")
        (tag ^ ": def before use"));

  (* STYLE-022 *)
  run "STYLE-022 fires: missing serial comma" (fun tag ->
      expect
        (fires "STYLE-022" "We studied cats, dogs and birds.")
        (tag ^ ": missing serial comma"));
  run "STYLE-022 clean: has serial comma" (fun tag ->
      expect
        (does_not_fire "STYLE-022" "We studied cats, dogs, and birds.")
        (tag ^ ": has serial comma"));

  (* STYLE-025 *)
  run "STYLE-025 fires: run-on" (fun tag ->
      let runon = String.concat " " (List.init 65 (fun _ -> "word")) ^ "." in
      expect (fires "STYLE-025" runon) (tag ^ ": 65-word sentence"));
  run "STYLE-025 clean: normal" (fun tag ->
      expect
        (does_not_fire "STYLE-025" "This sentence is quite normal.")
        (tag ^ ": normal sentence"));

  (* STYLE-027 *)
  run "STYLE-027 fires: adverb overuse" (fun tag ->
      let adverby =
        String.concat " "
          (List.init 50 (fun i -> if i mod 8 = 0 then "quickly" else "the"))
      in
      expect (fires "STYLE-027" adverby) (tag ^ ": adverb overuse"));
  run "STYLE-027 clean: few adverbs" (fun tag ->
      expect
        (does_not_fire "STYLE-027"
           "We tested carefully. The results clearly show improvement.")
        (tag ^ ": few adverbs"));

  (* STYLE-028 *)
  run "STYLE-028 fires: eqref no punct" (fun tag ->
      expect
        (fires "STYLE-028" "As shown in \\eqref{eq1} the result holds.")
        (tag ^ ": eqref no punct"));
  run "STYLE-028 clean: eqref with punct" (fun tag ->
      expect
        (does_not_fire "STYLE-028" "As shown in \\eqref{eq1}, the result holds.")
        (tag ^ ": eqref with comma"));

  (* ── Locale rules ────────────────────────────────────────────────── *)

  (* CE-001 *)
  run "CE-001 fires: colour/color mix" (fun tag ->
      expect
        (fires "CE-001" "The colour of the color wheel.")
        (tag ^ ": colour/color"));
  run "CE-001 clean: consistent" (fun tag ->
      expect
        (does_not_fire "CE-001" "The colour of the favour is good.")
        (tag ^ ": UK consistent"));

  (* CE-002 *)
  run "CE-002 fires: no oxford" (fun tag ->
      expect
        (fires "CE-002" "We studied cats, dogs and birds.")
        (tag ^ ": no oxford"));
  run "CE-002 clean: oxford present" (fun tag ->
      expect
        (does_not_fire "CE-002" "We studied cats, dogs, and birds.")
        (tag ^ ": oxford present"));

  (* TH-001 *)
  run "TH-001 fires: Thai vowel at line start" (fun tag ->
      (* U+0E40 = E0 B9 80 *)
      let thai_line = "\xe0\xb9\x80\xe0\xb8\x82\xe0\xb8\xb2" in
      expect (fires "TH-001" thai_line) (tag ^ ": Thai vowel line start"));
  run "TH-001 clean: no Thai" (fun tag ->
      expect (does_not_fire "TH-001" "Normal English text.") (tag ^ ": no Thai"));

  (* LANG-012 *)
  run "LANG-012 fires: babel/selectlanguage mismatch" (fun tag ->
      expect
        (fires "LANG-012"
           "\\usepackage[english]{babel}\n\\selectlanguage{french}")
        (tag ^ ": babel mismatch"));
  run "LANG-012 clean: matching" (fun tag ->
      expect
        (does_not_fire "LANG-012"
           "\\usepackage[french]{babel}\n\\selectlanguage{french}")
        (tag ^ ": matching"));

  (* LANG-014 *)
  run "LANG-014 fires: mixed ize/ise" (fun tag ->
      expect
        (fires "LANG-014" "We organized the data and recognised the pattern.")
        (tag ^ ": organize/recognise mix"));
  run "LANG-014 clean: consistent" (fun tag ->
      expect
        (does_not_fire "LANG-014" "We organised and analysed the data.")
        (tag ^ ": ise consistent"));

  (* LANG-016 *)
  run "LANG-016 fires: programme/program mix" (fun tag ->
      expect
        (fires "LANG-016" "The programme includes a program for training.")
        (tag ^ ": programme/program"));
  run "LANG-016 clean: consistent" (fun tag ->
      expect
        (does_not_fire "LANG-016"
           "The programme is part of the larger programme.")
        (tag ^ ": programme consistent"));

  finalise "style"
