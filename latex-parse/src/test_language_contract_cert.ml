(** Adversarial certification of the LP-Core classifier's byte-level boundary.

    Context: the compile guarantee is scoped to the DECIDABLE subset LP-Core,
    which EXCLUDES arbitrary \def/\csname/\catcode and non-catalogue primitive
    conditionals, plus every LP-Foreign escape hatch (\write18, \directlua,
    shell-escape). The tier DECISION (feature-list -> tier) is the Coq-EXTRACTED
    [Language_contract_extracted.classify] (proofs/LanguageContractExtract.v,
    governed by [classify_lp_core_sound], Qed, 0 admits). The remaining TRUSTED
    step is [Unsupported_feature.detect] (bytes -> feature-list): this test
    adversarially certifies that detect (hence classify_source) catches EVERY
    forbidden-in-core construct and EVERY LP-Foreign trigger across MULTIPLE
    syntactic forms (whitespace, comments, line breaks, obfuscation), while
    genuine LP-Core documents stay LP_Core.

    If any forbidden construct classifies as LP_Core, that is a REAL soundness
    gap: this test fails loudly rather than silently trusting the regex. *)

open Latex_parse_lib
open Test_helpers

let classify s = fst (Language_profile.classify_source s)
let tier_s = Language_profile.tier_to_string

(* A forbidden-in-core construct (family) with several syntactic FORMS. Every
   form must classify as NOT LP_Core (i.e. LP_Extended, since none of these are
   foreign). *)
let forbidden_families : (string * string list) list =
  [
    ( "arbitrary_def",
      [
        "\\def\\x{y}";
        "\\def \\x{y}";
        "\\def  \\x{y}";
        "\\def\t\\x{y}";
        "\\def\n\\x{y}";
        "\\def%comment\n\\x{y}";
        "\\def%\n\\x{y}";
        "prose then \\def\\macro{payload} and more";
        "  \\def\\foo{bar}";
      ] );
    ( "expanded_def",
      [ "\\edef\\x{y}"; "\\gdef\\x{}"; "\\xdef\\x{}"; "\\edef \\y{z}" ] );
    ("let_alias", [ "\\let\\x=\\y"; "\\let\\x\\y"; "\\futurelet\\a\\b" ]);
    ( "csname_metaprogramming",
      [
        "\\csname foo\\endcsname";
        "\\csname foo \\endcsname";
        "\\expandafter\\csname x\\endcsname";
        "\\csname\nfoo\\endcsname";
        "\\csname%c\nfoo\\endcsname";
        "\\csname a@b\\endcsname";
      ] );
    ("makeatletter", [ "\\makeatletter"; "  \\makeatletter\n" ]);
    ("expandafter_chain", [ "\\expandafter\\expandafter\\x" ]);
    ( "primitive_conditionals",
      [
        "\\ifnum1<2 x\\fi";
        "\\ifnum 1<2 x\\fi";
        "\\ifdim1pt<2pt\\fi";
        "\\ifx\\a\\b\\fi";
        "\\ifx \\a\\b\\fi";
        "\\ifodd\\count0\\fi";
        "\\ifcase2\\fi";
        "\\ifcase 2\\fi";
        "\\iftrue\\fi";
        "\\iffalse\\fi";
        "\\ifcat ab\\fi";
        "\\ifhmode\\fi";
        "\\ifvmode\\fi";
        "\\ifmmode\\fi";
        "\\ifinner\\fi";
        "\\ifdefined\\x\\fi";
        "\\ifcsname x\\endcsname\\fi";
        "\\ifeof0\\fi";
        "\\ifvoid0\\fi";
        "\\ifhbox0\\fi";
        "\\ifvbox0\\fi";
        "\\if ab\\fi";
      ] );
  ]

(* LP-Foreign escape hatches: every form must classify as LP_Foreign. *)
let foreign_families : (string * string list) list =
  [
    ( "shell_escape_write18",
      [ "\\write18{ls}"; "\\immediate\\write18{ls}"; "\\write18 {rm -rf}" ] );
    ("shell_escape_command", [ "\\ShellEscape{ls}" ]);
    ( "catcode_mutation",
      [
        "\\catcode`\\@=11";
        "\\catcode `\\@=11";
        "\\catcode`@=12";
        "\\catcode65=12";
      ] );
    ("lua_scripting", [ "\\directlua{print(1)}"; "\\latelua{x}"; "\\luaexec{}" ]);
    ("scantokens", [ "\\scantokens{x}" ]);
    ("detokenize", [ "\\detokenize{x}" ]);
    ("csstring", [ "\\csstring\\x" ]);
    ("openout", [ "\\openout1=x"; "\\openout\\myout=x" ]);
  ]

(* Obfuscation attempts: constructs hidden inside realistic surrounding text,
   after comments, split across lines, embedded mid-document. *)
let obfuscated_forbidden : (string * string) list =
  [
    ( "def-after-comment",
      "\\documentclass{article}\n% define below\n\\def\\evil{x}\n" );
    ( "csname-split-lines",
      "\\begin{document}\\csname\n  relax\\endcsname\\end{document}" );
    ( "def-mid-paragraph",
      "Some prose and then \\def\\macro{payload} more prose." );
    ( "conditional-in-body",
      "\\begin{document}\n\
       Text \\ifnum\\value{x}>0 A\\else B\\fi text\n\
       \\end{document}" );
  ]

let obfuscated_foreign : (string * string) list =
  [
    ("write18-immediate", "text\n\\immediate\\write18 {rm -rf}\ntext");
    ( "directlua-in-body",
      "\\begin{document}\n\\directlua{os.execute('ls')}\n\\end{document}" );
    ("catcode-spaced", "preamble\n\\catcode `\\@ =11\nmore");
  ]

(* Genuine LP-Core documents: must STAY LP_Core (no over-flagging). Includes
   near-miss lexical traps: \mydef, the word "define", \textbf{def}. *)
let genuine_core : (string * string) list =
  [
    ("newcommand", "\\newcommand{\\x}{y}");
    ("renewcommand", "\\renewcommand{\\x}{y}");
    ("providecommand", "\\providecommand{\\x}{y}");
    ("usepackage", "\\usepackage{amsmath}");
    ("section", "\\section{Introduction}");
    ("textbf-def-word", "This \\textbf{def}inition is fine.");
    ("mydef-macro", "\\mydef stuff here");
    ("define-prose", "We now define a precise notion of x.");
    ("label-ref", "\\label{a}\\ref{a}\\eqref{a}");
    ("equation-env", "\\begin{equation}a=b\\end{equation}");
    ("newenvironment", "\\newenvironment{e}{}{}");
    ("citations", "\\cite{key} and \\includegraphics{fig}");
    ("title-block", "\\title{T}\\author{A}\\date{\\today}");
    ("emph-item", "\\emph{different}\\item text\\footnote{n}");
    ("coefficient-prose", "The coefficient definitely helps here.");
  ]

let () =
  let forbidden_forms = ref 0 in
  List.iter
    (fun (fam, forms) ->
      List.iter
        (fun src ->
          incr forbidden_forms;
          run (Printf.sprintf "forbidden %s stays out of LP-Core" fam)
            (fun tag ->
              let t = classify src in
              expect
                (t <> Language_profile.LP_Core)
                (Printf.sprintf "%s: [%s] classified '%s' as LP_Core (SLIP)" tag
                   (tier_s t) (String.escaped src))))
        forms)
    forbidden_families;

  let foreign_forms = ref 0 in
  List.iter
    (fun (fam, forms) ->
      List.iter
        (fun src ->
          incr foreign_forms;
          run (Printf.sprintf "foreign %s classifies as LP-Foreign" fam)
            (fun tag ->
              let t = classify src in
              expect
                (t = Language_profile.LP_Foreign)
                (Printf.sprintf "%s: [%s] classified '%s' not LP_Foreign (SLIP)"
                   tag (tier_s t) (String.escaped src))))
        forms)
    foreign_families;

  let obf_forbidden = ref 0 in
  List.iter
    (fun (name, src) ->
      incr obf_forbidden;
      run (Printf.sprintf "obfuscated forbidden %s caught" name) (fun tag ->
          let t = classify src in
          expect
            (t <> Language_profile.LP_Core)
            (Printf.sprintf "%s: [%s] slipped as LP_Core" tag (tier_s t))))
    obfuscated_forbidden;

  let obf_foreign = ref 0 in
  List.iter
    (fun (name, src) ->
      incr obf_foreign;
      run (Printf.sprintf "obfuscated foreign %s caught" name) (fun tag ->
          let t = classify src in
          expect
            (t = Language_profile.LP_Foreign)
            (Printf.sprintf "%s: [%s] not LP_Foreign" tag (tier_s t))))
    obfuscated_foreign;

  let core_docs = ref 0 in
  List.iter
    (fun (name, src) ->
      incr core_docs;
      run (Printf.sprintf "genuine LP-Core %s stays LP-Core" name) (fun tag ->
          let t = classify src in
          expect
            (t = Language_profile.LP_Core)
            (Printf.sprintf "%s: [%s] over-flagged (false positive)" tag
               (tier_s t))))
    genuine_core;

  (* Cross-check: the extracted classify agrees with a foreign>forbidden>core
     precedence when both a forbidden and a foreign construct are present. *)
  run "foreign dominates forbidden (extracted precedence)" (fun tag ->
      let src = "\\def\\x{y}\n\\write18{ls}\n" in
      expect
        (classify src = Language_profile.LP_Foreign)
        (tag ^ ": " ^ tier_s (classify src)));

  Printf.printf
    "[cert] forbidden_forms=%d foreign_forms=%d obf_forbidden=%d \
     obf_foreign=%d core_docs=%d families=%d\n\
     %!"
    !forbidden_forms !foreign_forms !obf_forbidden !obf_foreign !core_docs
    (List.length forbidden_families + List.length foreign_families);

  finalise "language_contract_cert"
