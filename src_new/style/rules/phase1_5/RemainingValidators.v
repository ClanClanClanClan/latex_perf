(** * REMAINING VALIDATORS - REF, SCRIPT, and CMD rules *)

From Coq Require Import String List Bool Arith.
From validation Require Import ValidationTypes ValidationRules.
From expander Require Import ExpanderTypes.
From lexer Require Import LatexLexer.
Import ListNotations.
Open Scope string_scope.

(** ** Helper: Check if string contains only lowercase *)
Fixpoint is_lowercase (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest =>
      let n := Ascii.nat_of_ascii c in
      if (andb (Nat.leb 97 n) (Nat.leb n 122)) || 
         (andb (Nat.leb 48 n) (Nat.leb n 57)) ||
         (orb (Nat.eqb n 45) (Nat.eqb n 58)) then (* - or : *)
        is_lowercase rest
      else false
  end.

(** ** REF-004: Label contains uppercase letters *)
Fixpoint check_label_case (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "label" :: TBeginGroup :: TText label :: TEndGroup :: rest =>
      if negb (is_lowercase label) then
        {| rule_id := "REF-004"; issue_severity := Info;
           message := String.append "Label '" (String.append label "' contains uppercase letters");
           loc := None; suggested_fix := Some "use_lowercase_labels";
           rule_owner := "@structure" |} :: check_label_case rest
      else check_label_case rest
  | _ :: rest => check_label_case rest
  end.

Definition ref_004_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_label_case expanded
    else [].

(** ** REF-005: Label not prefixed with fig:, tab:, eq:, sec: *)
Fixpoint check_label_prefix (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "label" :: TBeginGroup :: TText label :: TEndGroup :: rest =>
      let prefixes := ["fig:"; "tab:"; "eq:"; "sec:"; "chap:"; "app:"; "alg:"; "thm:"; "lem:"] in
      let has_prefix := existsb (fun prefix => String.prefix prefix label) prefixes in
      if negb has_prefix then
        {| rule_id := "REF-005"; issue_severity := Info;
           message := String.append "Label '" (String.append label 
                     "' should be prefixed with fig:, tab:, eq:, sec:, etc.");
           loc := None; suggested_fix := Some "add_label_prefix";
           rule_owner := "@structure" |} :: check_label_prefix rest
      else check_label_prefix rest
  | _ :: rest => check_label_prefix rest
  end.

Definition ref_005_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_label_prefix expanded
    else [].

(** ** REF-006: Reference to page number uses \ref not \pageref *)
Fixpoint check_pageref_usage (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText "page" :: TSpace :: TCommand "ref" :: rest =>
      {| rule_id := "REF-006"; issue_severity := Info;
         message := "Reference to page number should use \\pageref not \\ref";
         loc := None; suggested_fix := Some "suggest_pageref";
         rule_owner := "@structure" |} :: check_pageref_usage rest
  | TText "Page" :: TSpace :: TCommand "ref" :: rest =>
      {| rule_id := "REF-006"; issue_severity := Info;
         message := "Reference to page number should use \\pageref not \\ref";
         loc := None; suggested_fix := Some "suggest_pageref";
         rule_owner := "@structure" |} :: check_pageref_usage rest
  | _ :: rest => check_pageref_usage rest
  end.

Definition ref_006_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_pageref_usage expanded
    else [].

(** ** REF-007: Cite key contains whitespace *)
Fixpoint check_cite_keys (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand cmd :: TBeginGroup :: TText key :: TEndGroup :: rest =>
      let cite_cmds := ["cite"; "citep"; "citet"; "citeauthor"; "citeyear"] in
      if existsb (String.eqb cmd) cite_cmds then
        if existsb (fun c => Nat.eqb (Ascii.nat_of_ascii c) 32) (string_to_list key) then
          {| rule_id := "REF-007"; issue_severity := Error;
             message := String.append "Citation key '" (String.append key "' contains whitespace");
             loc := None; suggested_fix := Some "remove_whitespace";
             rule_owner := "@bib-team" |} :: check_cite_keys rest
        else check_cite_keys rest
      else check_cite_keys rest
  | _ :: rest => check_cite_keys rest
  end.

Definition ref_007_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_cite_keys expanded
    else [].

(** ** REF-009: Forward references (ref before label) *)
Fixpoint check_forward_refs (tokens : list latex_token) (defined_labels : list string) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "ref" :: TBeginGroup :: TText label :: TEndGroup :: rest =>
      if negb (existsb (String.eqb label) defined_labels) then
        {| rule_id := "REF-009"; issue_severity := Info;
           message := String.append "Forward reference to '" 
                     (String.append label "' (appears before label definition)");
           loc := None; suggested_fix := Some "reorder_content";
           rule_owner := "@structure" |} :: check_forward_refs rest defined_labels
      else check_forward_refs rest defined_labels
  | TCommand "label" :: TBeginGroup :: TText label :: TEndGroup :: rest =>
      check_forward_refs rest (label :: defined_labels)
  | _ :: rest => check_forward_refs rest defined_labels
  end.

Definition ref_009_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_forward_refs expanded []
    else [].

(** ** SCRIPT-002: Superscript dash - instead of -- *)
Fixpoint check_superscript_dash (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TSuperscript :: TText "-" :: rest =>
      {| rule_id := "SCRIPT-002"; issue_severity := Info;
         message := "Single dash in superscript - use \\textsuperscript{--} for endash";
         loc := None; suggested_fix := Some "use_double_dash";
         rule_owner := "@math-rules" |} :: check_superscript_dash rest
  | _ :: rest => check_superscript_dash rest
  end.

Definition script_002_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_superscript_dash expanded
    else [].

(** ** SCRIPT-003: Comma-separated superscripts without braces *)
Fixpoint check_comma_superscripts (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TSuperscript :: TText s :: rest =>
      if string_contains_substring s "," then
        {| rule_id := "SCRIPT-003"; issue_severity := Warning;
           message := String.append "Comma-separated superscript '" 
                     (String.append s "' should use braces");
           loc := None; suggested_fix := Some "add_braces";
           rule_owner := "@math-rules" |} :: check_comma_superscripts rest
      else check_comma_superscripts rest
  | _ :: rest => check_comma_superscripts rest
  end.

Definition script_003_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_comma_superscripts expanded
    else [].

(** ** SCRIPT-005: Letter l instead of \ell *)
Fixpoint check_ell_usage (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TSuperscript :: TText "l" :: rest =>
      {| rule_id := "SCRIPT-005"; issue_severity := Info;
         message := "Superscript 'l' - consider using \\ell for clarity";
         loc := None; suggested_fix := Some "replace_with_ell";
         rule_owner := "@math-rules" |} :: check_ell_usage rest
  | TSubscript :: TText "l" :: rest =>
      {| rule_id := "SCRIPT-005"; issue_severity := Info;
         message := "Subscript 'l' - consider using \\ell for clarity";
         loc := None; suggested_fix := Some "replace_with_ell";
         rule_owner := "@math-rules" |} :: check_ell_usage rest
  | _ :: rest => check_ell_usage rest
  end.

Definition script_005_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_ell_usage expanded
    else [].

(** ** SCRIPT-006: Degree symbol ° instead of ^\circ *)
Definition script_006_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TText s =>
            if string_contains_substring s "°" then
              [{| rule_id := "SCRIPT-006"; issue_severity := Info;
                  message := "Degree symbol ° used - use ^\\circ instead";
                  loc := None; suggested_fix := Some "replace_with_circ";
                  rule_owner := "@math-rules" |}]
            else []
        | _ => []
        end
      ) expanded
    else [].

(** ** CMD-002: \def instead of \renewcommand *)
Fixpoint check_def_usage (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "def" :: TCommand cmd :: rest =>
      {| rule_id := "CMD-002"; issue_severity := Warning;
         message := String.append "Command redefined with \\def - use \\renewcommand{\\" 
                   (String.append cmd "} instead");
         loc := None; suggested_fix := Some "suggest_renewcommand";
         rule_owner := "@structure" |} :: check_def_usage rest
  | _ :: rest => check_def_usage rest
  end.

Definition cmd_002_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_def_usage expanded
    else [].

(** ** CMD-003: Command name clashes with package macro *)
Definition cmd_003_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      (* Common package commands that shouldn't be redefined *)
      let package_commands := ["section"; "chapter"; "cite"; "ref"; "label"; 
                              "includegraphics"; "textbf"; "emph"; "footnote"] in
      
      let check_newcommand (toks : list latex_token) : list validation_issue :=
        match toks with
        | TCommand "newcommand" :: TBeginGroup :: TCommand cmd :: rest =>
            if existsb (String.eqb cmd) package_commands then
              [{| rule_id := "CMD-003"; issue_severity := Warning;
                  message := String.append "User command \\" 
                            (String.append cmd " may clash with package macro");
                  loc := None; suggested_fix := Some "rename_command";
                  rule_owner := "@pkg-lint" |}]
            else []
        | _ => []
        end in
        
      flat_map check_newcommand (windows 10 expanded)
    else [].

(** ** CMD-004: CamelCase command names *)
Fixpoint has_uppercase (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
      let n := Ascii.nat_of_ascii c in
      if andb (Nat.leb 65 n) (Nat.leb n 90) then true
      else has_uppercase rest
  end.

Definition cmd_004_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      
      let check_camelcase (toks : list latex_token) : list validation_issue :=
        match toks with
        | TCommand "newcommand" :: TBeginGroup :: TCommand cmd :: rest =>
            if has_uppercase cmd then
              [{| rule_id := "CMD-004"; issue_severity := Info;
                  message := String.append "CamelCase command name \\" 
                            (String.append cmd " - LaTeX convention prefers lowercase");
                  loc := None; suggested_fix := Some "use_lowercase";
                  rule_owner := "@style-council" |}]
            else []
        | _ => []
        end in
        
      flat_map check_camelcase (windows 10 expanded)
    else [].

(** ** CMD-005: Single-letter macro *)
Definition cmd_005_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      
      let check_single_letter (toks : list latex_token) : list validation_issue :=
        match toks with
        | TCommand "newcommand" :: TBeginGroup :: TCommand cmd :: rest =>
            if String.length cmd =? 1 then
              [{| rule_id := "CMD-005"; issue_severity := Warning;
                  message := String.append "Single-letter macro \\" 
                            (String.append cmd " created - may cause conflicts");
                  loc := None; suggested_fix := Some "use_longer_name";
                  rule_owner := "@structure" |}]
            else []
        | _ => []
        end in
        
      flat_map check_single_letter (windows 10 expanded)
    else [].

(** Helper to create sliding windows of tokens *)
Fixpoint windows (n : nat) (l : list latex_token) : list (list latex_token) :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | S n', h :: t =>
      let window := firstn (S n') (h :: t) in
      if length window =? S n' then
        window :: windows (S n') t
      else
        []
  end.

(** Helper to take first n elements *)
Fixpoint firstn (n : nat) (l : list latex_token) : list latex_token :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | S n', h :: t => h :: firstn n' t
  end.