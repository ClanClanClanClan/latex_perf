(** Detection of LaTeX source constructs outside the LP-Core subset.

    See [unsupported_feature.mli] and [specs/v26/language_contract.yaml]. *)

type severity = Forbidden_in_core | Foreign_trigger

type t = {
  id : string;
  severity : severity;
  offset : int;
  line : int;
  message : string;
}

let severity_to_string = function
  | Forbidden_in_core -> "forbidden_in_core"
  | Foreign_trigger -> "foreign_trigger"

type feature_def = {
  f_id : string;
  f_severity : severity;
  f_pattern : string;
  f_message : string;
}
(** Feature definition used by the detection scanner. *)

(* Each pattern is a Re_compat (Str-syntax) regex. We deliberately use narrow
   literal patterns rather than attempt full parsing; the detector errs on the
   side of demoting a document (LP-Core -> LP-Extended) when ambiguous. *)

let foreign_triggers : feature_def list =
  [
    {
      f_id = "shell_escape_invocation";
      f_severity = Foreign_trigger;
      f_pattern = "\\\\\\(immediate\\\\\\)?write18";
      f_message = "shell-escape (\\write18) detected; LP-Foreign";
    };
    {
      f_id = "shell_escape_command";
      f_severity = Foreign_trigger;
      f_pattern = "\\\\ShellEscape";
      f_message = "\\ShellEscape detected; LP-Foreign";
    };
    {
      f_id = "catcode_mutation_direct";
      f_severity = Foreign_trigger;
      (* Match the bare \catcode primitive: it may be followed by a space then a
         backtick (\catcode `\@) or directly by a char-code number
         (\catcode65=12). Matching the control word alone is sufficient and
         safe: the only strict superstring is the LuaTeX \catcodetable
         primitive, which is itself outside LP-Core. *)
      f_pattern = "\\\\catcode";
      f_message = "\\catcode direct mutation detected; LP-Foreign";
    };
    {
      f_id = "scantokens_primitive";
      f_severity = Foreign_trigger;
      f_pattern = "\\\\scantokens";
      f_message = "\\scantokens primitive detected; LP-Foreign";
    };
    {
      f_id = "detokenize_primitive";
      f_severity = Foreign_trigger;
      f_pattern = "\\\\detokenize";
      f_message = "\\detokenize primitive detected; LP-Foreign";
    };
    {
      f_id = "csstring_primitive";
      f_severity = Foreign_trigger;
      f_pattern = "\\\\csstring";
      f_message = "\\csstring primitive detected; LP-Foreign";
    };
    {
      f_id = "openout_primitive";
      f_severity = Foreign_trigger;
      f_pattern = "\\\\openout[0-9\\\\]";
      f_message = "\\openout file-output primitive detected; LP-Foreign";
    };
    (* LuaTeX scripting escape hatches: arbitrary Lua execution at typeset time
       is a shell-escape-class capability → LP-Foreign. \directlua / \latelua
       run code immediately/late; \luaexec is the ConTeXt/luacode wrapper. Word
       boundary \b avoids matching longer identifiers. *)
    {
      f_id = "directlua_primitive";
      f_severity = Foreign_trigger;
      f_pattern = "\\\\\\(directlua\\|latelua\\|luaexec\\)\\b";
      f_message = "\\directlua/\\latelua/\\luaexec scripting; LP-Foreign";
    };
    (* \write to stream 18 is shell-escape; the earlier shell_escape_invocation
       pattern requires the literal "write18". A \write to the shell-escape
       stream can also be written with an intervening (immediate) or spaces;
       that is covered above. *)
  ]

let core_forbidden : feature_def list =
  [
    (* Arbitrary \def outside the \newcommand family. \def is a control WORD, so
       TeX terminates it at any non-letter (space, comment, {, or the backslash
       of the defined macro). We anchor on the word boundary \b after "def" so
       we still catch \def\x, "\def \x", "\def%c\n\x", "\def\n\x" — all
       syntactic forms — without matching longer identifiers like
       \defaultfontfeatures (no boundary between "def" and "a"). *)
    {
      f_id = "arbitrary_def";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\def\\b";
      f_message = "\\def outside \\newcommand family; not LP-Core";
    };
    (* The expanded/global \def variants are equally arbitrary macro-definition
       primitives (Turing-complete metaprogramming): \edef \gdef \xdef. \b
       anchors avoid matching \edefault etc. *)
    {
      f_id = "arbitrary_edef";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\\\(edef\\|gdef\\|xdef\\)\\b";
      f_message = "\\edef/\\gdef/\\xdef expanded macro definition; not LP-Core";
    };
    (* \let and \futurelet alias control sequences to arbitrary meanings — a
       def-family metaprogramming primitive outside \newcommand. *)
    {
      f_id = "arbitrary_let";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\\\(let\\|futurelet\\)\\b";
      f_message = "\\let/\\futurelet control-sequence aliasing; not LP-Core";
    };
    (* \makeatletter in document body (we don't know body boundaries without
       parsing; we flag any occurrence — package internals handle their own
       \makeatletter/\makeatother elsewhere. This deliberately over-flags; the
       classifier treats this as a demotion to LP-Extended only, not LP-Foreign,
       so the cost is bounded. *)
    {
      f_id = "makeatletter";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\makeatletter";
      f_message = "\\makeatletter detected; demotes to LP-Extended";
    };
    (* \csname...\endcsname (basic form). Dynamic/static variants both surface
       here — they're treated as LP-Extended, not LP-Foreign, unless the
       expansion clearly contains a primitive. *)
    {
      f_id = "csname_construct";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\csname";
      f_message = "\\csname metaprogramming; not LP-Core";
    };
    (* Primitive conditionals outside supported catalogue. *)
    {
      f_id = "primitive_ifnum";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\ifnum";
      f_message = "\\ifnum primitive conditional; not LP-Core";
    };
    {
      f_id = "primitive_ifdim";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\ifdim";
      f_message = "\\ifdim primitive conditional; not LP-Core";
    };
    {
      f_id = "primitive_ifx";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\ifx\\b";
      f_message = "\\ifx primitive conditional; not LP-Core";
    };
    {
      f_id = "primitive_ifodd";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\ifodd";
      f_message = "\\ifodd primitive conditional; not LP-Core";
    };
    (* The remaining TeX primitive conditionals outside the supported catalogue.
       Matched by exact primitive name (no trailing \b: these primitives are
       frequently followed immediately by a digit/box register — e.g.
       "\ifcase2", "\ifnum1<2" — where a word-boundary would fail to fire). No
       standard package macro is a strict superstring of these names, so the
       bare-name match does not over-reach. Longer engine/package conditionals
       (\ifpdf, \ifluatex, \ifthenelse) are NOT members of this alternation and
       are handled by their own catalogue entries elsewhere. *)
    {
      f_id = "primitive_conditionals";
      f_severity = Forbidden_in_core;
      f_pattern =
        "\\\\\\(ifcase\\|ifcat\\|ifhmode\\|ifvmode\\|ifmmode\\|ifinner\\|ifhbox\\|ifvbox\\|ifvoid\\|ifeof\\|iftrue\\|iffalse\\|ifdefined\\|ifcsname\\|ifdim\\|ifnum\\|ifodd\\|ifx\\)";
      f_message = "primitive conditional outside catalogue; not LP-Core";
    };
    (* Bare \if primitive (\if <token1><token2>): two-char control word. Anchor
       with \b so it fires only on the standalone primitive, never on the
       \ifsomething family (which the entry above and the catalogue cover). *)
    {
      f_id = "primitive_if_bare";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\if\\b";
      f_message = "bare \\if primitive conditional; not LP-Core";
    };
    {
      f_id = "expandafter_chain";
      f_severity = Forbidden_in_core;
      f_pattern = "\\\\expandafter\\\\expandafter";
      f_message = "chained \\expandafter; not LP-Core";
    };
  ]

(* Pre-compile all regexes once at module load. *)
let compiled_foreign =
  List.map (fun fd -> (fd, Re_compat.regexp fd.f_pattern)) foreign_triggers

let compiled_core =
  List.map (fun fd -> (fd, Re_compat.regexp fd.f_pattern)) core_forbidden

(** Count newlines in [src] up to [offset] to derive a 1-indexed line number. *)
let line_at_offset src offset =
  let n = min offset (String.length src) in
  let lines = ref 1 in
  for i = 0 to n - 1 do
    if String.unsafe_get src i = '\n' then incr lines
  done;
  !lines

(** Scan [src] for every match of [re] and invoke [f] with each start offset. No
    allocation beyond the returned accumulator. *)
let scan_all src re f acc =
  let len = String.length src in
  let rec loop pos acc =
    if pos >= len then acc
    else
      match Re_compat.search_forward re src pos with
      | exception Not_found -> acc
      | mr, start_pos ->
          let acc = f start_pos acc in
          let next = max (start_pos + 1) (Re_compat.match_end mr) in
          loop next acc
  in
  loop 0 acc

let detect src =
  let collect defs compiled acc =
    List.fold_left2
      (fun acc fd (_, re) ->
        scan_all src re
          (fun start_pos acc ->
            {
              id = fd.f_id;
              severity = fd.f_severity;
              offset = start_pos;
              line = line_at_offset src start_pos;
              message = fd.f_message;
            }
            :: acc)
          acc)
      acc defs compiled
  in
  let acc = collect foreign_triggers compiled_foreign [] in
  let acc = collect core_forbidden compiled_core acc in
  List.sort (fun a b -> compare a.offset b.offset) acc

let any_foreign_trigger xs =
  List.exists (fun x -> x.severity = Foreign_trigger) xs

let any_forbidden_in_core xs =
  List.exists (fun x -> x.severity = Forbidden_in_core) xs
