# L3 Source-Regex → AST Migration Inventory (v27.1.20)

The missing **Stage 2** of `V27_L3_AST_PLAN`: a per-rule inventory of the 116 `L3_Semantics` rules by current extraction mechanism and migration difficulty. Result: **the migration is ~an order of magnitude smaller than the plan framing.**

## Landscape

The "migrate 116 L3 rules from source-regex to AST" framing is significantly inflated. The two surveys cover 76 of the 116 L3 rules; of those, 17 are already correctly semantic (PRJ-001..004 consume the resolved Project_state; 13 layout rules — LAY-001/002/003/004/006/009/011/017/018/021, MATH-026/027, CJK-007 — consume Log_parser/File_context build artifacts that an AST literally cannot reproduce). The remaining ~40 unsurveyed L3 rules are dominated by the 18 already-file-based validators_l3_file.ml producers (FIG/COL/PDF/TIKZ metadata), so roughly 34-35 of the 116 are ALREADY non-source-regex and need zero migration. Of the 60 surveyed source-regex rules, 39 are "defer" (BibTeX-text scans, preamble substring probes, byte-scanners) where regex is adequate or where an AST is the wrong tool, and 9 "hard" ones (CJK-003/009/011/013, RTL-001/002, LAY-019, LANG-010) explicitly want a line/script/layout context, NOT a LaTeX AST. That leaves only ~11 "easy" rules as genuine AST wins, and the sharp, high-value core is even smaller: 6 env/math-scoped rules (MATH-076/089/103/107, TAB-004, CHEM-010) plus REF-008/010 (which want semantic label/ref/bib tables, not env nodes). So the real AST/semantics workstream is ~6-11 rules, plus optionally upgrading the regex-fed semantic_state.ml that PRJ-003/004 already depend on — an order of magnitude smaller than "116."

## Migration mix (surveyed 76 of 116)

- **already_semantic**: 17
- **easy**: 11
- **hard**: 9
- **defer**: 39

## Proposed `ast_semantic_state.ml` scope

ast_semantic_state.ml should be the SINGLE-FILE, AST-derived model that semantic_state.ml currently fakes with Re_compat scans — project_state.ml stays as-is (the cross-file projector) and simply swaps its per-file source from Semantic_state.analyze to Ast_semantic_state.analyze, keeping global_labels/global_refs/cross_file_duplicates/cross_file_undefined merging unchanged. Do NOT duplicate project_state's cross-file tables, and do NOT synthesize layout facts (overfull/widow/font — those stay in Log_parser/Build_artifact_state).

Proposed types:
  type span = { start_off : int; end_off : int }
  type env_node = { name : string; body : span; args : string list; depth : int } (* comment/verbatim-aware, correctly nested *)
  type math_seg = { span : span; display : bool } (* wraps existing find_math_ranges; inline vs display *)
  type label_entry = { key : string; prefix : string; pos : int; def_env : string option (* figure/table/equation/section *) }
  type ref_entry = { key : string; command : string; pos : int }
  type cite_entry = { key : string; command : string; pos : int }
  type bib_entry = { key : string; etype : string; fields : (string * string) list } (* parsed @entry{key, field={..}} *)
  type package = { name : string; options : (string * string option) list }
  type preamble = { doc_class : string; class_opts : (string*string option) list; packages : package list; hypersetup : (string*string) list; pdfinfo : (string*string) list }
  type t = { src : string; envs : env_node list; math : math_seg list; labels : label_entry list; refs : ref_entry list; cites : cite_entry list; bib : bib_entry list; preamble : preamble }

Proposed functions:
  val analyze : string -> t                              (* single-file, replaces Semantic_state.analyze; must produce label/ref lists field-compatible with Semantic_state so project_state.build is a drop-in *)
  val envs_named : t -> string -> env_node list          (* MATH-076, TAB-004, CHEM-010 *)
  val math_segments : ?display:bool option -> t -> math_seg list  (* MATH-089/103, LANG-010 *)
  val labels_by_env : t -> string -> label_entry list    (* REF-010 float first-mention *)
  val lookup_bib : t -> string -> bib_entry option       (* REF-008 + (deferred) BIB-* *)
  val package_opt : t -> pkg:string -> key:string -> string option option (* PKG-018/019, LAY-022 *)

Notes: the BibTeX sub-model (bib_entry list) is orthogonal to the LaTeX AST — expose it here but implement as a separate parser module. Compatibility shim: keep Semantic_state.label_entry/ref_entry shapes so project_state.ml need not change its field accesses (l.key/l.position vs pos).

## Staged plan

### 0. Reframe + scope-lock — _0.5 day (doc/decision only)_

Record the honest tally (17 surveyed already-semantic + ~18 file-based = ~35/116 need nothing; 39 defer; 9 hard are NOT AST work). Declare non-goals in the module header: no layout/log facts, no byte/script segmentation, no cross-file tables (project_state owns those). Prevents the plan from ballooning back to 116.

### 1. AST env + math nodes — _3-5 days_

Build env_node extraction (comment/verbatim-aware, nesting-correct) and wrap the existing byte-accurate find_math_ranges into math_seg. This is the load-bearing new capability. Migrate the 6 clean wins: MATH-076/089/103/107, TAB-004, CHEM-010 off extract_env_blocks/extract_math_segments. Collapse MATH-089 and MATH-103 (identical impls) onto one shared helper.

### 2. Semantic label/ref upgrade + project_state swap — _3-4 days_

Add AST-derived label_entry (with def_env) and ref_entry; make analyze field-compatible with Semantic_state so project_state.build swaps in unchanged. Migrate REF-010 to use labels_by_env/first-mention instead of its duplicated regex extractor. This also de-duplicates semantic_state.ml's regex label scan that PRJ-003/004 silently rely on.

### 3. BibTeX sub-model (optional, gated) — _3-6 days (only if BIB-* re-prioritized; else skip)_

Standalone @entry parser producing bib_entry list; wire REF-008 to lookup_bib. Only pursue further if the 17 deferred BIB-* rules are prioritized — otherwise stop here; regex-over-@entry-text is adequate for them and this is a large parser for low marginal value.

### 4. Preamble/package table (low priority) — _2-3 days, defer-eligible_

Structured packages+options+hypersetup/pdfinfo table for PKG-018/019, LAY-022. Marginal benefit over substring probes; do last or defer indefinitely. Explicitly do NOT build this to serve the substring-adequate META/DOC/PKG-003/006 defers.

### OUT OF SCOPE (separate workstream, not ast_semantic_state) — _separate epic; not counted here_

CJK-003/009/011/013, RTL-001/002, LANG-010, LAY-019 need a per-line script-run/layout context (leading-token script class, codepoint ranges, line-break position). Track as a distinct 'text/layout context' module; do not fold into the AST migration or it will look 9 rules bigger than it is.

## Per-rule classification (surveyed)

| rule | current | migration |
|---|---|---|
| PRJ-001 | project_state | already_semantic |
| PRJ-002 | project_state | already_semantic |
| PRJ-003 | project_state | already_semantic |
| PRJ-004 | project_state | already_semantic |
| REF-010 | source_regex | easy |
| REF-008 | source_regex | easy |
| REF-012 | source_regex | hard |
| BIB-001 | source_regex | defer |
| BIB-002 | source_regex | defer |
| BIB-003 | source_regex | defer |
| BIB-004 | source_regex | defer |
| BIB-005 | source_regex | defer |
| BIB-006 | source_regex | defer |
| BIB-007 | source_regex | defer |
| BIB-008 | source_regex | defer |
| BIB-009 | source_regex | defer |
| BIB-010 | source_regex | defer |
| BIB-011 | source_regex | defer |
| BIB-012 | source_regex | defer |
| BIB-013 | source_regex | defer |
| BIB-014 | source_regex | defer |
| BIB-015 | source_regex | defer |
| BIB-016 | source_regex | defer |
| BIB-017 | source_regex | defer |
| META-001 | source_regex | defer |
| META-003 | source_regex | defer |
| META-004 | source_regex | defer |
| DOC-005 | source_regex | defer |
| TH-001 | source_regex | defer |
| LAY-001 | file_inspection | already_semantic |
| LAY-002 | file_inspection | already_semantic |
| LAY-003 | file_inspection | already_semantic |
| LAY-004 | file_inspection | already_semantic |
| LAY-005 | source_regex | defer |
| LAY-006 | file_inspection | already_semantic |
| LAY-007 | source_regex | defer |
| LAY-008 | source_regex | defer |
| LAY-009 | file_inspection | already_semantic |
| LAY-010 | source_regex | defer |
| LAY-011 | file_inspection | already_semantic |
| LAY-012 | source_regex | defer |
| LAY-013 | source_regex | defer |
| LAY-014 | source_regex | defer |
| LAY-015 | source_regex | defer |
| LAY-016 | source_regex | defer |
| LAY-017 | file_inspection | already_semantic |
| LAY-018 | file_inspection | already_semantic |
| LAY-019 | source_regex | hard |
| LAY-020 | source_regex | defer |
| LAY-021 | file_inspection | already_semantic |
| LAY-022 | source_regex | easy |
| MATH-026 | file_inspection | already_semantic |
| MATH-027 | file_inspection | already_semantic |
| MATH-076 | source_regex | easy |
| MATH-089 | source_regex | easy |
| MATH-103 | source_regex | easy |
| MATH-107 | source_regex | easy |
| TAB-004 | source_regex | easy |
| PKG-003 | source_regex | defer |
| PKG-006 | source_regex | defer |
| PKG-018 | source_regex | easy |
| PKG-019 | source_regex | easy |
| CJK-003 | source_regex | hard |
| CJK-005 | source_regex | defer |
| CJK-007 | file_inspection | already_semantic |
| CJK-009 | source_regex | hard |
| CJK-011 | source_regex | hard |
| CJK-012 | source_regex | defer |
| CJK-013 | source_regex | hard |
| CJK-016 | source_regex | defer |
| LANG-005 | source_regex | defer |
| LANG-009 | source_regex | defer |
| LANG-010 | source_regex | hard |
| RTL-001 | source_regex | hard |
| RTL-002 | source_regex | hard |
| CHEM-010 | source_regex | easy |
