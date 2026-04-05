# Appendix B — Layer Interfaces & Data Structures

Per v25 master plan §15, Table B (93 pages).

## L0 Lexer Interface

```ocaml
(* core/l0_lexer/catcode.ml *)
type catcode = int  (* 0–15, following TeX conventions *)
val classify_ascii : int -> int

(* latex-parse/src/validators_common.ml *)
type severity = Error | Warning | Info
type result = { id : string; severity : severity; message : string; count : int }
type rule = { id : string; run : string -> result option; languages : string list }
type layer = L0 | L1 | L2 | L3 | L4
```

### Key Functions

```ocaml
val strip_math_segments : string -> string
val count_substring : string -> string -> int
val contains_substring : string -> string -> bool  (* pure OCaml, no Str *)
val any_line_pred : string -> (string -> bool) -> int * int
val extract_env_blocks : string -> string -> string list
val extract_document_body : string -> string option
val extract_preamble : string -> string
val extract_usepackages : string -> (int * string) list
```

## L1 Expander Interface

```ocaml
(* core/l1_expander/expander.ml *)
val expand : catalogue -> string -> string
val expand_fix : config -> string -> string  (* iterative expansion to fixpoint *)
```

### Macro Catalogue

- 441 symbol macros (`macro_catalogue.v25r2.json`)
- 79 argsafe macros (`macro_catalogue.argsafe.v25r1.json`)
- Total: 520 production macros

## L2 Parser Interface

```ocaml
(* latex-parse/src/parser_l2.ml *)
type cmd = { name : string; opts : string list; args : string list }
type node = Word | Cmd | Group | Environment | MathInline | MathDisplay | Comment

type document = {
  preamble : node list;
  body : doc_element list;
  labels : (string * int) list;
  refs : (string * int) list;
}

val parse : string -> node list
val parse_with_envs : string -> node list
val extract_document : node list -> document
val parse_success : string -> bool
```

## Validator Engine Interface

```ocaml
(* latex-parse/src/validators.mli *)
val run_all : string -> result list
val run_all_for_language : string -> string option -> result list
val run_all_with_timings : string -> result list * float * (string * float) list
val run_all_with_timings_for_layer : string -> layer -> result list * float * (string * float) list
val precondition_of_rule_id : string -> layer
```

## Cross-Layer Sync Interface

```ocaml
(* latex-parse/src/layer_sync.mli *)
type version_vector = { gen : int; parent_gen : int }
type 'a snapshot = { generation : int; states : 'a layer_state list }

val accepts_delta : version_vector -> version_vector -> bool
val advance : version_vector -> version_vector
val is_consistent : 'a snapshot -> bool
val rollback_child : 'a snapshot -> layer_id -> 'a snapshot * rollback_result
```

## Validator DAG Interface

```ocaml
(* latex-parse/src/validator_dag.mli *)
type validator_meta = { id; phase; provides; requires; conflicts }
type dag = { nodes; edges; topo_order }

val build_dag : validator_meta list -> (dag, string) result
val detect_conflicts : validator_meta list -> conflict list
val resolve_conflict : validator_meta -> validator_meta -> int -> int -> string
```

## Log Parser Interface

```ocaml
(* latex-parse/src/log_parser.mli *)
type log_event = Overfull | Underfull | PageNumber | WidowPenalty | ...
type log_context = { events; overfull_lines; underfull_lines; pages; ... }

val parse_log : string -> log_context
val set_log_context : log_context -> unit
val get_log_context : unit -> log_context option
```
