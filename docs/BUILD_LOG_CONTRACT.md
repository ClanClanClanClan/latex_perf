# Build Log Contract

Formal contract for the compile-log integration subsystem (WS1).

---

## Parsed Event Types

The `Log_parser.parse_log` function extracts structured events from LaTeX
`.log` files. Supported event types:

| Event | Pattern matched | Fields |
|-------|----------------|--------|
| `Overfull` | `Overfull \hbox (Npt too wide) in paragraph at lines M--N` | `box`, `amount_pt`, `line_start`, `line_end` |
| `Underfull` | `Underfull \hbox (badness N) in paragraph at lines M` | `box`, `badness`, `line_start` |
| `PageNumber` | `[N]` | page number |
| `WidowPenalty` | `Widow penalty` | `page` |
| `ClubPenalty` | `Club penalty` | `page` |
| `FloatWarning` | `LaTeX Warning: Float too large...input line N` | `message`, `line` |
| `LatexWarning` | `LaTeX Warning: ...on input line N` | `message`, `line` |
| `RerunNeeded` | `LaTeX Warning: ... Rerun to get cross-references right` (v26.1) | (none; presence-only) |
| `CitationUndefined` | `LaTeX Warning: Citation 'key' on page N undefined` (v26.1) | `key`, `page` |
| `FontSubstitution` | `LaTeX Font Warning: Font shape ... not available` (v26.1) | `message` |

Additionally, TikZ compile times are extracted via `Compile time...: Ns`.

## Derived Facts (log_context)

From raw events, the parser computes aggregate facts:

| Fact | Type | Derived from |
|------|------|-------------|
| `overfull_lines` | `(int * int) list` | All `Overfull Hbox` events |
| `underfull_lines` | `int list` | All `Underfull` events with `line_start > 0` |
| `pages` | `int list` | All `PageNumber` events |
| `max_overfull_pt` | `float` | Maximum `amount_pt` across all `Overfull` events |
| `has_widows` | `bool` | Any `WidowPenalty` event present |
| `has_orphans` | `bool` | Any `ClubPenalty` event present |
| `tikz_compile_times` | `float list` | All TikZ compile time values |

## Consuming Rules (Class C)

17 rules depend on `Log_parser.get_log_context()`. They are in `rules_class_c`
and execute only via `run_class_c` / `run_with_build` / `run_with_policy`:

| Rule | Fact consumed | Condition |
|------|--------------|-----------|
| LAY-001 | `overfull_lines`, `max_overfull_pt` | `max_overfull_pt > 2.0` |
| LAY-002 | `has_widows`, `has_orphans` | Either true |
| LAY-003 | `overfull_lines` + source text | Overfull near `\section` |
| LAY-004 | `max_overfull_pt` | `> 10.0` |
| LAY-006 | `events` | Any `FloatWarning` |
| LAY-009 | `events` | Any `Underfull Vbox` |
| LAY-011 | `events` | `FloatWarning` with "too large" |
| LAY-017 | `has_widows` | True |
| LAY-018 | `events` | Any `Underfull Vbox` |
| LAY-021 | `events` | Any `Overfull Vbox` |
| MATH-026 | `max_overfull_pt` | `> 0.0` |
| MATH-027 | `max_overfull_pt` | `> 5.0` |
| FIG-020 | `max_overfull_pt` | `> 0.0` |
| TIKZ-002 | `tikz_compile_times` | Any time `> 5.0` |
| LAY-025 | `events` | Any `RerunNeeded` |
| LAY-026 | `events` | Any `CitationUndefined` |
| LAY-027 | `events` | Any `FontSubstitution` |

The three v26.1 rules (LAY-025/026/027) carry `formal_conditional` proofs
in `proofs/BuildLog.v` — sound given a compile-log-predicate contract.

## Staleness Policy

`Build_profile.is_stale` returns `true` when the `.log` file's `mtime` is
older than the `.tex` file's `mtime`. Stale logs are still used (the data is
better than nothing) but the staleness can be reported to the user.

## Engine Detection

`Build_profile.detect_engine` examines the first 200 bytes of the log file:

| Engine | Pattern | Result |
|--------|---------|--------|
| pdfTeX | `pdfTeX` in header | `PDFLaTeX` |
| XeTeX | `XeTeX` in header | `XeLaTeX` |
| LuaTeX | `LuaTeX` in header | `LuaLaTeX` |
| Other | No match | `Unknown` |

## Thread-Safety Model

Log context is stored per-thread via `Hashtbl` keyed by `Thread.id (Thread.self ())`.
This is safe for OCaml 4.x threads (each thread has a unique ID). For OCaml 5
domains, `Thread.id` returns 0 for all domains — this is a known limitation
shared with `File_context`, `Validators_context`, `User_macro_context`,
`Build_artifact_state`, `Project_context`, and `Semantic_state`.

The lifecycle is: `set` before validation, `clear` after. The `Build_profile.activate`
/ `deactivate` functions wrap `Log_parser.set_log_context` / `clear_log_context`.

## Formal Guarantee

`proofs/BuildLog.v` proves monotonicity: appending events to a log only
increases derived fact counts (`count_overfull_app`, `count_underfull_app`)
and preserves existing boolean signals (`has_event_preserved`). Zero admits.
