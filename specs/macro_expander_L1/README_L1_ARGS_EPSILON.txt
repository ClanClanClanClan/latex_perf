
L1 Argumentful Macro Catalogue — epsilon profile
================================================

This folder contains a *stand-alone* catalogue of L1 macros that are
**argumentful**, **deterministic** and **epsilon-safe** (no side effects).

Created: 2025-08-12T18:32:59Z

Files
-----
- `macro_catalogue.argsafe.v25r1.json` — the catalogue (this is the one you check in)
- `macro_catalogue.argsafe.schema.json` — JSON Schema for structure sanity
- `load_catalogue_v3.ml` — OCaml loader (Yojson) + epsilon-safety checker
- `check_catalogue_v3.ml` — CLI that validates the catalogue

Build & Run (locally)
---------------------
```bash
opam install yojson        # if not already available
ocamlfind ocamlopt -linkpkg -package yojson load_catalogue_v3.ml -o /tmp/loader
ocamlfind ocamlopt -linkpkg -package yojson check_catalogue_v3.ml -o /tmp/check
/tmp/check macro_catalogue.argsafe.v25r1.json
```

Policy Snapshot (latex-epsilon)
-------------------------------
- Allowed: pure grouping `{...}`, NFSS shape/family/series switches
  (`\bfseries`, `\itshape`, `\sffamily`, `\ttfamily`, `\rmfamily`,
  `\mdseries`, `\scshape`, `\slshape`, `\upshape`, `\normalfont`),
  math font switches (`\mathrm`, `\mathbf`, ...).
- Builtins (handled in L1): `\verb`/`\verb*`, `\mbox`, `\textsuperscript`,
  `\textsubscript`, `\ensuremath`.
- Forbidden in inline templates: any token with I/O, file, write, catcode
  manipulation, assignments, measuring boxes/glue, or package-dependent effects.

Extending the Catalogue
-----------------------
Add entries to `macros` with:
```json
{
  "name": "textbf",
  "mode": "text",
  "category": "style",
  "epsilon_allowed": true,
  "args": { "positional": 1, "optional": [], "kinds": ["text"] },
  "template": { "kind": "inline", "body": "{\\bfseries $1}" }
}
```
Then run the checker (`/tmp/check ...`).

