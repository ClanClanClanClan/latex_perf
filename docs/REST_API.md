# REST API (L0 Lexer Façade)

This REST façade exposes a thin HTTP wrapper over the UDS service implemented by `latex-parse/src/main_service.ml`.

Base URL (local dev): `http://127.0.0.1:8080`

## POST /expand

Purpose
- Expand LaTeX using the lightweight expander and run validators in-process. This endpoint does NOT require the SIMD service and is ideal for validator smokes.

Request
- Content-Type: application/json
- Body:
  ```json
  { "latex": "\\\"LaTeX source\\\"" }
  ```

Response (200 OK)
- JSON schema (always present fields):
  ```json
  {
    "expanded": "...", 
    "validators": [
      { "id": "TYPO-001", "severity": "warning", "message": "...", "count": 2 },
      { "id": "TYPO-005", "severity": "warning", "message": "...", "count": 1 }
    ]
  }
  ```

- When `L0_DEBUG_L1=1` (or `true`/`on`), the response additionally includes token and expander summary fields useful for debugging rule alignment:
  ```json
  {
    "post_tokens": [
      { "kind": "word", "s": 0, "e": 4, "ch": null },
      { "kind": "command", "s": 5, "e": 8, "ch": null }
    ],
    "post_commands": ["textbf", "emph", "bfseries"],
    "post_summary": {
      "commands": [
        { "name": "textbf",  "s": 12, "e": 19 },
        { "name": "bfseries","s": 21, "e": 30 }
      ]
    }
  }
  ```

Notes
- `post_commands` is the list of command names observed in the expanded text (order preserved).  
- `post_summary.commands` provides per‑command spans in byte indices over the expanded source and is used by L1 rules (e.g., modernization and incomplete‑expansion checks).

Feature flag
- Set `L0_VALIDATORS=pilot` (or `1`/`true`/`PILOT`) before starting REST to enable the pilot L0 rules. Without the flag, only a minimal baseline set runs.

Build note
- If your existing `_build` artifacts predate the addition of `/expand`, run `make rest-run` to rebuild the REST binary before testing this endpoint.

## POST /tokens (debug)

Purpose
- Returns a token snapshot of the input using the lightweight tokenizer (for debugging spacing/adjacency rules).
- Disabled by default; returns 403 unless `L0_DEBUG_TOKENS=1` (or `true`/`on`) is set in the environment.

Request
- Content-Type: application/json
- Body:
  ```json
  { "latex": "A -- \\bf test..." }
  ```

Response (200 OK when enabled)
- JSON schema:
  ```json
  {
    "count": 7,
    "tokens": [
      { "kind": "word", "s": 0, "e": 1, "ch": null },
      { "kind": "space", "s": 1, "e": 2, "ch": null },
      { "kind": "symbol", "s": 2, "e": 3, "ch": "-" }
    ]
  }
  ```
Notes
- Token kinds: `word|space|newline|command|bracket_open|bracket_close|quote|symbol`
- Indices `s` (start) and `e` (end, exclusive) are byte indices in the source string.

## POST /tokenize

Request
- Content-Type: application/json
- Body:
  ```json
  { "latex": "\\\"LaTeX source\\\"" }
  ```

Response (200 OK on success, 503 on error)
- JSON schema (success):
  ```json
  {
    "ok": true,
    "status": 0,
    "origin": "primary",
    "metrics": {
      "n_tokens": 123,
      "issues_len": 0,
      "request_bytes": 1100
    },
    "validators": {
      "applied": 0,
      "errors": 0
    },
    "service": {
      "name": "l0-lex",
      "version": "v25",
      "ts": 1690000000
    }
  }
  ```
- JSON schema (error):
  ```json
  { "error": "message", "code": 503 }
  ```

Notes
- `origin` comes from the service’s hedged broker (primary|hedge).
- `status=0` indicates success; non-zero statuses return HTTP 503.
- `validators.results` is a flattened array of summaries `{id,severity,message,count}` produced by `Validators.run_all`.

### Optional Validator Timing Fields

To include aggregate and per‑rule timing information in the `.validators` object, enable the flags below before starting the REST server:

- `L0_INCLUDE_VALIDATORS_DURATION=1` — Adds `.validators.duration_ms` (float, total runtime of all validators for the request).
- `L0_INCLUDE_VALIDATORS_TIMINGS=1` — Adds `.validators.timings` (array), where each element is `{ "id": string, "duration_ms": float }` for the corresponding rule in execution order.

Example (truncated):

```json
{
  "validators": {
    "applied": 6,
    "errors": 2,
    "duration_ms": 0.41,
    "timings": [
      { "id": "TYPO-001", "duration_ms": 0.02 },
      { "id": "TYPO-002", "duration_ms": 0.01 }
    ],
    "results": [ { "id": "TYPO-001", "severity": "error", "message": "...", "count": 2 } ]
  }
}
```

## GET /ready

Purpose
- Cheap readiness probe (socket only). Returns immediately if the UDS socket is available.

Response
```json
{ "ready": true }
```
- On failure: `{ "error": "service not ready", "code": 503 }`

## GET /health

Purpose
- Liveness + processing: performs a minimal internal request through the service and decodes the typed status payload.

Response
- Success:
  ```json
  { "status": "healthy", "n_tokens": 1 }
  ```
- Failure:
  ```json
  { "error": "...", "code": 503 }
  ```

## Protocol (internal)

The REST server speaks to the service over Unix domain socket with a 16‑byte big‑endian header:
- Request: type(4) | req_id(8) | len(4) + payload
- Response: type(4) | req_id(8) | len(4) + 13‑byte status payload

Status payload (13 bytes):
- `status` (u32 BE), `n_tokens` (u32 BE), `issues_len` (u32 BE), `origin` (u8)
- `origin`: 1=primary, 2=hedge, else unknown
