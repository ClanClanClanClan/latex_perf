#!/usr/bin/env bash
set -euo pipefail

want_switch="l0-testing"
want_ocaml="5.1.1"
want_coq_prefix="8.18"
want_dune_min="3.10"

fail=false

echo "[check] opam switch"
sw=$(opam switch show 2>/dev/null || echo "(none)")
echo "  current: $sw"
if [[ "$sw" != "$want_switch" ]]; then
  echo "  -> expected switch '$want_switch'"; fail=true
fi

echo "[check] ocamlc -version"
ocv=$(ocamlc -version 2>/dev/null || echo "(missing)")
echo "  current: $ocv"
if [[ "$ocv" != "$want_ocaml" ]]; then
  echo "  -> expected OCaml $want_ocaml"; fail=true
fi

echo "[check] coqc -v"
cv=$(coqc -v 2>/dev/null | sed -n '1p' || true)
echo "  first line: $cv"
if ! echo "$cv" | grep -q "$want_coq_prefix"; then
  echo "  -> expected Coq $want_coq_prefix.x"; fail=true
fi

echo "[check] dune --version"
dv=$(dune --version 2>/dev/null || echo "(missing)")
echo "  current: $dv"
# naive compare: accept same major.minor or higher
if [[ "$dv" != "$want_dune_min"* && "$dv" != 3.* && "$dv" != 4.* ]]; then
  echo "  -> expected dune >= $want_dune_min"; fail=true
fi

if $fail; then
  cat <<MSG
[check] Environment mismatch. Remediation:
  1) Run: ./scripts/setup_env.sh
  2) Or manually:
     - opam switch create $want_switch $want_ocaml
     - opam repo add coq-released https://coq.inria.fr/opam/released
     - opam update -y
     - opam install -y coq.8.18.0 coq-core.8.18.0 dune.3.10 yojson angstrom ppx_deriving uutf
     - eval "\$(opam env --switch=$want_switch)"
MSG
  exit 2
else
  echo "[check] OK: environment matches baseline"
fi

