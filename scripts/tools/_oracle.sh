# shellcheck shell=bash
# Sourced by the shell graders (false_ready_oracle.sh, diff_compile_check.sh).
# The ONE pdflatex oracle (ADR-012 decision 7) is the pinned TeX Live image;
# scripts/tools/_oracle.py is its only entry point, and this file is the shell
# side of it. After `oracle_setup TAG REQUIRE`:
#
#   PDFLATEX        array: the command to run INSTEAD of `pdflatex`
#   ORACLE_BACKEND  native | container
#   ORACLE_BANNER   the oracle's `pdflatex --version` first line
#   ORACLE_TIMEOUT_INSIDE  1 when the command enforces TEX_TIMEOUT itself
#                   (container: the timeout runs INSIDE the container, because
#                   killing the docker client on the host would leave pdflatex
#                   running in the container), so no outer `timeout` wrapper
#
# native     only when LP_ORACLE_IN_IMAGE is set (tex-oracle.yml sets it to the
#            image) AND `_oracle.py assert-native` verifies the TeX tree's
#            fingerprint; a mismatch is exit 2.
# container  otherwise; TMPDIR is exported to the oracle work root, and every
#            work directory must be made with an EXPLICIT template,
#            `mktemp -d "${TMPDIR:-/tmp}/lp-oracle.XXXXXX"`: macOS's BSD mktemp
#            ignored TMPDIR without one and returned /var/folders/..., which
#            the container cannot see (measured 2026-09-27: the shim refused
#            every run, loudly, which is how it was found).
# Neither    exit 2 if REQUIRE=1 or ANY host pdflatex is on PATH (a host
#            pdflatex is not the oracle, and skipping silently would hide that);
#            a clean SKIP (exit 0) only where there is no TeX at all.
oracle_setup() {
  local tag="$1" req="$2" py out
  py="$ROOT/scripts/tools/_oracle.py"
  if [ -n "${LP_ORACLE_IN_IMAGE:-}" ]; then
    if ! out="$(python3 "$py" assert-native 2>&1)"; then
      echo "[$tag] FATAL: $out" >&2; exit 2
    fi
    ORACLE_BACKEND=native
    PDFLATEX=(pdflatex)
    ORACLE_TIMEOUT_INSIDE=0
    ORACLE_BANNER="$(pdflatex --version 2>/dev/null | head -1)"
    return 0
  fi
  if command -v python3 >/dev/null 2>&1 && out="$(python3 "$py" version 2>&1)"; then
    ORACLE_BACKEND=container
    PDFLATEX=(python3 "$py" pdflatex --timeout "$TEX_TIMEOUT")
    ORACLE_TIMEOUT_INSIDE=1
    ORACLE_BANNER="$(printf '%s\n' "$out" | tail -1)"
    TMPDIR="$(python3 "$py" workroot)" || { echo "[$tag] FATAL: no oracle work root" >&2; exit 2; }
    mkdir -p "$TMPDIR" || exit 2
    export TMPDIR
    return 0
  fi
  if [ "$req" = 1 ] || command -v pdflatex >/dev/null 2>&1; then
    echo "[$tag] FATAL: the pinned-image oracle is unavailable: ${out:-python3 missing}" >&2
    echo "[$tag]   A host pdflatex is NOT the oracle (ADR-012 decision 7); start the" >&2
    echo "[$tag]   container (colima start; docker pull the TEX_IMAGE of tex-oracle.yml)." >&2
    exit 2
  fi
  echo "[$tag] SKIP: no TeX and no pinned-image oracle in this environment"
  exit 0
}
