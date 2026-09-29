# shellcheck shell=bash
# Sourced by the shell graders (false_ready_oracle.sh, diff_compile_check.sh).
# The ONE pdflatex oracle (ADR-012 decision 7) is the pinned TeX Live image;
# scripts/tools/_oracle.py is its only entry point, and this file is the shell
# side of it. After `oracle_setup TAG REQUIRE`:
#
#   PDFLATEX        array: the command to run INSTEAD of `pdflatex`; on BOTH
#                   backends the `_oracle.py pdflatex` shim, which imposes the
#                   ONE grading environment (ORACLE_TEX_VARS, private TEXMF*,
#                   no host TeX variable; C-91) and the graded ARGV allow-list
#                   (-interaction/-halt-on-error/... and one file; round 5),
#                   so no caller can differ
#   ORACLE_BACKEND  native | container
#   ORACLE_BANNER   the oracle's `pdflatex --version` first line
#   ORACLE_RM       array: the command that deletes work files pdflatex will
#                   write again (container: through `_oracle.py rm`, because a
#                   host-side delete leaves the container's view of the
#                   directory stale for about a second, and pdflatex then
#                   cannot create its log; see ContainerOracle.remove)
#   ORACLE_TIMEOUT_INSIDE  1: the shim enforces TEX_TIMEOUT itself
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
# oracle_vet DIR                  BEFORE a run: is DIR's free space above the
#                                  oracle's floor (_oracle.py MIN_FREE_MB)?
# oracle_vet DIR OUTFILE ARGS...   AFTER a run: the same, AND does OUTFILE (the
#                                  run's stdout) show pdfTeX failing to write
#                                  its OWN output (fwrite() failed, "I can't
#                                  write on file `<jobname>.<ext>'")?
# Exit 0 = gradeable; non-zero = NOT a grade. MEASURED 2026-09-27 (OPEN-118
# review round 3): with the work root full, pdfTeX prints its banner, fails on
# its own .log/.pdf and exits 1, which passed every proof-of-run check here.
# The Python side is the single definition of both checks; the container shim
# applies them too, this covers the native backend and is defence in depth.
# oracle_job FILE            pdfTeX's job name for FILE (doc.TEX -> doc, a.b.tex
#                            -> a.b): _oracle.pdftex_jobname, the ONE definition
#                            (a `${base%.tex}` strips a lowercase .tex only).
# oracle_pdf_written DIR FILE  0 iff pdfTeX itself wrote DIR/<job>.pdf, with
#                            pages, in the run whose log is DIR/<job>.log
#                            (_oracle.pdf_written): a file named .pdf is not
#                            evidence, a document can \openout one (C-97).
oracle_job() { python3 "$ROOT/scripts/tools/_oracle.py" job "$1"; }
oracle_pdf_written() { python3 "$ROOT/scripts/tools/_oracle.py" pdf-written "$1" "$2"; }

oracle_vet() {
  local d="$1"; shift
  if [ $# -eq 0 ]; then
    python3 "$ROOT/scripts/tools/_oracle.py" vet --dir "$d"
  else
    local f="$1"; shift
    python3 "$ROOT/scripts/tools/_oracle.py" vet --dir "$d" --output "$f" -- "$@"
  fi
}

oracle_setup() {
  local tag="$1" req="$2" py out
  py="$ROOT/scripts/tools/_oracle.py"
  if [ -n "${LP_ORACLE_IN_IMAGE:-}" ]; then
    if ! out="$(python3 "$py" assert-native 2>&1)"; then
      echo "[$tag] FATAL: $out" >&2; exit 2
    fi
    ORACLE_BACKEND=native
    # Through the shim on the native backend too (C-91): the shim, not the
    # caller, gives every graded run the protocol's environment (_oracle.py
    # graded_env: ORACLE_TEX_VARS, a private TEXMFHOME/TEXMFVAR/TEXMFCONFIG, no host TeX
    # variable), so CI grades exactly what a laptop grades. A bare `pdflatex`
    # here ran with the image's defaults: no openin_any/openout_any=p, no
    # SOURCE_DATE_EPOCH, the persistent TEXMFVAR. The shim enforces the
    # timeout (124) and maps an oracle failure to INFRA_RC (125).
    PDFLATEX=(python3 "$py" pdflatex --timeout "$TEX_TIMEOUT")
    ORACLE_RM=(rm -f --)
    ORACLE_TIMEOUT_INSIDE=1
    ORACLE_BANNER="$(python3 "$py" version 2>/dev/null | tail -1)"
    return 0
  fi
  if command -v python3 >/dev/null 2>&1 && out="$(python3 "$py" version 2>&1)"; then
    ORACLE_BACKEND=container
    PDFLATEX=(python3 "$py" pdflatex --timeout "$TEX_TIMEOUT")
    ORACLE_RM=(python3 "$py" rm)
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
