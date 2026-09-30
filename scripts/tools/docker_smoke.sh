#!/usr/bin/env bash
# docker_smoke.sh IMAGE — assert that a built LaTeX Perfectionist image RUNS.
#
# Why this exists: the published ghcr.io/.../latex_perf:v27.1.63 image shipped
# a validators_cli that exits 2 (Rule_contracts_missing) on EVERY input,
# because the Dockerfile never copied specs/rules/rule_contracts.json. Nothing
# ran the image before it was pushed. docker-push.yml now runs this script
# between the build and the push; a non-zero exit blocks the push.
#
# Each check pins an exit code AND a content property, so neither a crash
# (rc 2) nor a silently degraded run (rc 0, empty output) passes:
#   1. lint a small real article        -> rc 0, >=1 finding row, TYPO-005 row
#   2. --compile-check the same article -> rc 0, a READY row
#   3. --compile-check a failing doc    -> rc 1, NOT-READY + the T2 reason
#   4. --explain TYPO-005               -> rc 0, catalogue message (rules_v3.yaml)
#                                          and the curated remediation
#                                          (rule_remediation.yaml), not the
#                                          generic fallback
#   5. rest_api_server start-up         -> loads the macro catalogue
#
# Usage: scripts/tools/docker_smoke.sh ghcr.io/clanclanclanclan/latex_perf:vX
#        (DOCKER_SMOKE_PLATFORM=linux/amd64 to run an amd64 image elsewhere)
set -u

IMAGE="${1:?usage: docker_smoke.sh IMAGE}"
HERE="$(cd "$(dirname "$0")" && pwd)"
FIX="${HERE}/docker_smoke"
PLATFORM_ARGS=()
if [ -n "${DOCKER_SMOKE_PLATFORM:-}" ]; then
  PLATFORM_ARGS=(--platform "${DOCKER_SMOKE_PLATFORM}")
fi
OUT="$(mktemp -d)"
trap 'rm -rf "${OUT}"' EXIT
FAILS=0

# run NAME ENTRYPOINT ARGS... : stdout+stderr -> $OUT/NAME.out, rc -> $OUT/NAME.rc
run() {
  local name="$1" entry="$2"; shift 2
  docker run --rm "${PLATFORM_ARGS[@]}" --network none \
    -v "${FIX}:/work:ro" -w /work --entrypoint "${entry}" \
    "${IMAGE}" "$@" > "${OUT}/${name}.out" 2>&1
  echo $? > "${OUT}/${name}.rc"
}

fail() { echo "SMOKE FAIL [$1]: $2"; echo "---- output ----"; cat "${OUT}/$1.out"; echo "----------------"; FAILS=$((FAILS + 1)); }
rc_is() { [ "$(cat "${OUT}/$1.rc")" = "$2" ] || { fail "$1" "exit code $(cat "${OUT}/$1.rc"), expected $2"; return 1; }; }
has() { grep -qE -- "$2" "${OUT}/$1.out" || { fail "$1" "no line matching /$2/"; return 1; }; }
lacks() { ! grep -qE -- "$2" "${OUT}/$1.out" || { fail "$1" "unexpected line matching /$2/"; return 1; }; }

# 1. lint
run lint validators_cli article.tex
rc_is lint 0 && has lint $'^[A-Z]+-[0-9]+\t(error|warning|info)\t' \
  && has lint $'^TYPO-005\t' && lacks lint 'Fatal error|Rule_contracts_missing'

# 2. compile-check, compiling document
run ready validators_cli --compile-check article.tex
rc_is ready 0 && has ready $'^READY\t' && lacks ready 'NOT-READY'

# 3. compile-check, failing document
run notready validators_cli --compile-check missing_input.tex
rc_is notready 1 && has notready $'^NOT-READY\t' \
  && has notready 'T2 project not closed: missing file'

# 4. explain: catalogue + remediation data present
run explain validators_cli --explain TYPO-005
rc_is explain 0 && has explain 'message: +Ellipsis' \
  && has explain 'remediation: ' \
  && lacks explain 'remediation: +No auto-fix is available'

# 5. REST server start-up loads the macro catalogue (then is stopped)
run rest sh -c 'timeout 5 rest_api_server -p 8080; exit 0'
has rest 'Loaded macro catalogue: [1-9][0-9]* symbols'

for n in lint ready notready explain rest; do
  echo "smoke ${n}: rc=$(cat "${OUT}/${n}.rc") lines=$(wc -l < "${OUT}/${n}.out" | tr -d ' ')"
done
if [ "${FAILS}" -ne 0 ]; then
  echo "DOCKER SMOKE: ${FAILS} check(s) FAILED for ${IMAGE}"
  exit 1
fi
echo "DOCKER SMOKE: all checks passed for ${IMAGE}"
