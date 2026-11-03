#!/usr/bin/env bash
# readme_docker_smoke.sh [IMAGE] — run the README's Docker quick-start command
# EXACTLY as documented, and assert that it lints the file.
#
# Why this exists (C-175): README.md's quick-start was
#   docker run --rm -v $(pwd):/data ghcr.io/.../latex_perf:latest /data/paper.tex
# The image's ENTRYPOINT is lp-serve (the REST server), so that command started
# the server, ignored /data/paper.tex and never exited; nothing ever ran it.
#
# What it does:
#   1. extracts the `docker run` line(s) from the fenced block under README.md's
#      "### Docker" heading — exactly one is required (zero means the
#      extraction is stale, which is a FAIL, not a vacuous PASS);
#   2. if IMAGE is given, replaces the documented image reference with IMAGE
#      (docker_smoke.sh passes the freshly built image); with no IMAGE the
#      documented image is run unchanged;
#   3. evaluates the line in a fresh directory holding paper.tex (a copy of
#      docker_smoke/article.tex), so `$(pwd)` and /data/paper.tex resolve as a
#      reader's would;
#   4. asserts: it exits within DEADLINE seconds, rc 0, >=1 finding row, a
#      TYPO-005 row, and no REST-server or fatal output.
# The only change to the documented argv is a `--label` (to find and remove
# the container if it hangs) and, if DOCKER_SMOKE_PLATFORM is set, a
# `--platform`. Neither changes what the container runs.
#
# Env: DOCKER_SMOKE_TMP  parent dir for the work dir. Default: mktemp's on
#                        Linux; on macOS a dir under $HOME, because colima /
#                        Docker Desktop share $HOME with the VM but not
#                        mktemp's /var/folders (the mount would be empty).
#      DOCKER_SMOKE_PLATFORM  e.g. linux/amd64
#      README_DOCKER_DEADLINE seconds (default 180)
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
README="${HERE}/../../README.md"
DOC_IMAGE='ghcr.io/clanclanclanclan/latex_perf:latest'
IMAGE="${1:-${DOC_IMAGE}}"
DEADLINE="${README_DOCKER_DEADLINE:-180}"
LABEL="lp-readme-smoke=$$"

if [ -z "${DOCKER_SMOKE_TMP:-}" ] && [ "$(uname -s)" = Darwin ]; then
  DOCKER_SMOKE_TMP="${HOME}/.cache"
  mkdir -p "${DOCKER_SMOKE_TMP}"
fi
if [ -n "${DOCKER_SMOKE_TMP:-}" ]; then
  WORK="$(mktemp -d "${DOCKER_SMOKE_TMP%/}/lp-readme-smoke.XXXXXX")"
else
  WORK="$(mktemp -d)"
fi
cleanup() {
  # A container whose `docker run` client was killed can still be starting;
  # look for it for a few seconds, not once.
  local ids _
  for _ in 1 2 3 4 5; do
    ids="$(command docker ps -aq --filter "label=${LABEL}" 2>/dev/null)"
    [ -n "${ids}" ] && command docker rm -f ${ids} > /dev/null 2>&1
    sleep 1
  done
  rm -rf "${WORK}"
}
trap cleanup EXIT

die() { echo "README DOCKER SMOKE FAIL: $*"; [ -f "${WORK}/run.out" ] && { echo "---- output ----"; cat "${WORK}/run.out"; echo "----------------"; }; exit 1; }

# 1. Extract the docker run line(s) from the "### Docker" section's code block.
[ -f "${README}" ] || die "README not found at ${README}"
awk '
  /^### Docker[[:space:]]*$/ { insec = 1; next }
  insec && !inblk && /^##?#? / { insec = 0 }
  insec && /^```/            { inblk = !inblk; next }
  insec && inblk && /^docker run / { print }
' "${README}" > "${WORK}/cmds"
N="$(wc -l < "${WORK}/cmds" | tr -d ' ')"
echo "README docker run lines found under '### Docker': ${N}"
[ "${N}" -eq 1 ] || die "expected exactly 1 'docker run' line in README.md's ### Docker block, found ${N} (extraction stale or README changed shape)"
CMD="$(cat "${WORK}/cmds")"
echo "documented: ${CMD}"

# 2. Substitute the image under test.
case "${CMD}" in
  *"${DOC_IMAGE}"*) ;;
  *) die "documented command does not reference ${DOC_IMAGE}" ;;
esac
CMD="${CMD//"${DOC_IMAGE}"/${IMAGE}}"
echo "running:    ${CMD}"

PLATFORM_ARGS=()
[ -n "${DOCKER_SMOKE_PLATFORM:-}" ] && PLATFORM_ARGS=(--platform "${DOCKER_SMOKE_PLATFORM}")
PLATFORM_PULL="${DOCKER_SMOKE_PLATFORM:+--platform ${DOCKER_SMOKE_PLATFORM}}"

# 3. Make the image local FIRST (the README's own `docker pull` step), so the
#    deadline times the run, not a download: a deadline that fired mid-pull
#    would kill the client before the container existed, and the container
#    would start after the cleanup had looked for it.
if ! command docker image inspect "${IMAGE}" > /dev/null 2>&1; then
  command docker pull ${PLATFORM_PULL:-} "${IMAGE}" > "${WORK}/pull.out" 2>&1 \
    || die "docker pull ${IMAGE} failed: $(tail -3 "${WORK}/pull.out")"
fi

# 4. Run it from a reader's directory holding paper.tex.
cp "${HERE}/docker_smoke/article.tex" "${WORK}/paper.tex"
docker() {  # add only a label (+ optional platform) to `docker run`
  if [ "${1:-}" = run ]; then
    shift
    command docker run --label "${LABEL}" "${PLATFORM_ARGS[@]}" "$@"
  else
    command docker "$@"
  fi
}
( cd "${WORK}" && eval "${CMD}" ) > "${WORK}/run.out" 2>&1 &
PID=$!
waited=0
while kill -0 "${PID}" 2> /dev/null; do
  if [ "${waited}" -ge "${DEADLINE}" ]; then
    kill "${PID}" 2> /dev/null
    die "the documented command did not exit within ${DEADLINE}s (it is probably serving REST instead of linting)"
  fi
  sleep 1; waited=$((waited + 1))
done
wait "${PID}"; RC=$?
echo "exit code ${RC} after ~${waited}s"

# 5. Assertions: exit code AND content.
[ "${RC}" -eq 0 ] || die "exit code ${RC}, expected 0"
ROWS="$(grep -cE $'^[A-Z]+-[0-9]+\t(error|warning|info)\t' "${WORK}/run.out")"
echo "finding rows: ${ROWS}"
[ "${ROWS}" -ge 1 ] || die "no finding rows"
grep -qE $'^TYPO-005\t' "${WORK}/run.out" || die "no TYPO-005 row"
! grep -qE 'REST API Server|listening|Fatal error|Rule_contracts_missing' "${WORK}/run.out" \
  || die "REST-server or fatal output"
echo "README DOCKER SMOKE: passed for ${IMAGE}"
