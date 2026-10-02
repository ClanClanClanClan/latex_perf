#!/bin/sh
# Default entrypoint of the published image: the REST server.
#
# rest_api_server refuses to start (exit 1, "SIMD service not running") unless
# main_service is already listening on /tmp/l0_lex_svc.sock, so an image whose
# ENTRYPOINT was rest_api_server alone could never serve a request. This starts
# main_service, waits for its socket, then execs the REST server with the
# given arguments (default: -p 8080).
#
# Service settings: scalar mode allowed, 4 MB minor heap, no mlock (as in
# rest-smoke.yml), and a ONE-worker pool. Override any of them by setting the
# variable.
#
# ⚠ ONE worker, not rest-smoke.yml's two, because of a MEASURED defect
# (linux/arm64 under colima, 2026-10-01): inside a container a two-worker pool
# (L0_POOL_CORES=0,1) leaves requests unanswered. Six identical POST /tokenize
# requests: 2 got no response within 20 s, 4 answered at once; six direct UDS
# requests to main_service: 3 timed out at 15 s. With L0_POOL_CORES=0: 6 of 6
# answered at once, both ways. The cause (the broker with two workers in a
# container) is not diagnosed; until it is, the image runs the configuration
# measured to work, and docker_smoke.sh's 5-in-a-row check guards it.
set -eu
: "${L0_ALLOW_SCALAR:=1}"
: "${L0_NO_MLOCK:=1}"
: "${L0_POOL_CORES:=0}"
: "${L0_MINOR_HEAP_MB:=4}"
export L0_ALLOW_SCALAR L0_NO_MLOCK L0_POOL_CORES L0_MINOR_HEAP_MB
rm -f /tmp/l0_lex_svc.sock
main_service &
i=0
while [ ! -S /tmp/l0_lex_svc.sock ]; do
  i=$((i + 1))
  if [ "$i" -gt 60 ]; then
    echo "lp-serve: main_service socket never appeared" >&2
    exit 1
  fi
  sleep 0.5
done
exec rest_api_server "$@"
