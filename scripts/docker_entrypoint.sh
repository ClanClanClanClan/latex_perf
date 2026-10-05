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
# (linux/arm64 under colima, 2026-10-01): a two-worker pool (L0_POOL_CORES=0,1)
# left requests unanswered (6 POST /tokenize: 2 got no response in 20 s; 6
# direct UDS requests: 3 timed out at 15 s; L0_POOL_CORES=0: 6 of 6).
# DIAGNOSED AND FIXED 2026-10-02 (OPEN-125, C-122..C-124): it was not the
# container. Forked workers inherited the parent's end of earlier workers'
# sockets, so retiring a worker hung the request that retired it, and a units
# bug retired a worker after EVERY request; the same drop reproduced natively
# on macOS (7 of 12 answered) and is the rust-proxy-smoke failure of OPEN-056.
# docker_smoke.sh now checks a two-worker pool too (10 in a row + 4x5
# concurrent). The default stays at one worker until a two-worker image has
# been measured on linux/arm64 (the platform of the original measurement):
# that run could not be made on 2026-10-02 (colima's docker disk was 99% full).
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
