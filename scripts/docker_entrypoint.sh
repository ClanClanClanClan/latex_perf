#!/bin/sh
# Default entrypoint of the published image: the REST server.
#
# rest_api_server refuses to start (exit 1, "SIMD service not running") unless
# main_service is already listening on /tmp/l0_lex_svc.sock, so an image whose
# ENTRYPOINT was rest_api_server alone could never serve a request. This starts
# main_service, waits for its socket, then execs the REST server with the
# given arguments (default: -p 8080).
#
# The service settings default to rest-smoke.yml's (scalar mode allowed, a
# two-core worker pool, 4 MB minor heap, no mlock); override any of them by
# setting the variable. Like rest-smoke.yml, expect the FIRST request after
# start-up to be slow or to time out while the worker pool warms up.
set -eu
: "${L0_ALLOW_SCALAR:=1}"
: "${L0_NO_MLOCK:=1}"
: "${L0_POOL_CORES:=0,1}"
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
