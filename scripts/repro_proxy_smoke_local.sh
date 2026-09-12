#!/bin/bash
# OPEN-056 — DETERMINISTIC local reproduction of the rust-proxy-smoke failure.
#
#   bash scripts/repro_proxy_smoke_local.sh [worker_start_delay_ms]
#
# Builds nothing; expects
#   dune build latex-parse/src/main_service.exe
#   cargo build --manifest-path rust/Cargo.toml -p elderd_rust_proxy --release
#
# WHAT IT SHOWS. On origin/main this prints SMOKE_RC=0 and the log carries
# EXACTLY 2 `WARN ... attempt=1 status=1` lines, in 10 runs out of 10, with zero
# variance. The smoke retries up to 5x, which is the ONLY reason the job usually
# passes. So the "39 of 40 runs pass" figure measures the RETRY POLICY, not the
# defect: the underlying per-attempt failure rate is 2 of 3, every run.
#
# Timings, from proxy.stderr: a healthy request is 4.5-7.3 ms and the proxy's
# read timeout is 5 SECONDS (rust/l0_lexer_client/src/lib.rs:53). A failure is
# therefore a multi-second stall, not a tight-timeout artefact.
#
# The service RECEIVES the failing requests -- service.stderr shows
# `[svc] recv req_id=... len=9` for every one -- and then does not answer in
# time. `[svc] read_exact(hdr) exn: Failure("unexpected EOF")` afterwards is
# BENIGN: it is the proxy hanging up after its own timeout.

# $1 = worker start delay ms (0 = control)
cd /Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts
S=/tmp/claude-501/-Users-dylanpossamai-Library-CloudStorage-Dropbox-Work-Articles-Scripts/582b2e66-0d05-45f5-a112-44ed2994f25c/scratchpad
DELAY=${1:-0}
pkill -f main_service.exe 2>/dev/null; pkill -f elderd_rust_proxy 2>/dev/null; sleep 0.5
rm -f /tmp/l0_lex_svc.sock
env L0_ALLOW_SCALAR=1 L0_POOL_CORES=0,1 L0_MINOR_HEAP_MB=4 L0_NO_MLOCK=1 \
    L0_WORKER_START_DELAY_MS=$DELAY \
    ./_build/default/latex-parse/src/main_service.exe 1>$S/service.stdout 2>$S/service.stderr &
for i in $(seq 1 60); do [ -S /tmp/l0_lex_svc.sock ] && break; sleep 0.25; done
[ -S /tmp/l0_lex_svc.sock ] || { echo "SERVICE_NEVER_UP"; exit 2; }
./rust/target/release/elderd_rust_proxy 1>$S/proxy.stdout 2>$S/proxy.stderr &
for i in $(seq 1 60); do python3 -c "
import socket,sys
try: socket.create_connection(('127.0.0.1',9123),timeout=2.0).close()
except OSError: sys.exit(1)" 2>/dev/null && break; sleep 0.5; done
PYTHONUNBUFFERED=1 python3 scripts/proxy_smoke.py > $S/proxy_smoke.log 2>&1
rc=$?
pkill -f main_service.exe 2>/dev/null; pkill -f elderd_rust_proxy 2>/dev/null
echo "SMOKE_RC=$rc"
