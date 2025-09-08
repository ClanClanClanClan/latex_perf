SHELL := /bin/bash
FILE ?= /tmp/perf_smoke_big.tex
J ?= 8
AB_ITERS ?= 100000
AB_WARMUP ?= 512

.PHONY: all build clean verify service-run service-stop

all: build

build:
	dune build @all -j $(J)

clean:
	dune clean

# Launch the service (2 workers, hedge=10ms), kill any stale one, unlink socket
service-run:
	-pkill -f main_service || true
	-rm -f /tmp/l0_lex_svc.sock
	ulimit -n 65536; \
	_build/default/latex-parse/src/main_service.exe &
	@sleep 0.3
	@echo "[service] started on /tmp/l0_lex_svc.sock"

service-stop:
	-pkill -f main_service || true
	@echo "[service] stopped"

# Quick verification: build, time selftest, IPC propcheck,
# SIMD guard self-check, A+B microbench (strict percentiles),
# run service, hammer it with 4×2500
verify: build service-run
	_build/default/latex-parse/bench/time_selftest.exe
	_build/default/latex-parse/bench/ipc_propcheck.exe
	_build/default/latex-parse/bench/ab_microbench.exe "$(FILE)" $(AB_ITERS) $(AB_WARMUP)
	@if [[ ! -f "$(FILE)" ]]; then echo "Set FILE=<path to perf_smoke_big.tex>"; exit 2; fi
	_build/default/latex-parse/bench/run_service_bench_concurrent.exe "$(FILE)" 10000 4
	@echo "[verify] tail CSV (slowest-100):"
	@tail -n 10 /tmp/l0_service_tail.csv || true
	@$(MAKE) service-stop