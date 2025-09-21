SHELL := /bin/bash
FILE ?= /tmp/perf_smoke_big.tex
J ?= 8
OUT ?= /tmp/latencies_ms.txt
THREADS ?= 4
NREQ ?= 100000
HEDGE ?= 10
AB_ITERS ?= 100000
AB_WARMUP ?= 512
AB_CSV ?= /tmp/ab_microbench.csv
EDIT_ITERS ?= 5000

.PHONY: all build clean verify service-run service-stop gate ci soak proxy service verify_r1
.PHONY: edit-replay ab-compare
.PHONY: prom-smoke
.PHONY: perf-summary
.PHONY: gates-all
.PHONY: hash-bench
.PHONY: fmt
.PHONY: rest-run rest-stop rest-smoke
.PHONY: build-simd
.PHONY: simd-hash-avx2 simd-hash-neon

all: build

build:
	dune build @all -j $(J)

clean:
	dune clean

fmt:
	OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune fmt

service-run:
	@pkill -f main_service || true
	@rm -f /tmp/l0_lex_svc.sock
	@L0_PROM=1 L0_POOL_CORES=$${L0_POOL_CORES:-0,1,2,3} ./_build/default/latex-parse/src/main_service.exe &
	@sleep 0.3
	@echo "[run] workers = $${L0_POOL_CORES:-0,1,2,3}"
	@echo "[run] hedge   = $(HEDGE) ms"

service-stop:
	-pkill -f main_service || true
	@echo "[service] stopped"

# Quick verification: build, time selftest, IPC propcheck,
# SIMD guard self-check, A+B microbench (strict percentiles),
# run service, hammer it with 4×2500
verify: build service-run
	_build/default/latex-parse/bench/time_selftest.exe
	_build/default/latex-parse/bench/ipc_propcheck.exe
	_build/default/latex-parse/bench/ab_microbench.exe "$(FILE)" $(AB_ITERS) --warmup $(AB_WARMUP) --csv "$(AB_CSV)"
	_build/default/latex-parse/bench/edit_window_bench.exe corpora/perf/edit_window_4kb.tex $(EDIT_ITERS) --warmup 256 --csv /tmp/edit_window_bench.csv --window 4096
	@if [[ ! -f "$(FILE)" ]]; then echo "Set FILE=<path to perf_smoke_big.tex>"; exit 2; fi
	# keepalive bench exercises persistent server path  
	_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" 10000 $(THREADS) --out "$(OUT)"
	# legacy one-shot connection bench for comparison
	_build/default/latex-parse/bench/run_service_bench_concurrent.exe "$(FILE)" 4000 $(THREADS)
	@echo "[verify] tail CSV (slowest-100):"
	@tail -n 10 /tmp/l0_service_tail.csv || true
	@$(MAKE) service-stop

edit-replay:
	OPAMSWITCH=l0-testing opam exec -- \
	  ./_build/default/latex-parse/bench/edit_replay_bench.exe \
	  corpora/perf/edit_window_4kb.tex 2000 --window 4096 --csv /tmp/edit_replay_2k.csv

ab-compare:
	OPAMSWITCH=l0-testing opam exec -- bash scripts/ab_compare.sh corpora/perf/perf_smoke_big.tex 10000

prom-smoke:
	@echo "[prom] TCP"; bash scripts/prom_smoke.sh tcp || true
	@echo "[prom] UDS"; L0_PROM_UDS=/tmp/l0_prom.sock bash scripts/prom_smoke.sh uds || true

perf-summary:
	OPAMSWITCH=l0-testing opam exec -- bash scripts/perf_summary.sh corpora/perf/perf_smoke_big.tex /tmp/perf_summary.csv
	@echo "[summary] /tmp/perf_summary.csv"

gates-all:
	OPAMSWITCH=l0-testing opam exec -- bash scripts/run_all_gates.sh corpora/perf/perf_smoke_big.tex corpora/perf/edit_window_4kb.tex 100

hash-bench:
	@echo "[hash] FNV-1a and XXH-like scalar throughput"
	OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/bench/hash_throughput.exe
	OPAMSWITCH=l0-testing opam exec -- ./_build/default/latex-parse/bench/hash_throughput.exe \
	  corpora/perf/perf_smoke_big.tex 50 --csv /tmp/hash_throughput.csv
	@echo "[hash] CSV: /tmp/hash_throughput.csv"

hash-gate: hash-bench
	@ENABLE_HASH_GATE=${ENABLE_HASH_GATE:-0} THRESH_MBPS=${THRESH_MBPS:-500.0} \
	  ENABLE_HASH_GATE_XXH=${ENABLE_HASH_GATE_XXH:-0} THRESH_MBPS_XXH=${THRESH_MBPS_XXH:-1000.0} \
	  L0_USE_SIMD_XXH=${L0_USE_SIMD_XXH:-0} \
	  bash scripts/hash_gate.sh corpora/perf/perf_smoke_big.tex 50 /tmp/hash_throughput.csv

hash-bench-avx2:
	@echo "[hash] AVX2 lane (if available)"
	ENABLE_XXH_AVX2=-DENABLE_XXH_AVX2 OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/bench/hash_throughput.exe
	L0_USE_SIMD_XXH=1 \
	  OPAMSWITCH=l0-testing opam exec -- ./_build/default/latex-parse/bench/hash_throughput.exe \
	  corpora/perf/perf_smoke_big.tex 50 --csv /tmp/hash_throughput.csv || true
	@echo "[hash] CSV: /tmp/hash_throughput.csv"

hash-bench-neon:
	@echo "[hash] NEON lane (if available)"
	ENABLE_XXH_NEON=-DENABLE_XXH_NEON OPAMSWITCH=l0-testing opam exec -- dune build latex-parse/bench/hash_throughput.exe
	L0_USE_SIMD_XXH=1 \
	  OPAMSWITCH=l0-testing opam exec -- ./_build/default/latex-parse/bench/hash_throughput.exe \
	  corpora/perf/perf_smoke_big.tex 50 --csv /tmp/hash_throughput.csv || true
	@echo "[hash] CSV: /tmp/hash_throughput.csv"

gate: ; ./acceptance_gate.sh "$(OUT)" /tmp/l0_service_tail.csv

ci: build service-run
	@echo "[ci] 100k keepalive run"
	_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" $(NREQ) $(THREADS) --out "$(OUT)"
	@$(MAKE) gate OUT="$(OUT)"
	@$(MAKE) service-stop

soak: build service-run
	@echo "[soak] 1h keepalive soak (prints every 10k)"; \
	T_END=$$(( $$(date +%s) + 3600 )); \
	while [[ $$(date +%s) -lt $$T_END ]]; do \
	  ./_build/default/latex-parse/bench/run_service_bench_keepalive.exe "$(FILE)" 10000 $(THREADS) --out "$(OUT)"; \
	  ./verify_percentiles "$(OUT)" | sed -n '1,12p'; \
	done; \
	$(MAKE) service-stop

proxy:
	cargo build -p elderd_rust_proxy --release

service:
	dune build latex-parse/src/main_service.exe

verify_r1: service proxy
	# Start OCaml service (Unix socket)
	pkill -f main_service || true
	rm -f /tmp/l0_lex_svc.sock
	_build/default/latex-parse/src/main_service.exe &
	sleep 0.5
	# Start Tokio proxy (TCP 127.0.0.1:9123)
	./target/release/elderd_rust_proxy &
	# Run p95 perf-gate per v25_R1
	bash scripts/perf_gate.sh corpora/perf/perf_smoke_big.tex 100

rest-run: service
	@pkill -f rest_api_server || true
	OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build latex-parse/src/rest_api_server.exe
	OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- ./_build/default/latex-parse/src/rest_api_server.exe -p 8080 &
	@sleep 0.3
	@echo "[rest] http://127.0.0.1:8080/"

rest-stop:
	-pkill -f rest_api_server || true
	@echo "[rest] stopped"

rest-smoke: rest-run
	bash scripts/rest_smoke.sh || true
	$(MAKE) rest-stop
	$(MAKE) service-stop

build-simd:
	@bash scripts/build_simd.sh

simd-hash-avx2:
	OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build --profile=simd-avx2 @simd-hash

simd-hash-neon:
	OPAMSWITCH=${OPAMSWITCH:-l0-testing} opam exec -- dune build --profile=simd-neon @simd-hash
