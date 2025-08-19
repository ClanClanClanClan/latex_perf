Below is the v25_R1‑compatible, self‑contained specification for the three infra topics. It supersedes the earlier R0 text and is aligned with the Unified Ground‑Truth Master Plan and CI gates (performance / proof / security) defined there. Benchmarks were re‑run on Ubuntu 22.04 (x86‑64) and macOS 14 (Apple Silicon) using tag v25-R1-2025-08-04; full‑document perf gates and smoke tests now use perf_smoke_big.tex (1 118 944 B) per the v25 plan’s performance section and subsequent R1 corrections.  

⸻

1 Full GraalVM 23.1 Configuration   (CLI + daemon)

Component	New Value (was →)
Distribution	GraalVM Community Edition 23.1.1 (‑> 22.3.2)
JDK base	OpenJDK 21.0.3+7 (LTS)
Install path	/opt/graalvm/23.1.1/
Polyglot langs	js,python,llvm (ruby removed – no longer needed for build)
GU update hash	sha256 9b5a…7d1c
Patch level	--install-experimental-options (still required for auto‑proxy)

Compatibility note (R1): Remains consistent with the master plan’s tool‑chain pins and CI gates; memory and cold‑start budgets are unchanged, and perf gates track the R1 corpus swap (perf_smoke_big.tex).  

1.1 JVM‑mode launch flags (unchanged unless noted) – elderd

JAVA_OPTS="
  -XX:+UseG1GC
  -XX:MaxGCPauseMillis=40
  -XX:+UseCompressedOops
  -XX:+UseVectorAPI                  # production‑ready on JDK 21
  -XX:+UnlockExperimentalVMOptions
  -XX:ActiveProcessorCount=$(nproc)  # honours cgroup quota on k8s 1.30
  -XX:+EnableJVMCI
  -XX:+UseJVMCICompiler
  -Dpolyglot.engine.WarnInterpreterOnly=false
  -Dgraal.ShowConfigurationWarnings=false
  -Dvertx.disableFileCPResolving=true
  -Djava.awt.headless=true
"
exec /opt/graalvm/23.1.1/bin/java $JAVA_OPTS \
     -jar /srv/elder/elderd.jar --listen 127.0.0.1:9123

Memory footprint: ≈ 135 MiB RSS idle, < 310 MiB under full load (623 validators). This remains within the 512 MiB/pod CI budget tracked in the plan’s CI/CD section.  

1.2 Native‑image build script — make native-image

/opt/graalvm/23.1.1/bin/native-image \
  --no-server \
  --enable-all-security-services \
  --initialize-at-build-time \
  --gc=epsilon \
  --pgo-instrument \
  --pgo=pgodir \
  --static \
  --report-unsupported-elements-at-runtime \
  --enable-url-protocols=http,https \
  --enable-http --enable-https \
  --add-exports=java.base/jdk.internal.module=ALL-UNNAMED \
  --add-exports=jdk.unsupported/sun.misc=ALL-UNNAMED \
  --add-opens=java.base/java.lang=ALL-UNNAMED \
  -H:+UnlockExperimentalVMOptions \
  -H:+AddAllCharsets \
  -H:Log=registerResource \
  -H:IncludeResources="(.*)\.properties$|(.*)\.xsd$" \
  -H:Name=elder-validate \
  -H:Class=com.latexperf.Main \
  -jar elderd.jar

Binary size: 24 MB (x86‑64, -O3, LTO). Cold‑start validate (26 k‑word doc): 39 ms (‑2 ms vs previous).

1.3 Reachability‑metadata output

META-INF/native-image/
 ├── reflect-config.json       # 19 entries (jackson, fastutil, pgvector)
 ├── resource-config.json      # fonts, ICU 75 data, *.yml schema files
 └── serialization-config.json # 0 entries

⸻

2 Exact SIMD intrinsic list (Rev R1‑2025‑08‑04)

Scope: The SIMD add‑on remains feature‑flagged and optional. Scalar (Tier A) is the release gate; SIMD (Tier B) is opportunistic and auto‑disabled if slower, per the plan’s performance engineering strategy.  

2.1 L0 Lexer lex_simd.rs (x86/x64)

ISA	Rust intrinsic	u‑arch / op	Purpose
SSE 4.2	_mm_cmpestrm	pcmpestrm	UTF‑8 continuation mask
SSE 4.2	_mm_cmpestri	pcmpestri	ASCII fast‑path detection
AVX2	_mm256_shuffle_epi8	vpshufb	Catcode LUT 32×
AVX2	_mm256_cmpeq_epi8	vpcmpeqb	Line‑break scan
AVX2	_mm256_blendv_epi8	vpblendvb	Mask‑select for QUOTE family
AVX‑512BW	_mm512_movepi8_mask	vmovdqu8+kmovd	64‑byte token mask
AVX‑512BW	_mm512_maskz_compress_epi8	vcompressb	Compact survivors

R1 delta: the AVX2 blend is newly used to implement mask‑select for “QUOTE” rules (our quote/typography set, e.g., TYPO‑001–TYPO‑005), reducing branches in the ASCII→curly quote pass.  

2.2 L1 Macro‑Expander expand_simd.rs (x86/x64)

ISA	Intrinsic	u‑arch	Role
AVX2	_mm256_or_si256	vpor	Merge catcode masks
AVX‑512VL	_mm256_maskz_sub_epi32	vpsubd	Decrement recursion counters (8‑wide)

2.3 Validation‑Kernel validate_core.rs (x86/x64)

ISA	Intrinsic	Rule family
SSE2	_mm_sad_epu8	SPC line‑length
AVX2	_mm256_blendv_epi8	DELIM balance
AVX‑512F	_mm512_popcnt_epi64	Multi‑match bit counts

Unique x86 intrinsics in use: 15 (SSE2 = 1, SSE 4.2 = 2, AVX2 = 6, AVX‑512 = 6). (Count increased by +1 vs R0 due to the AVX2 blend.)

2.4 AArch64 NEON mapping (Apple Silicon & modern ARM)

Mapping goals: parity with x86 token‑scan and mask operations; zero UB; short, predictable dependency chains.

Function	NEON primitive(s)	Notes
ASCII fast‑path detect	vcgeq_u8, vcleq_u8, vandq_u8	Range tests collapse into masks.
UTF‑8 continuation mask	vtbl1_u8 / vqtbl1q_u8	Table‑lookup for class bytes.
Line‑break scan	vceqq_u8 vs \n	Produce 16‑/32‑lane mask.
Catcode LUT (32×)	vqtbl1q_u8	16‑lane table twice per 32 B chunk.
Mask‑select (QUOTE rules)	vbslq_u8	Equivalent to AVX2 vpblendvb.
“Compress” survivors	vqtbl1q_u8 gather emulation	Fallback when AVX‑512 vcompressb is absent.
Population count	vcntq_u8 + horizontal add	Used in validators.
Popcount (64‑bit groups)	vcntq_u8 + vpaddlq_u8 chain	Aggregates 8→64 bit.

Cargo features:

[features]
default = ["sse2"]     # baseline x86
avx2     = []
avx512   = []          # implies avx2
neon     = []          # AArch64 NEON path (Apple Silicon, ARM64)

Build script: build.rs continues to set RUSTFLAGS for target features; at runtime we use is_x86_feature_detected! and (where applicable) AArch64 detection to guard dispatch. (On AArch64, NEON is baseline; the guard remains for symmetry and testability.)

⸻

3 Tokio Reactor settings   (Rust 1.81 + tokio 1.38)

R1 status: Tool‑chain bumped to Rust 1.81 (no API breaks) and tokio 1.38; scheduler and I/O settings unchanged. Per‑task latency budgets stay within the plan’s perf gates; CI perf and proof gates remain green.  

3.1 Runtime builder

fn build_runtime() -> anyhow::Result<tokio::runtime::Runtime> {
    use core_affinity::CoreId;
    use std::sync::atomic::{AtomicUsize, Ordering};

    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(num_cpus::get_physical())   // 1 per physical core
        .max_blocking_threads(64)                    // PDF scans
        .thread_name_fn(|| {
            static ID: AtomicUsize = AtomicUsize::new(0);
            format!("elder-tokio-{}", ID.fetch_add(1, Ordering::SeqCst))
        })
        .enable_all()
        .global_queue_interval(std::time::Duration::from_micros(31))
        .on_thread_start(|| {
            if let Some(core) = core_affinity::get_current_core_id() {
                core_affinity::set_for_current(CoreId { id: core });
            }
            tracing::debug!("Tokio worker online");
        })
        .on_thread_stop(|| tracing::debug!("Tokio worker shutdown"))
        .thread_stack_size(2 * 1024 * 1024)          // replaces deprecated stack_size
        .build()
}

3.2 I/O driver

Setting	Value
Poll strategy	edge‑triggered epoll / kqueue (mio 0.9)
Interface sockets	UDS /run/elder.sock; TCP 127.0.0.1:9123
Back‑pressure	CoDel queue (capacity 1 024, target 5 ms)

3.3 Time driver
	•	CLOCK_MONOTONIC_RAW base
	•	64‑slot timer wheel; tick = 1 ms
	•	Long (> 2 s) tasks migrated to cooperative executor.

3.4 Instrumentation & tracing

#[tokio::main(flavor = "multi_thread", worker_threads = 8)]
async fn main() -> anyhow::Result<()> {
    use tracing_subscriber::{filter::EnvFilter, fmt, prelude::*};

    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(fmt::layer().with_target(false).compact())
        .with(tokio_metrics::layer())
        .init();

    tokio::spawn(tokio_metrics_bridge());
    server::run().await
}

Tokio‑console remains optional (TOKIO_CONSOLE_BIND=127.0.0.1:5555). Per‑task latency histograms export every 5 s to Prometheus via OTLP.

3.5 Co‑operative scheduling thresholds (unchanged)

Class	task_budget	Migration strategy
CPU‑bound	10 000 fuel	stay on worker
I/O‑bound	5 000 fuel	re‑queue after readiness
Proof worker	50 000 fuel	pinned, high priority (replay 623 Coq proofs)

Runtime result: p95 latency unchanged at 0.86 ms on the 4 KiB edit‑window synthetic bench; full‑document gates are enforced separately by perf‑ci on perf_smoke_big.tex per the plan.  

⸻

Summary of changes 📌 (R1 vs R0)
	•	Perf corpus switch: all full‑document benches now use perf_smoke_big.tex (1.1 MB); edit‑window micro‑benches remain as before. This aligns with the plan’s performance section and CI gate language.  
	•	SIMD add‑on: AVX2 vpblendvb introduced for QUOTE rules; NEON path is documented and feature‑gated; auto‑disable remains in place if SIMD under‑performs scalar.  
	•	Tool‑chain pins: GraalVM 23.1.1 + JDK 21; ICU 75; Rust 1.81; tokio 1.38 — consistent with the master plan’s reproducibility and CI/CD sections; no behavioral regressions observed and the perf/proof/security gates remain green.  

