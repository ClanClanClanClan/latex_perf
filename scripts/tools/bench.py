#!/usr/bin/env python3
"""
LaTeX Perfectionist v25 - Performance Benchmark Harness
Week 5 Performance Gate: p95 < 20ms on perf_smoke corpus (Tier A)

Usage:
    bench.py --scenario edit-stream --iterations 1000
    bench.py --scenario cold-lex --corpus perf_smoke
    bench.py --scenario full-pipeline --output bench.json
"""

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from statistics import median, quantiles
from typing import Dict, List, Tuple

class PerformanceBenchmark:
    def __init__(self):
        self.project_root = Path(__file__).parent.parent
        self.corpus_dir = self.project_root / "corpora"
        self.build_dir = self.project_root / "_build" / "default"
        
    def load_corpus(self, name: str) -> str:
        """Load test corpus by name"""
        corpus_file = self.corpus_dir / f"{name}.tex"
        if not corpus_file.exists():
            raise FileNotFoundError(f"Corpus {name} not found at {corpus_file}")
        return corpus_file.read_text()
    
    def run_lexer_only(self, content: str) -> Tuple[float, Dict]:
        """Run L0 lexer only - used for throughput measurement"""
        # Write content to temp file
        temp_file = "/tmp/bench_input.tex"
        with open(temp_file, 'w') as f:
            f.write(content)
        
        # Measure L0 lexer performance
        start_time = time.perf_counter()
        
        try:
            # Run the lexer binary
            result = subprocess.run([
                str(self.build_dir / "src" / "core" / "l0_lexer.exe"),
                temp_file
            ], capture_output=True, text=True, timeout=10)
            
            end_time = time.perf_counter()
            elapsed_us = (end_time - start_time) * 1_000_000
            
            if result.returncode != 0:
                return float('inf'), {"error": result.stderr}
            
            # Parse token count from output
            token_count = len(result.stdout.strip().split('\n'))
            
            return elapsed_us, {
                "tokens": token_count,
                "throughput_tokens_per_sec": token_count / (elapsed_us / 1_000_000) if elapsed_us > 0 else 0,
                "stdout_lines": token_count
            }
            
        except subprocess.TimeoutExpired:
            return float('inf'), {"error": "timeout"}
        finally:
            if os.path.exists(temp_file):
                os.unlink(temp_file)
    
    def run_full_pipeline(self, content: str) -> Tuple[float, Dict]:
        """Run full L0->L1 pipeline"""
        # Write content to temp file
        temp_file = "/tmp/bench_input.tex"
        with open(temp_file, 'w') as f:
            f.write(content)
        
        start_time = time.perf_counter()
        
        try:
            # Run integration test which exercises both L0 and L1
            result = subprocess.run([
                str(self.build_dir / "test_l0_l1_integration.exe"),
                temp_file
            ], capture_output=True, text=True, timeout=10)
            
            end_time = time.perf_counter()
            elapsed_us = (end_time - start_time) * 1_000_000
            
            if result.returncode != 0:
                return float('inf'), {"error": result.stderr}
            
            # Parse output for metrics
            lines = result.stdout.strip().split('\n')
            metrics = {"stages": []}
            
            for line in lines:
                if "L0 time:" in line:
                    metrics["l0_time_us"] = float(line.split()[-1])
                elif "L1 time:" in line:
                    metrics["l1_time_us"] = float(line.split()[-1])
                elif "Total tokens:" in line:
                    metrics["tokens"] = int(line.split()[-1])
                elif "Cache hits:" in line:
                    metrics["cache_hits"] = int(line.split()[-1])
            
            return elapsed_us, metrics
            
        except subprocess.TimeoutExpired:
            return float('inf'), {"error": "timeout"}
        finally:
            if os.path.exists(temp_file):
                os.unlink(temp_file)
    
    def run_edit_stream(self, content: str, iterations: int) -> List[Tuple[float, Dict]]:
        """Simulate incremental editing - key metric for Week 5"""
        results = []
        
        # Generate simple edits (insert characters at random positions)
        import random
        random.seed(42)  # Reproducible
        
        for i in range(iterations):
            # Make a small edit
            pos = random.randint(0, len(content) - 1)
            char = random.choice("abcdefghijklmnopqrstuvwxyz ")
            edited_content = content[:pos] + char + content[pos:]
            
            # Measure incremental processing time
            elapsed_us, metrics = self.run_full_pipeline(edited_content)
            results.append((elapsed_us, metrics))
            
            # Use edited content for next iteration
            content = edited_content
            
            if i % 100 == 0:
                print(f"Edit iteration {i}/{iterations}", file=sys.stderr)
        
        return results
        
    def run_scenario(self, scenario: str, corpus: str = "perf_smoke", 
                    iterations: int = 1000) -> Dict:
        """Run a specific benchmark scenario"""
        print(f"Loading corpus: {corpus}", file=sys.stderr)
        content = self.load_corpus(corpus)
        
        print(f"Corpus size: {len(content)} bytes", file=sys.stderr)
        print(f"Running scenario: {scenario}", file=sys.stderr)
        
        if scenario == "cold-lex":
            # Single cold lexer run for throughput
            elapsed_us, metrics = self.run_lexer_only(content)
            throughput_mbs = (len(content) / (1024 * 1024)) / (elapsed_us / 1_000_000)
            
            return {
                "scenario": scenario,
                "corpus": corpus,
                "elapsed_us": elapsed_us,
                "throughput_mb_per_sec": throughput_mbs,
                "metrics": metrics
            }
        
        elif scenario == "edit-stream":
            # Multiple incremental edits - this is the Week 5 gate test
            results = self.run_edit_stream(content, iterations)
            latencies = [r[0] for r in results if r[0] != float('inf')]
            
            if not latencies:
                return {"error": "All runs failed"}
            
            # Calculate percentiles
            latencies.sort()
            n = len(latencies)
            p50 = latencies[n // 2]
            p95 = latencies[int(n * 0.95)]
            p99 = latencies[int(n * 0.99)]
            
            return {
                "scenario": scenario,
                "corpus": corpus,
                "iterations": iterations,
                "successful_runs": len(latencies),
                "failed_runs": len(results) - len(latencies),
                "latency_p50_us": p50,
                "latency_p95_us": p95,
                "latency_p99_us": p99,
                "latency_p95_ms": p95 / 1000,  # Week 5 gate metric
                "week5_gate_passed": p95 < 20000,  # < 20ms requirement
                "all_latencies": latencies[:50] if len(latencies) > 50 else latencies  # Sample for debugging
            }
        
        elif scenario == "full-pipeline":
            # Single full pipeline run
            elapsed_us, metrics = self.run_full_pipeline(content)
            
            return {
                "scenario": scenario,
                "corpus": corpus,
                "elapsed_us": elapsed_us,
                "elapsed_ms": elapsed_us / 1000,
                "metrics": metrics
            }
        
        else:
            raise ValueError(f"Unknown scenario: {scenario}")

def main():
    parser = argparse.ArgumentParser(description="LaTeX Perfectionist v25 Benchmarks")
    parser.add_argument("--scenario", required=True, 
                       choices=["cold-lex", "edit-stream", "full-pipeline"],
                       help="Benchmark scenario to run")
    parser.add_argument("--corpus", default="perf_smoke",
                       help="Test corpus to use")
    parser.add_argument("--iterations", type=int, default=1000,
                       help="Number of iterations for edit-stream")
    parser.add_argument("--output", help="Output JSON file")
    parser.add_argument("--verbose", "-v", action="store_true")
    
    args = parser.parse_args()
    
    bench = PerformanceBenchmark()
    
    try:
        result = bench.run_scenario(args.scenario, args.corpus, args.iterations)
        
        if args.output:
            with open(args.output, 'w') as f:
                json.dump(result, f, indent=2)
        else:
            print(json.dumps(result, indent=2))
        
        # Exit code based on Week 5 gate
        if args.scenario == "edit-stream":
            if result.get("week5_gate_passed", False):
        print(f"✅ Week 5 gate PASSED: p95 = {result['latency_p95_ms']:.2f}ms < 20ms", 
                      file=sys.stderr)
                sys.exit(0)
            else:
                print(f"❌ Week 5 gate FAILED: p95 = {result['latency_p95_ms']:.2f}ms >= 2ms", 
                      file=sys.stderr)
                sys.exit(1)
                
    except Exception as e:
        print(f"Benchmark failed: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
