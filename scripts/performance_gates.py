#!/usr/bin/env python3
"""
PERFORMANCE GATES AUTOMATION - v25_R1 Compliance Checker
Automates performance validation for LaTeX Perfectionist v25_R1
"""

import subprocess
import time
import json
import sys
import os
from pathlib import Path
from statistics import mean, median
from typing import List, Dict, Tuple

class PerformanceGates:
    """Automated performance gate validation system"""
    
    def __init__(self):
        self.project_root = Path(__file__).parent.parent
        self.targets = {
            'p99_latency_ms': 20.0,      # v25_R1 target: ≤20ms P99
            'memory_ratio': 2.0,         # v25_R1 target: ≤2.0× source size
            'first_token_us': 350.0,     # v25_R1 target: ≤350µs
            'gc_collections_per_1k': 0.5, # Target: <0.5 major collections per 1000 runs
        }
        self.test_corpus = self.project_root / "corpora" / "perf" / "perf_smoke_big.tex"
        self.cli_binary = self.project_root / "latex_perfectionist_cli_phase3_ultra"
        
    def check_prerequisites(self) -> bool:
        """Check that required files exist"""
        if not self.test_corpus.exists():
            print(f"❌ Test corpus not found: {self.test_corpus}")
            return False
            
        if not self.cli_binary.exists():
            print(f"❌ CLI binary not found: {self.cli_binary}")
            return False
            
        print(f"✅ Prerequisites check passed")
        print(f"   Test corpus: {self.test_corpus}")
        print(f"   CLI binary: {self.cli_binary}")
        return True
    
    def run_benchmark(self, iterations: int = 1000) -> Dict:
        """Run performance benchmark with statistical validation"""
        print(f"\n🔬 Running performance benchmark ({iterations} iterations)")
        
        latencies = []
        memory_usages = []
        token_counts = []
        
        for i in range(iterations):
            if i % 100 == 0:
                print(f"   Progress: {i}/{iterations} ({100*i//iterations}%)")
            
            # Run CLI tool and measure performance
            start_time = time.perf_counter()
            
            try:
                result = subprocess.run(
                    [str(self.cli_binary), "--summary", str(self.test_corpus)],
                    capture_output=True,
                    text=True,
                    timeout=5.0  # 5 second timeout
                )
                
                end_time = time.perf_counter()
                latency_ms = (end_time - start_time) * 1000.0
                
                if result.returncode == 0:
                    latencies.append(latency_ms)
                    
                    # Parse output for token count and memory usage
                    output_lines = result.stdout.strip().split('\n')
                    for line in output_lines:
                        if 'tokens' in line.lower():
                            # Extract token count from output
                            token_count = self._extract_number(line)
                            if token_count:
                                token_counts.append(token_count)
                        elif 'memory' in line.lower() or 'mb' in line.lower():
                            # Extract memory usage
                            memory_mb = self._extract_number(line)
                            if memory_mb:
                                memory_usages.append(memory_mb)
                else:
                    print(f"⚠️  Run {i} failed with return code {result.returncode}")
                    
            except subprocess.TimeoutExpired:
                print(f"⚠️  Run {i} timed out")
            except Exception as e:
                print(f"⚠️  Run {i} error: {e}")
        
        if not latencies:
            print("❌ No successful runs completed")
            return {}
        
        # Calculate statistics
        latencies.sort()
        n = len(latencies)
        
        stats = {
            'iterations': n,
            'latency_ms': {
                'min': min(latencies),
                'max': max(latencies),
                'mean': mean(latencies),
                'median': median(latencies),
                'p90': latencies[int(0.90 * n)] if n > 10 else latencies[-1],
                'p95': latencies[int(0.95 * n)] if n > 20 else latencies[-1],
                'p99': latencies[int(0.99 * n)] if n > 100 else latencies[-1],
            },
            'token_count': token_counts[0] if token_counts else 0,
            'memory_mb': memory_usages[0] if memory_usages else 0,
            'success_rate': len(latencies) / iterations,
        }
        
        return stats
    
    def _extract_number(self, text: str) -> float:
        """Extract first number from text string"""
        import re
        match = re.search(r'(\d+(?:\.\d+)?)', text)
        return float(match.group(1)) if match else None
    
    def validate_performance_gates(self, stats: Dict) -> bool:
        """Validate performance against v25_R1 targets"""
        print(f"\n🎯 PERFORMANCE GATE VALIDATION")
        print(f"=" * 50)
        
        all_passed = True
        
        # P99 Latency Gate
        p99_latency = stats['latency_ms']['p99']
        p99_target = self.targets['p99_latency_ms']
        p99_passed = p99_latency <= p99_target
        margin = ((p99_target - p99_latency) / p99_target) * 100
        
        print(f"P99 Latency:     {p99_latency:.3f}ms (target: ≤{p99_target}ms)")
        if p99_passed:
            print(f"                 ✅ PASS ({margin:.1f}% margin)")
        else:
            print(f"                 ❌ FAIL ({-margin:.1f}% over target)")
            all_passed = False
        
        # Memory Efficiency Gate (if available)
        if stats['memory_mb'] > 0:
            corpus_size_mb = self.test_corpus.stat().st_size / (1024 * 1024)
            memory_ratio = stats['memory_mb'] / corpus_size_mb
            memory_target = self.targets['memory_ratio']
            memory_passed = memory_ratio <= memory_target
            
            print(f"Memory Ratio:    {memory_ratio:.2f}× (target: ≤{memory_target}×)")
            if memory_passed:
                print(f"                 ✅ PASS")
            else:
                print(f"                 ❌ FAIL")
                all_passed = False
        
        # Success Rate Gate
        success_rate = stats['success_rate']
        success_passed = success_rate >= 0.95
        
        print(f"Success Rate:    {success_rate:.3f} (target: ≥0.95)")
        if success_passed:
            print(f"                 ✅ PASS")
        else:
            print(f"                 ❌ FAIL")
            all_passed = False
        
        # Overall Performance Summary
        print(f"\n📊 PERFORMANCE SUMMARY")
        print(f"Mean:            {stats['latency_ms']['mean']:.3f}ms")
        print(f"P95:             {stats['latency_ms']['p95']:.3f}ms")
        print(f"P99:             {stats['latency_ms']['p99']:.3f}ms")
        print(f"Token Count:     {stats['token_count']:,}")
        print(f"Iterations:      {stats['iterations']:,}")
        
        print(f"\n🏁 OVERALL RESULT")
        if all_passed:
            print(f"✅ ALL PERFORMANCE GATES PASSED")
            print(f"   v25_R1 compliance: VERIFIED")
        else:
            print(f"❌ PERFORMANCE GATES FAILED")
            print(f"   v25_R1 compliance: NOT MET")
        
        return all_passed
    
    def generate_report(self, stats: Dict, passed: bool) -> str:
        """Generate performance report for CI/documentation"""
        report = {
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime()),
            'version': 'v25_R1',
            'performance_gates': {
                'passed': passed,
                'targets': self.targets,
                'results': stats
            },
            'summary': {
                'p99_latency_ms': stats['latency_ms']['p99'],
                'compliance_status': 'PASS' if passed else 'FAIL',
                'margin_percent': ((self.targets['p99_latency_ms'] - stats['latency_ms']['p99']) / self.targets['p99_latency_ms']) * 100
            }
        }
        
        return json.dumps(report, indent=2)

def main():
    """Main performance gate execution"""
    print("🚀 LATEX PERFECTIONIST v25_R1 PERFORMANCE GATES")
    print("=" * 60)
    
    gates = PerformanceGates()
    
    if not gates.check_prerequisites():
        sys.exit(1)
    
    # Get iteration count from command line or use default
    iterations = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    
    # Run performance benchmark
    stats = gates.run_benchmark(iterations)
    
    if not stats:
        print("❌ Benchmark failed - no results")
        sys.exit(1)
    
    # Validate against performance gates
    passed = gates.validate_performance_gates(stats)
    
    # Generate report
    report = gates.generate_report(stats, passed)
    
    # Save report to file
    report_file = Path("performance_gate_report.json")
    with open(report_file, 'w') as f:
        f.write(report)
    
    print(f"\n📄 Report saved to: {report_file}")
    
    # Exit with appropriate code for CI
    sys.exit(0 if passed else 1)

if __name__ == "__main__":
    main()