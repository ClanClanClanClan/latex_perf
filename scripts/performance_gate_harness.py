#!/usr/bin/env python3
"""
Performance Gate Harness for LaTeX Perfectionist v25
Automated measurement system for Week 4/5 performance gates

Per v25_master.yaml specifications:
- Week 4 target: p95 < 4ms  
- Week 5 target: p95 < 2ms (CRITICAL GATE)
- Final target: p95 < 1ms for edit operations
"""

import subprocess
import time
import statistics
import json
import sys
from pathlib import Path

class PerformanceGateHarness:
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent
        self.test_corpus = self.repo_root / "corpora" / "perf_smoke.tex"
        self.results_dir = self.repo_root / "results"
        self.results_dir.mkdir(exist_ok=True)
        
    def build_lexer(self):
        """Build optimized lexer for testing"""
        print("🔨 Building lexer...")
        result = subprocess.run(['make', 'build'], 
                              cwd=self.repo_root, 
                              capture_output=True, text=True)
        if result.returncode != 0:
            print(f"❌ Build failed: {result.stderr}")
            return False
        print("✅ Build successful")
        return True
        
    def measure_performance(self, iterations=100):
        """Measure lexer performance with statistical analysis"""
        print(f"📊 Running {iterations} performance measurements...")
        
        if not self.test_corpus.exists():
            print(f"❌ Test corpus not found: {self.test_corpus}")
            return None
            
        times = []
        lexer_cmd = ['./perf_test', str(self.test_corpus)]
        
        for i in range(iterations):
            if i % 10 == 0:
                print(f"Progress: {i}/{iterations}")
                
            start = time.perf_counter()
            result = subprocess.run(lexer_cmd, cwd=self.repo_root, 
                                  capture_output=True, text=True)
            end = time.perf_counter()
            
            if result.returncode != 0:
                print(f"❌ Lexer failed on iteration {i}: {result.stderr}")
                continue
                
            elapsed_ms = (end - start) * 1000
            times.append(elapsed_ms)
            
        return times
        
    def analyze_results(self, times):
        """Statistical analysis of performance measurements"""
        if not times:
            return None
            
        return {
            'count': len(times),
            'median_ms': statistics.median(times),
            'mean_ms': statistics.mean(times),
            'p95_ms': statistics.quantiles(times, n=20)[18],  # 95th percentile
            'p99_ms': statistics.quantiles(times, n=100)[98], # 99th percentile
            'min_ms': min(times),
            'max_ms': max(times),
            'stdev_ms': statistics.stdev(times) if len(times) > 1 else 0
        }
        
    def evaluate_gates(self, stats):
        """Evaluate against Week 4/5 gate requirements"""
        gates = {
            'week4_gate': {'target_ms': 4.0, 'status': 'UNKNOWN'},
            'week5_gate': {'target_ms': 2.0, 'status': 'UNKNOWN'},
            'final_target': {'target_ms': 1.0, 'status': 'UNKNOWN'}
        }
        
        p95 = stats['p95_ms']
        
        for gate_name, gate in gates.items():
            if p95 < gate['target_ms']:
                gate['status'] = '✅ PASS'
            else:
                improvement_needed = (p95 / gate['target_ms'] - 1) * 100
                gate['status'] = f'❌ FAIL (need {improvement_needed:.1f}% improvement)'
                
        return gates
        
    def save_results(self, stats, gates):
        """Save results for tracking and CI integration"""
        timestamp = int(time.time())
        results = {
            'timestamp': timestamp,
            'current_performance': stats,
            'gate_evaluation': gates,
            'measurement_date': time.strftime('%Y-%m-%d %H:%M:%S')
        }
        
        results_file = self.results_dir / f"performance_gate_{timestamp}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2)
            
        return results_file
        
    def run_full_assessment(self):
        """Run complete performance gate assessment"""
        print("🚀 Starting Performance Gate Assessment")
        print("=" * 50)
        
        # Build system
        if not self.build_lexer():
            return False
            
        # Measure performance  
        times = self.measure_performance()
        if not times:
            print("❌ Performance measurement failed")
            return False
            
        # Analyze results
        stats = self.analyze_results(times)
        gates = self.evaluate_gates(stats)
        
        # Report results
        print("\n📈 PERFORMANCE ANALYSIS RESULTS")
        print("=" * 50)
        print(f"Median: {stats['median_ms']:.2f}ms")
        print(f"P95:    {stats['p95_ms']:.2f}ms")
        print(f"P99:    {stats['p99_ms']:.2f}ms")
        print(f"StdDev: {stats['stdev_ms']:.2f}ms")
        
        print("\n🎯 GATE EVALUATION")
        print("=" * 50)
        for gate_name, gate in gates.items():
            target = gate['target_ms']
            status = gate['status'] 
            print(f"{gate_name.upper()}: <{target}ms → {status}")
            
        # Save for CI/tracking
        results_file = self.save_results(stats, gates)
        print(f"\n💾 Results saved: {results_file}")
        
        # Exit with appropriate code for CI
        all_passed = all('PASS' in gate['status'] for gate in gates.values())
        return all_passed

def main():
    harness = PerformanceGateHarness()
    success = harness.run_full_assessment()
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()