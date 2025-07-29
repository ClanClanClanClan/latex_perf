#!/usr/bin/env python3
"""
🚀 PERFORMANCE COMPARISON - LaTeX Perfectionist v24-R3
Compare original vs optimized tokenizer performance

This script measures the dramatic performance improvement achieved
by fixing the quadratic time complexity in the lexer.
"""

import time
import subprocess
from pathlib import Path

def benchmark_tokenizer(tokenizer_path, test_file, label):
    """Benchmark a tokenizer and return results"""
    print(f"\n📊 Testing {label}...")
    
    results = []
    for run in range(3):  # Multiple runs for accuracy
        start_time = time.time()
        try:
            result = subprocess.run([
                str(tokenizer_path), str(test_file)
            ], 
            capture_output=True,
            text=True,
            timeout=120  # 2 minute timeout
            )
            
            end_time = time.time()
            processing_time = end_time - start_time
            
            if result.returncode == 0:
                token_count = len([line for line in result.stdout.strip().split('\n') if line.strip()])
                results.append({
                    'time_seconds': processing_time,
                    'tokens': token_count,
                    'success': True
                })
                print(f"  Run {run+1}: {processing_time:.3f}s ({token_count} tokens)")
            else:
                results.append({
                    'time_seconds': processing_time,
                    'tokens': 0,
                    'success': False,
                    'error': result.stderr
                })
                print(f"  Run {run+1}: FAILED after {processing_time:.3f}s - {result.stderr[:100]}")
        
        except subprocess.TimeoutExpired:
            results.append({
                'time_seconds': 120.0,
                'tokens': 0,
                'success': False,
                'error': 'Timeout'
            })
            print(f"  Run {run+1}: TIMEOUT (>120s)")
    
    return results

def main():
    print("🚀 PERFORMANCE COMPARISON - LaTeX Perfectionist v24-R3")
    print("=" * 70)
    
    # Test file
    test_file = Path("/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/corpus/papers/2507.07717v1/main.tex")
    file_size_kb = test_file.stat().st_size / 1024
    
    print(f"Test file: {test_file.name}")
    print(f"File size: {file_size_kb:.1f} KB")
    
    # Tokenizers to test
    base_dir = Path("/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/src/integration/python-ocaml")
    tokenizers = [
        (base_dir / "file_tokenizer_native", "Original (Coq-extracted)"),
        (base_dir / "tokenizer_optimized", "Optimized (Hand-written)")
    ]
    
    all_results = {}
    
    for tokenizer_path, label in tokenizers:
        if tokenizer_path.exists():
            results = benchmark_tokenizer(tokenizer_path, test_file, label)
            successful_runs = [r for r in results if r['success']]
            
            if successful_runs:
                avg_time = sum(r['time_seconds'] for r in successful_runs) / len(successful_runs)
                avg_tokens = sum(r['tokens'] for r in successful_runs) / len(successful_runs)
                throughput = file_size_kb / avg_time if avg_time > 0 else 0
                
                all_results[label] = {
                    'avg_time': avg_time,
                    'avg_tokens': avg_tokens,
                    'throughput_kb_sec': throughput,
                    'successful_runs': len(successful_runs)
                }
            else:
                all_results[label] = {
                    'avg_time': float('inf'),
                    'avg_tokens': 0,
                    'throughput_kb_sec': 0,
                    'successful_runs': 0
                }
        else:
            print(f"\n❌ {label}: Not found at {tokenizer_path}")
    
    # Summary
    print("\n📈 PERFORMANCE SUMMARY")
    print("=" * 50)
    
    for label, results in all_results.items():
        if results['successful_runs'] > 0:
            print(f"\n{label}:")
            print(f"  Average time: {results['avg_time']:.3f}s")
            print(f"  Throughput: {results['throughput_kb_sec']:.1f} KB/sec")
            print(f"  Tokens generated: {results['avg_tokens']:.0f}")
            print(f"  Successful runs: {results['successful_runs']}/3")
        else:
            print(f"\n{label}: ALL RUNS FAILED")
    
    # Calculate speedup
    if len(all_results) >= 2:
        labels = list(all_results.keys())
        original_time = all_results[labels[0]]['avg_time']
        optimized_time = all_results[labels[1]]['avg_time']
        
        if original_time != float('inf') and optimized_time > 0:
            speedup = original_time / optimized_time
            print(f"\n🚀 SPEEDUP ACHIEVED: {speedup:.1f}x faster!")
            print(f"Performance improvement: {((speedup - 1) * 100):.0f}%")
            
            # Calculate target achievement
            target_time = 1.0  # <1s target
            if optimized_time <= target_time:
                print(f"✅ TARGET ACHIEVED: {optimized_time:.3f}s < {target_time}s")
            else:
                print(f"⚠️  Target not quite met: {optimized_time:.3f}s > {target_time}s")
                additional_speedup_needed = optimized_time / target_time
                print(f"Additional {additional_speedup_needed:.1f}x speedup needed for target")

if __name__ == "__main__":
    main()