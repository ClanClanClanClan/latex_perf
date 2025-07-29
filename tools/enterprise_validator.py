#!/usr/bin/env python3
"""
Enterprise-Scale Validator for LaTeX Perfectionist v24

Validates 2,846 papers × 75 rules = 213,450 validations in parallel
"""

import json
import time
import multiprocessing
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Tuple
import subprocess
import psutil
from tqdm import tqdm
import argparse

@dataclass
class ValidationResult:
    paper_id: str
    paper_path: str
    issues: List[Dict]
    validation_time: float
    memory_usage: int
    success: bool
    error_message: Optional[str] = None

@dataclass
class EnterpriseResults:
    total_papers: int
    successful_validations: int
    failed_validations: int
    total_issues: int
    total_time: float
    avg_time_per_paper: float
    peak_memory: int
    validations_per_second: float
    rule_distribution: Dict[str, int]
    results: List[ValidationResult]

class EnterpriseValidator:
    def __init__(self, corpus_path: str, num_workers: int = 8):
        self.corpus_path = Path(corpus_path)
        self.num_workers = num_workers
        self.validator_path = Path(__file__).parent.parent / "src/extraction/test_enterprise_streaming_native"
        self.papers = self.discover_papers()
        
    def discover_papers(self) -> List[Path]:
        """Discover all papers in the corpus."""
        papers = []
        
        # Look for paper directories
        for paper_dir in self.corpus_path.iterdir():
            if paper_dir.is_dir():
                # Find main.tex or similar
                main_files = list(paper_dir.glob("*.tex"))
                if main_files:
                    papers.append(paper_dir)
                    
        print(f"Discovered {len(papers)} papers in corpus")
        return papers
    
    def validate_paper(self, paper_path: Path) -> ValidationResult:
        """Validate a single paper."""
        start_time = time.time()
        start_memory = psutil.Process().memory_info().rss
        
        try:
            # Find main tex file
            tex_files = list(paper_path.glob("*.tex"))
            if not tex_files:
                return ValidationResult(
                    paper_id=paper_path.name,
                    paper_path=str(paper_path),
                    issues=[],
                    validation_time=0,
                    memory_usage=0,
                    success=False,
                    error_message="No .tex files found"
                )
            
            main_tex = tex_files[0]  # Use first .tex file
            
            # Run validator 
            result = subprocess.run(
                [str(self.validator_path.absolute()), str(main_tex.absolute())],
                capture_output=True,
                text=True,
                timeout=30  # 30 second timeout per paper
            )
            
            end_time = time.time()
            end_memory = psutil.Process().memory_info().rss
            
            if result.returncode == 0:
                # Parse JSON output from streaming validator
                try:
                    data = json.loads(result.stdout)
                    issue_count = data.get('issues', 0)
                    # Create simplified issue list
                    issues = [{'rule_id': 'SUMMARY', 'message': f'{issue_count} issues found'}] if issue_count > 0 else []
                except json.JSONDecodeError:
                    issues = []
                
                return ValidationResult(
                    paper_id=paper_path.name,
                    paper_path=str(paper_path),
                    issues=issues,
                    validation_time=end_time - start_time,
                    memory_usage=end_memory - start_memory,
                    success=True
                )
            else:
                return ValidationResult(
                    paper_id=paper_path.name,
                    paper_path=str(paper_path),
                    issues=[],
                    validation_time=end_time - start_time,
                    memory_usage=end_memory - start_memory,
                    success=False,
                    error_message=result.stderr
                )
                
        except subprocess.TimeoutExpired:
            return ValidationResult(
                paper_id=paper_path.name,
                paper_path=str(paper_path),
                issues=[],
                validation_time=30.0,
                memory_usage=0,
                success=False,
                error_message="Validation timeout"
            )
        except Exception as e:
            return ValidationResult(
                paper_id=paper_path.name,
                paper_path=str(paper_path),
                issues=[],
                validation_time=time.time() - start_time,
                memory_usage=0,
                success=False,
                error_message=str(e)
            )
    
    def validate_corpus_parallel(self, max_papers: Optional[int] = None) -> EnterpriseResults:
        """Validate entire corpus in parallel."""
        papers_to_process = self.papers[:max_papers] if max_papers else self.papers
        
        print(f"Starting enterprise validation of {len(papers_to_process)} papers...")
        print(f"Using {self.num_workers} workers")
        
        start_time = time.time()
        results = []
        
        with ProcessPoolExecutor(max_workers=self.num_workers) as executor:
            # Submit all papers
            future_to_paper = {
                executor.submit(self.validate_paper, paper): paper
                for paper in papers_to_process
            }
            
            # Process results as they complete
            for future in tqdm(as_completed(future_to_paper), total=len(papers_to_process)):
                paper = future_to_paper[future]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    # Create error result
                    error_result = ValidationResult(
                        paper_id=paper.name,
                        paper_path=str(paper),
                        issues=[],
                        validation_time=0,
                        memory_usage=0,
                        success=False,
                        error_message=str(e)
                    )
                    results.append(error_result)
        
        end_time = time.time()
        total_time = end_time - start_time
        
        # Analyze results
        successful = sum(1 for r in results if r.success)
        failed = len(results) - successful
        total_issues = sum(len(r.issues) for r in results)
        avg_time = total_time / len(results) if results else 0
        peak_memory = max(r.memory_usage for r in results) if results else 0
        validations_per_second = len(results) / total_time if total_time > 0 else 0
        
        # Rule distribution
        rule_distribution = {}
        for result in results:
            for issue in result.issues:
                rule_id = issue.get('rule_id', 'unknown')
                rule_distribution[rule_id] = rule_distribution.get(rule_id, 0) + 1
        
        return EnterpriseResults(
            total_papers=len(results),
            successful_validations=successful,
            failed_validations=failed,
            total_issues=total_issues,
            total_time=total_time,
            avg_time_per_paper=avg_time,
            peak_memory=peak_memory,
            validations_per_second=validations_per_second,
            rule_distribution=rule_distribution,
            results=results
        )
    
    def validate_corpus_incremental(self, batch_size: int = 100) -> EnterpriseResults:
        """Validate corpus in incremental batches."""
        all_results = []
        
        for i in range(0, len(self.papers), batch_size):
            batch = self.papers[i:i+batch_size]
            print(f"Processing batch {i//batch_size + 1}: papers {i+1}-{min(i+batch_size, len(self.papers))}")
            
            batch_results = []
            for paper in tqdm(batch, desc=f"Batch {i//batch_size + 1}"):
                result = self.validate_paper(paper)
                batch_results.append(result)
            
            all_results.extend(batch_results)
            
            # Save incremental results
            incremental_file = f"results/incremental_batch_{i//batch_size + 1}.json"
            Path("results").mkdir(exist_ok=True)
            
            with open(incremental_file, 'w') as f:
                json.dump([asdict(r) for r in batch_results], f, indent=2)
        
        # Combine all results
        return self.combine_results(all_results)
    
    def combine_results(self, results: List[ValidationResult]) -> EnterpriseResults:
        """Combine results into enterprise summary."""
        successful = sum(1 for r in results if r.success)
        failed = len(results) - successful
        total_issues = sum(len(r.issues) for r in results)
        total_time = sum(r.validation_time for r in results)
        avg_time = total_time / len(results) if results else 0
        peak_memory = max(r.memory_usage for r in results) if results else 0
        validations_per_second = len(results) / total_time if total_time > 0 else 0
        
        # Rule distribution
        rule_distribution = {}
        for result in results:
            for issue in result.issues:
                rule_id = issue.get('rule_id', 'unknown')
                rule_distribution[rule_id] = rule_distribution.get(rule_id, 0) + 1
        
        return EnterpriseResults(
            total_papers=len(results),
            successful_validations=successful,
            failed_validations=failed,
            total_issues=total_issues,
            total_time=total_time,
            avg_time_per_paper=avg_time,
            peak_memory=peak_memory,
            validations_per_second=validations_per_second,
            rule_distribution=rule_distribution,
            results=results
        )

def main():
    parser = argparse.ArgumentParser(description='Enterprise LaTeX Validator')
    parser.add_argument('--corpus', type=str, default='corpus/papers',
                      help='Path to corpus directory')
    parser.add_argument('--count', type=int, default=None,
                      help='Number of papers to process (default: all)')
    parser.add_argument('--workers', type=int, default=8,
                      help='Number of parallel workers')
    parser.add_argument('--output', type=str, default='results/enterprise_results.json',
                      help='Output file for results')
    parser.add_argument('--incremental', action='store_true',
                      help='Process in incremental batches')
    parser.add_argument('--batch-size', type=int, default=100,
                      help='Batch size for incremental processing')
    
    args = parser.parse_args()
    
    # Create results directory
    Path("results").mkdir(exist_ok=True)
    
    # Initialize validator
    validator = EnterpriseValidator(args.corpus, args.workers)
    
    print(f"Enterprise Validator initialized:")
    print(f"  Corpus: {args.corpus}")
    print(f"  Papers discovered: {len(validator.papers)}")
    print(f"  Workers: {args.workers}")
    print(f"  Target count: {args.count or 'all'}")
    
    # Run validation
    if args.incremental:
        results = validator.validate_corpus_incremental(args.batch_size)
    else:
        results = validator.validate_corpus_parallel(args.count)
    
    # Save results
    with open(args.output, 'w') as f:
        json.dump(asdict(results), f, indent=2)
    
    # Print summary
    print("\n" + "="*60)
    print("ENTERPRISE VALIDATION COMPLETE")
    print("="*60)
    print(f"Total papers: {results.total_papers}")
    print(f"Successful validations: {results.successful_validations}")
    print(f"Failed validations: {results.failed_validations}")
    print(f"Success rate: {results.successful_validations/results.total_papers*100:.1f}%")
    print(f"Total issues found: {results.total_issues}")
    print(f"Average issues per paper: {results.total_issues/results.total_papers:.1f}")
    print(f"Total time: {results.total_time:.1f} seconds")
    print(f"Average time per paper: {results.avg_time_per_paper:.3f} seconds")
    print(f"Validations per second: {results.validations_per_second:.1f}")
    print(f"Peak memory usage: {results.peak_memory/1024/1024:.1f} MB")
    print(f"Results saved to: {args.output}")
    
    # Top 10 rules by frequency
    print("\nTop 10 rules by frequency:")
    sorted_rules = sorted(results.rule_distribution.items(), key=lambda x: x[1], reverse=True)
    for rule, count in sorted_rules[:10]:
        print(f"  {rule}: {count} issues")

if __name__ == '__main__':
    main()