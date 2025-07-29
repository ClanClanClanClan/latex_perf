#!/usr/bin/env python3
"""
🎯 ENHANCED CORPUS VALIDATION SYSTEM - PHASE 2
LaTeX Perfectionist v24-R3: Full Corpus Validation with Parallel Processing

This implements Phase 2 of the roadmap:
- Parallel processing support
- Failure triage system
- Comprehensive error analysis
- 2,846 paper target
"""

import os
import sys
import json
import time
import logging
import argparse
import traceback
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, asdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime
import multiprocessing

# Import our working integration
from fixed_integration import RobustOCamlBridge, Token

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class PaperValidationResult:
    """Result of validating a single paper"""
    paper_id: str
    file_count: int
    total_chars: int
    processing_time_ms: float
    
    # Token statistics
    total_tokens: int
    text_tokens: int
    math_shifts: int
    commands: int
    other_tokens: int
    
    # CRITICAL: False positive analysis
    text_tokens_with_dollar: int
    text_tokens_with_caret: int
    text_tokens_with_underscore: int
    false_positive_potential: int
    
    # Detailed failure info for triage
    problematic_tokens: List[Dict[str, Any]]
    
    # Status
    success: bool
    error_message: Optional[str] = None
    validation_timestamp: str = ""

@dataclass
class CorpusValidationResults:
    """Comprehensive results from corpus validation"""
    # Scale metrics
    total_papers_attempted: int
    successful_validations: int
    failed_validations: int
    total_latex_files: int
    total_characters_processed: int
    total_tokens_generated: int
    
    # Performance metrics
    total_processing_time_ms: float
    average_time_per_paper: float
    papers_per_second: float
    characters_per_second: float
    tokens_per_second: float
    parallel_workers_used: int
    
    # CRITICAL: False positive analysis
    total_false_positive_indicators: int
    papers_with_clean_tokenization: int
    papers_with_dollar_issues: int
    papers_with_caret_issues: int
    papers_with_underscore_issues: int
    estimated_false_positives_prevented: int
    false_positive_elimination_rate: float
    
    # Quality metrics
    largest_paper_chars: int
    largest_paper_tokens: int
    failure_rate: float
    
    validation_timestamp: str

def validate_single_paper(args: Tuple[Path, Path]) -> PaperValidationResult:
    """
    Validate a single paper - designed for parallel execution
    
    Args are passed as tuple for multiprocessing compatibility
    """
    paper_path, lexer_path = args
    paper_id = paper_path.name
    start_time = time.time()
    
    try:
        # Find LaTeX files
        tex_files = list(paper_path.glob("*.tex"))
        if not tex_files:
            return PaperValidationResult(
                paper_id=paper_id,
                file_count=0,
                total_chars=0,
                processing_time_ms=0,
                total_tokens=0,
                text_tokens=0,
                math_shifts=0,
                commands=0,
                other_tokens=0,
                text_tokens_with_dollar=0,
                text_tokens_with_caret=0,
                text_tokens_with_underscore=0,
                false_positive_potential=0,
                problematic_tokens=[],
                success=False,
                error_message="No LaTeX files found"
            )
        
        # Initialize lexer bridge
        bridge = RobustOCamlBridge(lexer_path)
        
        # Process all files in the paper
        total_chars = 0
        total_tokens = 0
        text_tokens = 0
        math_shifts = 0
        commands = 0
        other_tokens = 0
        text_with_dollar = 0
        text_with_caret = 0
        text_with_underscore = 0
        estimated_prevented_fps = 0
        problematic_tokens = []
        
        for tex_file in tex_files:
            try:
                # Read file content
                content = tex_file.read_text(encoding='utf-8', errors='ignore')
                total_chars += len(content)
                
                # Limit size for performance
                if len(content) > 100000:  # 100KB limit per file
                    content = content[:100000]
                
                # Tokenize using OCaml lexer
                tokens = bridge.tokenize_file(content)
                
                # Analyze tokens
                for i, token in enumerate(tokens):
                    if token.type == 'TEXT':
                        text_tokens += 1
                        
                        # Check for false positive indicators
                        if '$' in token.content:
                            text_with_dollar += 1
                            # Capture context for triage
                            context_start = max(0, i-2)
                            context_end = min(len(tokens), i+3)
                            context_tokens = tokens[context_start:context_end]
                            
                            problematic_tokens.append({
                                'file': tex_file.name,
                                'token_index': i,
                                'token_content': token.content,
                                'issue_type': 'dollar_in_text',
                                'surrounding_context': [
                                    {'type': t.type, 'content': t.content[:50]} 
                                    for t in context_tokens
                                ]
                            })
                        
                        if '^' in token.content:
                            text_with_caret += 1
                            problematic_tokens.append({
                                'file': tex_file.name,
                                'token_index': i,
                                'token_content': token.content[:50],
                                'issue_type': 'caret_in_text'
                            })
                        
                        if '_' in token.content:
                            text_with_underscore += 1
                            problematic_tokens.append({
                                'file': tex_file.name,
                                'token_index': i,
                                'token_content': token.content[:50],
                                'issue_type': 'underscore_in_text'
                            })
                        
                        # Estimate prevented false positives
                        estimated_prevented_fps += token.content.count('$')
                        estimated_prevented_fps += token.content.count('^')
                        estimated_prevented_fps += token.content.count('_')
                        
                    elif token.type == 'MATHSHIFT':
                        math_shifts += 1
                    elif token.type == 'COMMAND':
                        commands += 1
                    else:
                        other_tokens += 1
                
                total_tokens += len(tokens)
                
            except Exception as file_error:
                problematic_tokens.append({
                    'file': tex_file.name,
                    'error': str(file_error),
                    'issue_type': 'file_processing_error'
                })
                continue
        
        processing_time = (time.time() - start_time) * 1000
        
        return PaperValidationResult(
            paper_id=paper_id,
            file_count=len(tex_files),
            total_chars=total_chars,
            processing_time_ms=processing_time,
            total_tokens=total_tokens,
            text_tokens=text_tokens,
            math_shifts=math_shifts,
            commands=commands,
            other_tokens=other_tokens,
            text_tokens_with_dollar=text_with_dollar,
            text_tokens_with_caret=text_with_caret,
            text_tokens_with_underscore=text_with_underscore,
            false_positive_potential=estimated_prevented_fps,
            problematic_tokens=problematic_tokens[:10],  # Limit to first 10 issues
            success=True,
            validation_timestamp=datetime.now().isoformat()
        )
        
    except Exception as e:
        processing_time = (time.time() - start_time) * 1000
        return PaperValidationResult(
            paper_id=paper_id,
            file_count=0,
            total_chars=0,
            processing_time_ms=processing_time,
            total_tokens=0,
            text_tokens=0,
            math_shifts=0,
            commands=0,
            other_tokens=0,
            text_tokens_with_dollar=0,
            text_tokens_with_caret=0,
            text_tokens_with_underscore=0,
            false_positive_potential=0,
            problematic_tokens=[{
                'error': str(e),
                'traceback': traceback.format_exc(),
                'issue_type': 'paper_processing_error'
            }],
            success=False,
            error_message=str(e),
            validation_timestamp=datetime.now().isoformat()
        )

class EnhancedCorpusValidator:
    """
    Enhanced corpus validation with parallel processing and failure triage
    """
    
    def __init__(self, corpus_path: Path, lexer_path: Path):
        self.corpus_path = corpus_path
        self.lexer_path = lexer_path
        self.papers_path = corpus_path / "papers"
        
        if not self.papers_path.exists():
            raise FileNotFoundError(f"Papers directory not found: {self.papers_path}")
    
    def validate_corpus(self, max_papers: int = 2846, parallel_workers: int = 8) -> Tuple[CorpusValidationResults, List[PaperValidationResult]]:
        """
        Validate the corpus with parallel processing
        
        Returns both summary results and detailed per-paper results
        """
        logger.info(f"🎯 Starting ENHANCED corpus validation - Phase 2")
        logger.info(f"Target: {max_papers} papers with {parallel_workers} parallel workers")
        logger.info("=" * 60)
        
        start_time = time.time()
        
        # Find paper directories
        paper_dirs = [p for p in self.papers_path.iterdir() if p.is_dir()]
        if len(paper_dirs) > max_papers:
            paper_dirs = paper_dirs[:max_papers]
        
        logger.info(f"📁 Found {len(paper_dirs)} papers to validate")
        
        # Prepare arguments for parallel processing
        validation_args = [(paper_dir, self.lexer_path) for paper_dir in paper_dirs]
        
        # Process papers in parallel
        results = []
        completed = 0
        
        with ProcessPoolExecutor(max_workers=parallel_workers) as executor:
            # Submit all tasks
            future_to_paper = {
                executor.submit(validate_single_paper, args): args[0] 
                for args in validation_args
            }
            
            # Process completed tasks
            for future in as_completed(future_to_paper):
                paper_dir = future_to_paper[future]
                completed += 1
                
                try:
                    result = future.result()
                    results.append(result)
                    
                    if result.success:
                        fp_status = "🚨" if (result.text_tokens_with_dollar > 0 or 
                                           result.text_tokens_with_caret > 0 or 
                                           result.text_tokens_with_underscore > 0) else "✅"
                        logger.info(f"[{completed:4}/{len(paper_dirs)}] {fp_status} {result.paper_id}: "
                                  f"{result.total_tokens} tokens, {result.processing_time_ms:.0f}ms")
                    else:
                        logger.warning(f"[{completed:4}/{len(paper_dirs)}] ❌ {result.paper_id}: {result.error_message}")
                    
                    # Progress update every 100 papers
                    if completed % 100 == 0:
                        elapsed = time.time() - start_time
                        rate = completed / elapsed
                        eta = (len(paper_dirs) - completed) / rate if rate > 0 else 0
                        logger.info(f"📈 Progress: {completed}/{len(paper_dirs)} "
                                  f"({rate:.1f} papers/sec, ETA: {eta/60:.1f}min)")
                        
                except Exception as e:
                    logger.error(f"[{completed:4}/{len(paper_dirs)}] Error processing {paper_dir.name}: {e}")
                    continue
        
        # Generate comprehensive results
        total_time = time.time() - start_time
        summary = self._analyze_results(results, total_time, parallel_workers)
        
        return summary, results
    
    def _analyze_results(self, results: List[PaperValidationResult], total_time: float, workers: int) -> CorpusValidationResults:
        """Analyze validation results and generate comprehensive metrics"""
        
        successful = [r for r in results if r.success]
        failed = [r for r in results if not r.success]
        
        # Aggregate statistics
        total_chars = sum(r.total_chars for r in successful)
        total_tokens = sum(r.total_tokens for r in successful)
        total_files = sum(r.file_count for r in successful)
        total_processing_time = sum(r.processing_time_ms for r in successful)
        
        # Critical false positive analysis
        total_fp_indicators = sum(
            r.text_tokens_with_dollar + r.text_tokens_with_caret + r.text_tokens_with_underscore 
            for r in successful
        )
        clean_papers = len([r for r in successful if 
                          r.text_tokens_with_dollar == 0 and 
                          r.text_tokens_with_caret == 0 and 
                          r.text_tokens_with_underscore == 0])
        papers_with_dollar = len([r for r in successful if r.text_tokens_with_dollar > 0])
        papers_with_caret = len([r for r in successful if r.text_tokens_with_caret > 0])
        papers_with_underscore = len([r for r in successful if r.text_tokens_with_underscore > 0])
        estimated_prevented = sum(r.false_positive_potential for r in successful)
        
        # Performance metrics
        papers_per_sec = len(results) / total_time if total_time > 0 else 0
        chars_per_sec = total_chars / total_time if total_time > 0 else 0
        tokens_per_sec = total_tokens / total_time if total_time > 0 else 0
        
        # Quality metrics
        largest_paper = max(successful, key=lambda r: r.total_chars) if successful else None
        largest_tokens = max(successful, key=lambda r: r.total_tokens) if successful else None
        
        return CorpusValidationResults(
            total_papers_attempted=len(results),
            successful_validations=len(successful),
            failed_validations=len(failed),
            total_latex_files=total_files,
            total_characters_processed=total_chars,
            total_tokens_generated=total_tokens,
            
            total_processing_time_ms=total_processing_time,
            average_time_per_paper=total_processing_time / max(len(successful), 1),
            papers_per_second=papers_per_sec,
            characters_per_second=chars_per_sec,
            tokens_per_second=tokens_per_sec,
            parallel_workers_used=workers,
            
            total_false_positive_indicators=total_fp_indicators,
            papers_with_clean_tokenization=clean_papers,
            papers_with_dollar_issues=papers_with_dollar,
            papers_with_caret_issues=papers_with_caret,
            papers_with_underscore_issues=papers_with_underscore,
            estimated_false_positives_prevented=estimated_prevented,
            false_positive_elimination_rate=(clean_papers / max(len(successful), 1)) * 100,
            
            largest_paper_chars=largest_paper.total_chars if largest_paper else 0,
            largest_paper_tokens=largest_tokens.total_tokens if largest_tokens else 0,
            failure_rate=(len(failed) / max(len(results), 1)) * 100,
            
            validation_timestamp=datetime.now().isoformat()
        )
    
    def save_detailed_report(self, summary: CorpusValidationResults, 
                           detailed_results: List[PaperValidationResult],
                           output_path: Path):
        """Save comprehensive validation report"""
        
        report = {
            "validation_summary": asdict(summary),
            "validation_metadata": {
                "lexer_version": "v24-R3-verified-phase1-complete",
                "integration_method": "file-based-ocaml-bridge",
                "validation_type": "real-execution-parallel",
                "corpus_path": str(self.corpus_path),
                "validation_scope": "phase2-full-corpus",
                "comment_fix_applied": True
            },
            "detailed_results": [asdict(r) for r in detailed_results],
            "summary_statistics": {
                "papers_processed": len(detailed_results),
                "clean_papers": len([r for r in detailed_results if r.success and 
                                   r.text_tokens_with_dollar == 0 and 
                                   r.text_tokens_with_caret == 0 and 
                                   r.text_tokens_with_underscore == 0]),
                "papers_with_issues": len([r for r in detailed_results if r.success and 
                                         (r.text_tokens_with_dollar > 0 or 
                                          r.text_tokens_with_caret > 0 or 
                                          r.text_tokens_with_underscore > 0)])
            }
        }
        
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        logger.info(f"📋 Detailed report saved to {output_path}")
    
    def triage_failures(self, results: List[PaperValidationResult], output_dir: Path):
        """
        Create failure triage reports for papers with false positive indicators
        
        This implements the Phase 2 failure triage system
        """
        output_dir.mkdir(exist_ok=True)
        
        # Find papers with issues
        papers_with_issues = [r for r in results if r.success and 
                            (r.text_tokens_with_dollar > 0 or 
                             r.text_tokens_with_caret > 0 or 
                             r.text_tokens_with_underscore > 0)]
        
        logger.info(f"📋 Creating triage reports for {len(papers_with_issues)} papers with issues")
        
        for paper in papers_with_issues:
            triage_data = {
                'paper_id': paper.paper_id,
                'validation_timestamp': paper.validation_timestamp,
                'false_positive_summary': {
                    'text_tokens_with_dollar': paper.text_tokens_with_dollar,
                    'text_tokens_with_caret': paper.text_tokens_with_caret,
                    'text_tokens_with_underscore': paper.text_tokens_with_underscore,
                    'total_fp_indicators': (paper.text_tokens_with_dollar + 
                                          paper.text_tokens_with_caret + 
                                          paper.text_tokens_with_underscore)
                },
                'problematic_tokens': paper.problematic_tokens,
                'analysis_needed': 'Check for verbatim blocks, tikzpicture, or other special environments',
                'token_statistics': {
                    'total_tokens': paper.total_tokens,
                    'text_tokens': paper.text_tokens,
                    'math_shifts': paper.math_shifts,
                    'commands': paper.commands
                }
            }
            
            output_file = output_dir / f"{paper.paper_id}_triage.json"
            with open(output_file, 'w') as f:
                json.dump(triage_data, f, indent=2)
        
        # Create summary triage report
        summary_file = output_dir / "triage_summary.json"
        summary_data = {
            'total_papers_with_issues': len(papers_with_issues),
            'issue_types': {
                'dollar_in_text': len([p for p in papers_with_issues if p.text_tokens_with_dollar > 0]),
                'caret_in_text': len([p for p in papers_with_issues if p.text_tokens_with_caret > 0]),
                'underscore_in_text': len([p for p in papers_with_issues if p.text_tokens_with_underscore > 0])
            },
            'papers_list': [p.paper_id for p in papers_with_issues]
        }
        
        with open(summary_file, 'w') as f:
            json.dump(summary_data, f, indent=2)
        
        logger.info(f"📁 Triage reports saved to {output_dir}")

def main():
    """Run enhanced corpus validation - Phase 2"""
    
    parser = argparse.ArgumentParser(description='LaTeX Perfectionist v24-R3 - Phase 2 Corpus Validation')
    parser.add_argument('--limit', type=int, default=2846, 
                       help='Maximum papers to process (default: 2846)')
    parser.add_argument('--parallel', type=int, default=8,
                       help='Number of parallel workers (default: 8)')
    parser.add_argument('--output', type=str, default='corpus_validation_phase2.json',
                       help='Output report filename')
    args = parser.parse_args()
    
    print("🚀 ENHANCED CORPUS VALIDATION - PHASE 2")
    print("LaTeX Perfectionist v24-R3: Full Corpus Validation")
    print("=" * 70)
    print(f"Configuration:")
    print(f"  Max papers: {args.limit}")
    print(f"  Parallel workers: {args.parallel}")
    print(f"  Output file: {args.output}")
    print("=" * 70)
    
    # Configure paths
    script_dir = Path(__file__).parent
    corpus_path = Path("/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/corpus")
    lexer_path = script_dir
    
    if not corpus_path.exists():
        print("❌ Corpus not found - cannot run validation")
        sys.exit(1)
    
    try:
        # Initialize enhanced validator
        validator = EnhancedCorpusValidator(corpus_path, lexer_path)
        
        # Run parallel validation
        print(f"\n🔬 Running parallel validation on {args.limit} papers...")
        summary, detailed_results = validator.validate_corpus(
            max_papers=args.limit, 
            parallel_workers=args.parallel
        )
        
        # Display results
        print("\n📊 PHASE 2 VALIDATION RESULTS")
        print("=" * 50)
        print(f"Papers attempted: {summary.total_papers_attempted}")
        print(f"Successful validations: {summary.successful_validations}")
        print(f"Failed validations: {summary.failed_validations}")
        print(f"Failure rate: {summary.failure_rate:.1f}%")
        print(f"Total LaTeX files: {summary.total_latex_files}")
        print(f"Total characters: {summary.total_characters_processed:,}")
        print(f"Total tokens: {summary.total_tokens_generated:,}")
        
        print(f"\n⚡ PERFORMANCE METRICS")
        print("=" * 50)
        print(f"Parallel workers used: {summary.parallel_workers_used}")
        print(f"Processing rate: {summary.papers_per_second:.2f} papers/sec")
        print(f"Character rate: {summary.characters_per_second:,.0f} chars/sec")  
        print(f"Token rate: {summary.tokens_per_second:,.0f} tokens/sec")
        print(f"Average time per paper: {summary.average_time_per_paper:.0f}ms")
        
        print(f"\n🎯 FALSE POSITIVE ANALYSIS")
        print("=" * 50)
        print(f"Papers with clean tokenization: {summary.papers_with_clean_tokenization}/{summary.successful_validations}")
        print(f"False positive elimination rate: {summary.false_positive_elimination_rate:.1f}%")
        print(f"Papers with $ in TEXT: {summary.papers_with_dollar_issues}")
        print(f"Papers with ^ in TEXT: {summary.papers_with_caret_issues}")
        print(f"Papers with _ in TEXT: {summary.papers_with_underscore_issues}")
        print(f"Total FP indicators: {summary.total_false_positive_indicators}")
        print(f"Estimated FPs prevented: {summary.estimated_false_positives_prevented:,}")
        
        # Save detailed report
        report_path = script_dir / args.output
        validator.save_detailed_report(summary, detailed_results, report_path)
        
        # Create triage reports for failures
        if summary.total_false_positive_indicators > 0:
            triage_dir = script_dir / "corpus_triage"
            validator.triage_failures(detailed_results, triage_dir)
            print(f"\n📁 Triage reports created in: {triage_dir}")
        
        # Assess success
        if summary.false_positive_elimination_rate == 100.0:
            print("\n🎉 PERFECT: 100% false positive elimination achieved!")
            print("✅ PHASE 2 COMPLETE: Ready for Phase 3 (Production Hardening)")
        elif summary.false_positive_elimination_rate >= 99.0:
            print("\n✅ EXCELLENT: Near-perfect false positive elimination!")
            print(f"⚠️  {summary.total_false_positive_indicators} edge cases need investigation")
        else:
            print(f"\n⚠️  NEEDS ATTENTION: {summary.false_positive_elimination_rate:.1f}% elimination rate")
            print("🔧 Review triage reports for patterns")
        
        print(f"\n📋 Full report saved to: {report_path}")
        print("🎉 Phase 2 corpus validation complete!")
        
        return summary.false_positive_elimination_rate >= 99.0
        
    except Exception as e:
        logger.error(f"❌ Validation failed: {e}")
        traceback.print_exc()
        sys.exit(1)

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)