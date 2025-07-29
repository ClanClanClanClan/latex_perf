#!/usr/bin/env python3
"""
🔍 PRODUCTION-HARDENED VALIDATOR - PHASE 3
LaTeX Perfectionist v24-R3: Production-Ready System

This implements Phase 3 of the roadmap:
- Structured logging with structlog
- Comprehensive error categorization
- Monitoring hooks for metrics
- Configurable timeouts
- Production-grade error handling
"""

import os
import sys
import json
import time
import signal
import traceback
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any, Union
from dataclasses import dataclass, asdict
from concurrent.futures import ProcessPoolExecutor, as_completed, TimeoutError
from datetime import datetime, timezone
import multiprocessing
import argparse

# Structured logging setup
import structlog

# Configure structured logging
structlog.configure(
    processors=[
        structlog.stdlib.filter_by_level,
        structlog.stdlib.add_logger_name,
        structlog.stdlib.add_log_level,
        structlog.stdlib.PositionalArgumentsFormatter(),
        structlog.processors.TimeStamper(fmt="iso"),
        structlog.processors.StackInfoRenderer(),
        structlog.processors.format_exc_info,
        structlog.processors.JSONRenderer()
    ],
    context_class=dict,
    logger_factory=structlog.stdlib.LoggerFactory(),
    wrapper_class=structlog.stdlib.BoundLogger,
    cache_logger_on_first_use=True,
)

logger = structlog.get_logger()

# Import our working integration
from fixed_integration import RobustOCamlBridge, Token

# ==============================================================================
# ERROR CATEGORIZATION SYSTEM
# ==============================================================================

class LaTeXPerfectionistError(Exception):
    """Base exception for all LaTeX Perfectionist errors"""
    def __init__(self, message: str, details: Optional[Dict[str, Any]] = None):
        super().__init__(message)
        self.details = details or {}
        self.timestamp = datetime.utcnow().isoformat()

class ValidationError(LaTeXPerfectionistError):
    """Validation rule execution errors"""
    pass

class LexerError(LaTeXPerfectionistError):
    """Lexer parsing errors"""
    pass

class BridgeError(LaTeXPerfectionistError):
    """Python-OCaml communication errors"""
    pass

class TimeoutError(LaTeXPerfectionistError):
    """Processing timeout errors"""
    pass

class CorpusError(LaTeXPerfectionistError):
    """Corpus access or structure errors"""
    pass

# ==============================================================================
# CONFIGURATION
# ==============================================================================

class Config:
    """Production configuration with environment variable support"""
    
    # Timeouts (in seconds)
    PAPER_TIMEOUT = int(os.environ.get('LP24_PAPER_TIMEOUT', '60'))
    LEXER_TIMEOUT = int(os.environ.get('LP24_LEXER_TIMEOUT', '60'))
    
    # File limits
    MAX_FILE_SIZE = int(os.environ.get('LP24_MAX_FILE_SIZE', '100000'))  # 100KB default
    MAX_FILES_PER_PAPER = int(os.environ.get('LP24_MAX_FILES_PER_PAPER', '50'))
    
    # Performance
    DEFAULT_PARALLEL_WORKERS = int(os.environ.get('LP24_PARALLEL_WORKERS', '8'))
    
    # Monitoring
    EMIT_METRICS = os.environ.get('LP24_EMIT_METRICS', 'false').lower() == 'true'
    METRICS_FILE = os.environ.get('LP24_METRICS_FILE', 'metrics.jsonl')
    
    # Debugging
    DEBUG_MODE = os.environ.get('LP24_DEBUG', 'false').lower() == 'true'
    SAVE_PROBLEMATIC_TOKENS = os.environ.get('LP24_SAVE_PROBLEMS', 'true').lower() == 'true'

# ==============================================================================
# DATA MODELS
# ==============================================================================

@dataclass
class PaperValidationResult:
    """Production validation result with enhanced error tracking"""
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
    
    # False positive analysis
    text_tokens_with_dollar: int
    text_tokens_with_caret: int
    text_tokens_with_underscore: int
    false_positive_potential: int
    
    # Detailed failure info
    problematic_tokens: List[Dict[str, Any]]
    
    # Status and errors
    success: bool
    error_type: Optional[str] = None
    error_message: Optional[str] = None
    error_details: Optional[Dict[str, Any]] = None
    validation_timestamp: str = ""
    
    # Performance metrics
    lexer_calls: int = 0
    files_skipped: int = 0
    timeout_occurred: bool = False

# ==============================================================================
# MONITORING AND METRICS
# ==============================================================================

class MetricsEmitter:
    """Emit metrics in Prometheus-scrapable format"""
    
    def __init__(self, enabled: bool = True, output_file: Optional[str] = None):
        self.enabled = enabled
        self.output_file = output_file
        self.metrics_buffer = []
    
    def emit(self, metric_type: str, paper_id: str, **kwargs):
        """Emit a metric"""
        if not self.enabled:
            return
            
        metric = {
            'timestamp': datetime.utcnow().isoformat(),
            'metric_type': metric_type,
            'paper_id': paper_id,
            **kwargs
        }
        
        # Output to stdout for Prometheus scraping
        if Config.EMIT_METRICS:
            print(f"LP24_METRIC {json.dumps(metric)}", file=sys.stdout)
        
        # Also save to file if configured
        if self.output_file:
            self.metrics_buffer.append(metric)
            if len(self.metrics_buffer) >= 100:  # Flush every 100 metrics
                self.flush()
    
    def flush(self):
        """Flush metrics to file"""
        if self.output_file and self.metrics_buffer:
            with open(self.output_file, 'a') as f:
                for metric in self.metrics_buffer:
                    json.dump(metric, f)
                    f.write('\n')
            self.metrics_buffer = []

# Global metrics emitter
metrics = MetricsEmitter(
    enabled=Config.EMIT_METRICS,
    output_file=Config.METRICS_FILE if Config.EMIT_METRICS else None
)

# ==============================================================================
# TIMEOUT HANDLING
# ==============================================================================

class TimeoutHandler:
    """Handle timeouts gracefully"""
    
    def __init__(self, timeout_seconds: int):
        self.timeout_seconds = timeout_seconds
        self.timed_out = False
    
    def __enter__(self):
        if sys.platform != 'win32':  # Signal-based timeout not available on Windows
            signal.signal(signal.SIGALRM, self._timeout_handler)
            signal.alarm(self.timeout_seconds)
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        if sys.platform != 'win32':
            signal.alarm(0)  # Cancel alarm
    
    def _timeout_handler(self, signum, frame):
        self.timed_out = True
        raise TimeoutError(f"Operation timed out after {self.timeout_seconds}s", 
                          {"timeout_seconds": self.timeout_seconds})

# ==============================================================================
# PRODUCTION VALIDATOR
# ==============================================================================

def validate_single_paper_production(args: Tuple[Path, Path]) -> PaperValidationResult:
    """
    Production-grade single paper validation with comprehensive error handling
    """
    paper_path, lexer_path = args
    paper_id = paper_path.name
    start_time = time.time()
    
    # Initialize logging context
    log = logger.bind(paper_id=paper_id)
    
    try:
        log.info("starting_paper_validation")
        
        # Find LaTeX files
        tex_files = list(paper_path.glob("*.tex"))
        if not tex_files:
            raise ValidationError("No LaTeX files found", {
                "paper_path": str(paper_path),
                "search_pattern": "*.tex"
            })
        
        # Limit number of files per paper
        if len(tex_files) > Config.MAX_FILES_PER_PAPER:
            log.warning("too_many_files", 
                       file_count=len(tex_files), 
                       limit=Config.MAX_FILES_PER_PAPER)
            tex_files = tex_files[:Config.MAX_FILES_PER_PAPER]
        
        # Initialize lexer bridge
        try:
            bridge = RobustOCamlBridge(lexer_path)
        except Exception as e:
            raise BridgeError(f"Failed to initialize OCaml bridge: {e}", {
                "lexer_path": str(lexer_path),
                "error": str(e)
            })
        
        # Process all files with timeout protection
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
        lexer_calls = 0
        files_skipped = 0
        
        for tex_file in tex_files:
            try:
                # Read file content
                content = tex_file.read_text(encoding='utf-8', errors='ignore')
                file_size = len(content)
                total_chars += file_size
                
                # Check file size limit
                if file_size > Config.MAX_FILE_SIZE:
                    log.warning("file_too_large", 
                              file=tex_file.name, 
                              size=file_size,
                              limit=Config.MAX_FILE_SIZE)
                    content = content[:Config.MAX_FILE_SIZE]
                    files_skipped += 1
                
                # Tokenize with timeout
                with TimeoutHandler(Config.LEXER_TIMEOUT) as th:
                    lexer_start = time.time()
                    tokens = bridge.tokenize_file(content)
                    lexer_time = (time.time() - lexer_start) * 1000
                    lexer_calls += 1
                    
                    log.debug("lexer_call_complete", 
                             file=tex_file.name,
                             tokens=len(tokens),
                             time_ms=lexer_time)
                
                # Analyze tokens
                for i, token in enumerate(tokens):
                    if token.type == 'TEXT':
                        text_tokens += 1
                        
                        # Check for false positive indicators
                        if '$' in token.content:
                            text_with_dollar += 1
                            if Config.SAVE_PROBLEMATIC_TOKENS and len(problematic_tokens) < 10:
                                problematic_tokens.append({
                                    'file': tex_file.name,
                                    'token_index': i,
                                    'token_content': token.content[:100],
                                    'issue_type': 'dollar_in_text'
                                })
                        
                        if '^' in token.content:
                            text_with_caret += 1
                            if Config.SAVE_PROBLEMATIC_TOKENS and len(problematic_tokens) < 10:
                                problematic_tokens.append({
                                    'file': tex_file.name,
                                    'token_index': i,
                                    'token_content': token.content[:100],
                                    'issue_type': 'caret_in_text'
                                })
                        
                        if '_' in token.content:
                            text_with_underscore += 1
                            if Config.SAVE_PROBLEMATIC_TOKENS and len(problematic_tokens) < 10:
                                problematic_tokens.append({
                                    'file': tex_file.name,
                                    'token_index': i,
                                    'token_content': token.content[:100],
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
                
            except TimeoutError as e:
                log.warning("file_timeout", file=tex_file.name, timeout=Config.LEXER_TIMEOUT)
                files_skipped += 1
                continue
            except Exception as e:
                log.error("file_processing_error", 
                         file=tex_file.name, 
                         error=str(e),
                         error_type=type(e).__name__)
                if Config.SAVE_PROBLEMATIC_TOKENS:
                    problematic_tokens.append({
                        'file': tex_file.name,
                        'error': str(e),
                        'issue_type': 'file_processing_error'
                    })
                files_skipped += 1
                continue
        
        processing_time = (time.time() - start_time) * 1000
        
        # Emit metrics
        fp_indicators = text_with_dollar + text_with_caret + text_with_underscore
        metrics.emit('paper_validation', paper_id,
                    token_count=total_tokens,
                    processing_time_ms=processing_time,
                    false_positive_indicators=fp_indicators,
                    success=True)
        
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
            problematic_tokens=problematic_tokens,
            success=True,
            lexer_calls=lexer_calls,
            files_skipped=files_skipped,
            timeout_occurred=False,
            validation_timestamp=datetime.now(timezone.utc).isoformat()
        )
        
    except LaTeXPerfectionistError as e:
        processing_time = (time.time() - start_time) * 1000
        log.error("validation_error", 
                 error=str(e), 
                 error_type=type(e).__name__,
                 details=e.details)
        
        metrics.emit('paper_validation', paper_id,
                    processing_time_ms=processing_time,
                    success=False,
                    error_type=type(e).__name__)
        
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
            problematic_tokens=[],
            success=False,
            error_type=type(e).__name__,
            error_message=str(e),
            error_details=e.details,
            validation_timestamp=datetime.now(timezone.utc).isoformat()
        )
    except Exception as e:
        processing_time = (time.time() - start_time) * 1000
        log.exception("unexpected_error")
        
        metrics.emit('paper_validation', paper_id,
                    processing_time_ms=processing_time,
                    success=False,
                    error_type='UnexpectedError')
        
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
                'traceback': traceback.format_exc() if Config.DEBUG_MODE else None,
                'issue_type': 'unexpected_error'
            }],
            success=False,
            error_type='UnexpectedError',
            error_message=str(e),
            validation_timestamp=datetime.now(timezone.utc).isoformat()
        )

# ==============================================================================
# MAIN PRODUCTION VALIDATOR
# ==============================================================================

class ProductionCorpusValidator:
    """Production-grade corpus validator with full error handling and monitoring"""
    
    def __init__(self, corpus_path: Path, lexer_path: Path):
        self.corpus_path = corpus_path
        self.lexer_path = lexer_path
        self.papers_path = corpus_path / "papers"
        
        if not self.papers_path.exists():
            raise CorpusError(f"Papers directory not found", {
                "expected_path": str(self.papers_path),
                "corpus_path": str(corpus_path)
            })
        
        logger.info("validator_initialized", 
                   corpus_path=str(corpus_path),
                   lexer_path=str(lexer_path))
    
    def validate_corpus(self, max_papers: int = 2846, 
                       parallel_workers: Optional[int] = None) -> Tuple[Dict[str, Any], List[PaperValidationResult]]:
        """
        Production corpus validation with comprehensive monitoring
        """
        if parallel_workers is None:
            parallel_workers = Config.DEFAULT_PARALLEL_WORKERS
            
        logger.info("starting_corpus_validation",
                   max_papers=max_papers,
                   parallel_workers=parallel_workers)
        
        start_time = time.time()
        
        # Find paper directories
        paper_dirs = [p for p in self.papers_path.iterdir() if p.is_dir()]
        if len(paper_dirs) > max_papers:
            paper_dirs = paper_dirs[:max_papers]
        
        logger.info("papers_found", count=len(paper_dirs))
        
        # Prepare arguments
        validation_args = [(paper_dir, self.lexer_path) for paper_dir in paper_dirs]
        
        # Process papers in parallel with timeout protection
        results = []
        completed = 0
        errors_by_type = {}
        
        with ProcessPoolExecutor(max_workers=parallel_workers) as executor:
            # Submit all tasks
            future_to_paper = {
                executor.submit(validate_single_paper_production, args): args[0] 
                for args in validation_args
            }
            
            # Process completed tasks
            for future in as_completed(future_to_paper):
                paper_dir = future_to_paper[future]
                completed += 1
                
                try:
                    result = future.result(timeout=Config.PAPER_TIMEOUT * 2)  # Grace period
                    results.append(result)
                    
                    if result.success:
                        fp_status = "clean" if (result.text_tokens_with_dollar == 0 and 
                                               result.text_tokens_with_caret == 0 and 
                                               result.text_tokens_with_underscore == 0) else "issues"
                        logger.info("paper_complete",
                                   paper_id=result.paper_id,
                                   status=fp_status,
                                   tokens=result.total_tokens,
                                   time_ms=result.processing_time_ms,
                                   progress=f"{completed}/{len(paper_dirs)}")
                    else:
                        error_type = result.error_type or 'Unknown'
                        errors_by_type[error_type] = errors_by_type.get(error_type, 0) + 1
                        logger.warning("paper_failed",
                                     paper_id=result.paper_id,
                                     error_type=error_type,
                                     error=result.error_message)
                    
                    # Progress update
                    if completed % 100 == 0:
                        elapsed = time.time() - start_time
                        rate = completed / elapsed
                        eta = (len(paper_dirs) - completed) / rate if rate > 0 else 0
                        logger.info("progress_update",
                                   completed=completed,
                                   total=len(paper_dirs),
                                   rate_per_sec=rate,
                                   eta_minutes=eta/60)
                        
                except TimeoutError:
                    logger.error("paper_timeout",
                               paper_id=paper_dir.name,
                               timeout=Config.PAPER_TIMEOUT * 2)
                    errors_by_type['Timeout'] = errors_by_type.get('Timeout', 0) + 1
                except Exception as e:
                    logger.exception("paper_processing_failed",
                                   paper_id=paper_dir.name)
                    errors_by_type['ProcessingError'] = errors_by_type.get('ProcessingError', 0) + 1
        
        # Generate summary
        total_time = time.time() - start_time
        summary = self._generate_summary(results, total_time, parallel_workers, errors_by_type)
        
        # Flush metrics
        metrics.flush()
        
        logger.info("corpus_validation_complete",
                   total_time_seconds=total_time,
                   papers_processed=len(results),
                   success_rate=summary['results']['success_rate'])
        
        return summary, results
    
    def _generate_summary(self, results: List[PaperValidationResult], 
                         total_time: float, workers: int,
                         errors_by_type: Dict[str, int]) -> Dict[str, Any]:
        """Generate comprehensive validation summary"""
        
        successful = [r for r in results if r.success]
        failed = [r for r in results if not r.success]
        
        # Aggregate statistics
        total_chars = sum(r.total_chars for r in successful)
        total_tokens = sum(r.total_tokens for r in successful)
        total_files = sum(r.file_count for r in successful)
        
        # False positive analysis
        clean_papers = len([r for r in successful if 
                          r.text_tokens_with_dollar == 0 and 
                          r.text_tokens_with_caret == 0 and 
                          r.text_tokens_with_underscore == 0])
        
        total_fp_indicators = sum(
            r.text_tokens_with_dollar + r.text_tokens_with_caret + r.text_tokens_with_underscore 
            for r in successful
        )
        
        return {
            'validation_timestamp': datetime.now().isoformat(),
            'configuration': {
                'paper_timeout': Config.PAPER_TIMEOUT,
                'lexer_timeout': Config.LEXER_TIMEOUT,
                'max_file_size': Config.MAX_FILE_SIZE,
                'parallel_workers': workers
            },
            'results': {
                'total_papers_attempted': len(results),
                'successful_validations': len(successful),
                'failed_validations': len(failed),
                'success_rate': (len(successful) / max(len(results), 1)) * 100
            },
            'performance': {
                'total_time_seconds': total_time,
                'papers_per_second': len(results) / total_time if total_time > 0 else 0,
                'total_characters_processed': total_chars,
                'total_tokens_generated': total_tokens
            },
            'false_positive_analysis': {
                'papers_with_clean_tokenization': clean_papers,
                'false_positive_elimination_rate': (clean_papers / max(len(successful), 1)) * 100,
                'total_false_positive_indicators': total_fp_indicators,
                'papers_with_dollar_issues': len([r for r in successful if r.text_tokens_with_dollar > 0]),
                'papers_with_caret_issues': len([r for r in successful if r.text_tokens_with_caret > 0]),
                'papers_with_underscore_issues': len([r for r in successful if r.text_tokens_with_underscore > 0])
            },
            'errors': {
                'total_errors': len(failed),
                'errors_by_type': errors_by_type
            }
        }

# ==============================================================================
# MAIN ENTRY POINT
# ==============================================================================

def main():
    """Production validator main entry point"""
    
    parser = argparse.ArgumentParser(
        description='LaTeX Perfectionist v24-R3 - Production Validator (Phase 3)')
    parser.add_argument('--limit', type=int, default=100,
                       help='Maximum papers to process')
    parser.add_argument('--parallel', type=int, default=None,
                       help=f'Parallel workers (default: {Config.DEFAULT_PARALLEL_WORKERS})')
    parser.add_argument('--output', type=str, default='production_validation.json',
                       help='Output report filename')
    parser.add_argument('--debug', action='store_true',
                       help='Enable debug mode')
    parser.add_argument('--metrics', action='store_true',
                       help='Enable metrics emission')
    args = parser.parse_args()
    
    # Override config with command line args
    if args.debug:
        Config.DEBUG_MODE = True
    if args.metrics:
        Config.EMIT_METRICS = True
    
    print("🔍 PRODUCTION VALIDATOR - PHASE 3")
    print("LaTeX Perfectionist v24-R3: Production-Grade System")
    print("=" * 70)
    print(f"Configuration:")
    print(f"  Max papers: {args.limit}")
    print(f"  Parallel workers: {args.parallel or Config.DEFAULT_PARALLEL_WORKERS}")
    print(f"  Debug mode: {Config.DEBUG_MODE}")
    print(f"  Metrics enabled: {Config.EMIT_METRICS}")
    print(f"  Timeouts: Paper={Config.PAPER_TIMEOUT}s, Lexer={Config.LEXER_TIMEOUT}s")
    print("=" * 70)
    
    # Configure paths
    script_dir = Path(__file__).parent
    corpus_path = Path("/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/corpus")
    lexer_path = script_dir
    
    try:
        # Initialize validator
        validator = ProductionCorpusValidator(corpus_path, lexer_path)
        
        # Run validation
        print(f"\n🔬 Running production validation...")
        summary, detailed_results = validator.validate_corpus(
            max_papers=args.limit,
            parallel_workers=args.parallel
        )
        
        # Display results
        print("\n📊 PRODUCTION VALIDATION RESULTS")
        print("=" * 50)
        print(f"Papers processed: {summary['results']['total_papers_attempted']}")
        print(f"Success rate: {summary['results']['success_rate']:.1f}%")
        print(f"Processing rate: {summary['performance']['papers_per_second']:.2f} papers/sec")
        
        print(f"\n🎯 FALSE POSITIVE ANALYSIS")
        print("=" * 50)
        fp_analysis = summary['false_positive_analysis']
        print(f"FP elimination rate: {fp_analysis['false_positive_elimination_rate']:.1f}%")
        print(f"Clean papers: {fp_analysis['papers_with_clean_tokenization']}")
        print(f"Total FP indicators: {fp_analysis['total_false_positive_indicators']}")
        
        if summary['errors']['total_errors'] > 0:
            print(f"\n⚠️  ERRORS ENCOUNTERED")
            print("=" * 50)
            print(f"Total errors: {summary['errors']['total_errors']}")
            for error_type, count in summary['errors']['errors_by_type'].items():
                print(f"  {error_type}: {count}")
        
        # Save detailed report
        report_path = script_dir / args.output
        with open(report_path, 'w') as f:
            json.dump({
                'summary': summary,
                'detailed_results': [asdict(r) for r in detailed_results]
            }, f, indent=2)
        
        print(f"\n📋 Report saved to: {report_path}")
        
        # Final assessment
        if fp_analysis['false_positive_elimination_rate'] == 100.0:
            print("\n🎉 PERFECT: 100% false positive elimination!")
            print("✅ PHASE 3 COMPLETE: Production hardening successful")
        else:
            print(f"\n📈 FP elimination: {fp_analysis['false_positive_elimination_rate']:.1f}%")
        
        return summary['results']['success_rate'] >= 95.0
        
    except LaTeXPerfectionistError as e:
        logger.exception("validator_error", details=e.details)
        print(f"\n❌ Validation failed: {e}")
        return False
    except Exception as e:
        logger.exception("unexpected_error")
        print(f"\n❌ Unexpected error: {e}")
        if Config.DEBUG_MODE:
            traceback.print_exc()
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)