#!/usr/bin/env python3
"""
Enterprise Corpus Analysis Tool

Analyzes the 2,846 paper corpus + 1,015 quarantined papers
to understand structure and potential issues
"""

import json
import os
from pathlib import Path
from collections import defaultdict, Counter
from dataclasses import dataclass, asdict
from typing import Dict, List, Tuple, Optional
import argparse
import subprocess
import re
from tqdm import tqdm

@dataclass
class CorpusStats:
    total_papers: int
    quarantined_papers: int
    metadata_files: int
    ground_truth_files: int
    total_tex_files: int
    avg_tex_files_per_paper: float
    domain_distribution: Dict[str, int]
    file_size_distribution: Dict[str, int]
    compilation_success_rate: float
    estimated_issue_distribution: Dict[str, int]

@dataclass
class QuarantinedAnalysis:
    total_quarantined: int
    issue_categories: Dict[str, int]
    compilation_failure_types: Dict[str, int]
    potential_validator_targets: List[str]
    value_assessment: Dict[str, int]
    sample_issues: List[Dict]

class EnterpriseCorpusAnalyzer:
    def __init__(self, corpus_path: str):
        self.corpus_path = Path(corpus_path)
        self.papers_path = self.corpus_path / "papers"
        self.quarantined_path = self.corpus_path / "quarantined"
        self.metadata_path = self.corpus_path / "metadata"
        self.ground_truth_path = self.corpus_path / "ground_truth"
        
    def analyze_corpus_structure(self) -> CorpusStats:
        """Analyze the main corpus structure."""
        print("Analyzing corpus structure...")
        
        # Count papers
        paper_dirs = [d for d in self.papers_path.iterdir() if d.is_dir()] if self.papers_path.exists() else []
        total_papers = len(paper_dirs)
        
        # Count quarantined papers
        quarantined_dirs = [d for d in self.quarantined_path.iterdir() if d.is_dir()] if self.quarantined_path.exists() else []
        quarantined_papers = len(quarantined_dirs)
        
        # Count metadata files
        metadata_files = len([f for f in self.metadata_path.iterdir() if f.suffix == '.json']) if self.metadata_path.exists() else 0
        
        # Count ground truth files
        ground_truth_files = len([f for f in self.ground_truth_path.iterdir() if f.suffix == '.json']) if self.ground_truth_path.exists() else 0
        
        # Analyze tex files
        total_tex_files = 0
        domain_distribution = defaultdict(int)
        file_size_distribution = defaultdict(int)
        
        sample_size = min(100, total_papers)  # Analyze first 100 papers for stats
        
        for paper_dir in tqdm(paper_dirs[:sample_size], desc="Analyzing papers"):
            # Count tex files
            tex_files = list(paper_dir.glob("*.tex"))
            total_tex_files += len(tex_files)
            
            # Extract domain from paper ID (e.g., 2506.19274v1 -> math/physics)
            paper_id = paper_dir.name
            domain = self.extract_domain(paper_id)
            domain_distribution[domain] += 1
            
            # Analyze file sizes
            for tex_file in tex_files:
                try:
                    size = tex_file.stat().st_size
                    if size < 10000:
                        file_size_distribution["small"] += 1
                    elif size < 100000:
                        file_size_distribution["medium"] += 1
                    else:
                        file_size_distribution["large"] += 1
                except:
                    pass
        
        # Extrapolate to full corpus
        avg_tex_files = total_tex_files / sample_size if sample_size > 0 else 0
        
        # Estimate domain distribution for full corpus
        full_domain_distribution = {}
        for domain, count in domain_distribution.items():
            full_domain_distribution[domain] = int(count * total_papers / sample_size)
        
        # Estimate compilation success rate from enterprise corpus summary
        compilation_success_rate = self.get_compilation_success_rate()
        
        # Estimate issue distribution
        estimated_issues = self.estimate_issue_distribution(total_papers)
        
        return CorpusStats(
            total_papers=total_papers,
            quarantined_papers=quarantined_papers,
            metadata_files=metadata_files,
            ground_truth_files=ground_truth_files,
            total_tex_files=int(total_tex_files * total_papers / sample_size),
            avg_tex_files_per_paper=avg_tex_files,
            domain_distribution=full_domain_distribution,
            file_size_distribution=dict(file_size_distribution),
            compilation_success_rate=compilation_success_rate,
            estimated_issue_distribution=estimated_issues
        )
    
    def analyze_quarantined_papers(self) -> QuarantinedAnalysis:
        """Analyze the quarantined papers for potential issues."""
        print("Analyzing quarantined papers...")
        
        if not self.quarantined_path.exists():
            return QuarantinedAnalysis(
                total_quarantined=0,
                issue_categories={},
                compilation_failure_types={},
                potential_validator_targets=[],
                value_assessment={},
                sample_issues=[]
            )
        
        quarantined_dirs = [d for d in self.quarantined_path.iterdir() if d.is_dir()]
        total_quarantined = len(quarantined_dirs)
        
        issue_categories = defaultdict(int)
        compilation_failures = defaultdict(int)
        sample_issues = []
        
        # Analyze sample of quarantined papers
        sample_size = min(50, total_quarantined)
        
        for paper_dir in tqdm(quarantined_dirs[:sample_size], desc="Analyzing quarantined"):
            issues = self.analyze_quarantined_paper(paper_dir)
            
            for issue_type, count in issues.items():
                issue_categories[issue_type] += count
                
            # Sample interesting issues
            if len(sample_issues) < 10:
                sample_issues.append({
                    'paper_id': paper_dir.name,
                    'issues': dict(issues)
                })
        
        # Extrapolate to full quarantined corpus
        full_issue_categories = {}
        for category, count in issue_categories.items():
            full_issue_categories[category] = int(count * total_quarantined / sample_size)
        
        # Identify potential validator targets
        validator_targets = self.identify_validator_targets(issue_categories)
        
        # Assess value for testing
        value_assessment = {
            'high_value': sum(1 for issues in sample_issues if len(issues['issues']) > 3),
            'medium_value': sum(1 for issues in sample_issues if 1 <= len(issues['issues']) <= 3),
            'low_value': sum(1 for issues in sample_issues if len(issues['issues']) == 0)
        }
        
        return QuarantinedAnalysis(
            total_quarantined=total_quarantined,
            issue_categories=full_issue_categories,
            compilation_failure_types=dict(compilation_failures),
            potential_validator_targets=validator_targets,
            value_assessment=value_assessment,
            sample_issues=sample_issues
        )
    
    def analyze_quarantined_paper(self, paper_dir: Path) -> Dict[str, int]:
        """Analyze a single quarantined paper for issue types."""
        issues = defaultdict(int)
        
        # Find tex files
        tex_files = list(paper_dir.glob("*.tex"))
        
        for tex_file in tex_files:
            try:
                content = tex_file.read_text(encoding='utf-8', errors='ignore')
                
                # Check for common issues
                if '\"' in content:
                    issues['straight_quotes'] += content.count('\"')
                
                if '$$' in content:
                    issues['double_dollar'] += content.count('$$') // 2
                
                if '\\eqnarray' in content:
                    issues['eqnarray'] += content.count('\\eqnarray')
                
                if '\\begin{' in content and '\\end{' in content:
                    # Check for mismatched environments
                    begins = re.findall(r'\\begin\{([^}]+)\}', content)
                    ends = re.findall(r'\\end\{([^}]+)\}', content)
                    if len(begins) != len(ends):
                        issues['mismatched_environments'] += 1
                
                # Check for encoding issues
                if any(ord(c) > 127 for c in content):
                    issues['unicode_characters'] += 1
                
                # Check for very long lines
                lines = content.split('\n')
                long_lines = sum(1 for line in lines if len(line) > 100)
                if long_lines > 0:
                    issues['long_lines'] += long_lines
                
                # Check for missing packages
                if '\\usepackage' not in content:
                    issues['minimal_packages'] += 1
                
            except Exception as e:
                issues['read_errors'] += 1
        
        return dict(issues)
    
    def extract_domain(self, paper_id: str) -> str:
        """Extract domain from paper ID."""
        # ArXiv paper IDs: YYMM.NNNNN[vN]
        # This is a simplified domain extraction
        if paper_id.startswith('2506') or paper_id.startswith('2507'):
            return 'recent_arxiv'
        elif 'math' in paper_id.lower():
            return 'mathematics'
        elif 'cs' in paper_id.lower():
            return 'computer_science'
        elif 'physics' in paper_id.lower() or 'astro' in paper_id.lower():
            return 'physics'
        else:
            return 'other'
    
    def get_compilation_success_rate(self) -> float:
        """Get compilation success rate from enterprise corpus summary."""
        summary_file = self.corpus_path / "enterprise_corpus_summary.json"
        
        if summary_file.exists():
            try:
                with open(summary_file) as f:
                    summary = json.load(f)
                    return summary.get('validation_rate', 0.0)
            except:
                pass
        
        return 0.85  # Default estimate
    
    def estimate_issue_distribution(self, total_papers: int) -> Dict[str, int]:
        """Estimate issue distribution across the corpus."""
        # Based on typical LaTeX paper patterns
        estimates = {
            'TYPO-001': int(total_papers * 0.30),  # 30% have straight quotes
            'TYPO-002': int(total_papers * 0.15),  # 15% have punctuation issues
            'MATH-001': int(total_papers * 0.25),  # 25% have math issues
            'MATH-002': int(total_papers * 0.10),  # 10% use $$
            'ENV-001': int(total_papers * 0.20),   # 20% have env issues
            'REF-001': int(total_papers * 0.40),   # 40% have reference issues
            'STYLE-001': int(total_papers * 0.30), # 30% have style issues
            'STRUCT-001': int(total_papers * 0.05), # 5% have structure issues
            'CHAR-001': int(total_papers * 0.15),  # 15% have character issues
            'ENC-001': int(total_papers * 0.10),   # 10% have encoding issues
        }
        
        return estimates
    
    def identify_validator_targets(self, issue_categories: Dict[str, int]) -> List[str]:
        """Identify which validators would benefit most from quarantined papers."""
        targets = []
        
        # Map issue categories to validator rules
        issue_to_rule = {
            'straight_quotes': 'TYPO-001',
            'double_dollar': 'MATH-002',
            'eqnarray': 'MATH-001',
            'mismatched_environments': 'ENV-001',
            'unicode_characters': 'ENC-001',
            'long_lines': 'STYLE-001'
        }
        
        # Find rules that would benefit from quarantined papers
        for issue_type, count in issue_categories.items():
            if count > 10 and issue_type in issue_to_rule:
                targets.append(issue_to_rule[issue_type])
        
        return targets
    
    def generate_corpus_report(self, output_file: str):
        """Generate comprehensive corpus analysis report."""
        print("Generating comprehensive corpus report...")
        
        corpus_stats = self.analyze_corpus_structure()
        quarantined_analysis = self.analyze_quarantined_papers()
        
        report = {
            'corpus_analysis': asdict(corpus_stats),
            'quarantined_analysis': asdict(quarantined_analysis),
            'recommendations': self.generate_recommendations(corpus_stats, quarantined_analysis),
            'testing_strategy': self.generate_testing_strategy(corpus_stats, quarantined_analysis)
        }
        
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        self.print_report_summary(corpus_stats, quarantined_analysis)
        
        return report
    
    def generate_recommendations(self, corpus_stats: CorpusStats, quarantined_analysis: QuarantinedAnalysis) -> List[str]:
        """Generate recommendations based on analysis."""
        recommendations = []
        
        if corpus_stats.total_papers > 2000:
            recommendations.append("Use parallel processing for corpus validation")
        
        if quarantined_analysis.total_quarantined > 500:
            recommendations.append("Analyze quarantined papers for valuable test cases")
        
        if corpus_stats.compilation_success_rate > 0.85:
            recommendations.append("Corpus may be too clean - consider including more problematic papers")
        
        if quarantined_analysis.total_quarantined > 1000:
            recommendations.append("Quarantined papers are a goldmine for testing - prioritize their analysis")
        
        return recommendations
    
    def generate_testing_strategy(self, corpus_stats: CorpusStats, quarantined_analysis: QuarantinedAnalysis) -> Dict:
        """Generate testing strategy based on corpus analysis."""
        return {
            'parallel_processing': {
                'recommended_workers': min(8, corpus_stats.total_papers // 100),
                'batch_size': 100,
                'estimated_time_minutes': corpus_stats.total_papers * 0.5 / 60
            },
            'issue_targeting': {
                'high_value_rules': quarantined_analysis.potential_validator_targets,
                'expected_issues': sum(corpus_stats.estimated_issue_distribution.values()),
                'ground_truth_potential': quarantined_analysis.total_quarantined
            },
            'resource_requirements': {
                'memory_gb': max(16, corpus_stats.total_papers // 200),
                'storage_gb': corpus_stats.total_papers * 0.1,
                'processing_time_hours': corpus_stats.total_papers * 75 / 3600
            }
        }
    
    def print_report_summary(self, corpus_stats: CorpusStats, quarantined_analysis: QuarantinedAnalysis):
        """Print summary of corpus analysis."""
        print("\n" + "="*60)
        print("ENTERPRISE CORPUS ANALYSIS COMPLETE")
        print("="*60)
        print(f"Main corpus: {corpus_stats.total_papers} papers")
        print(f"Quarantined: {quarantined_analysis.total_quarantined} papers")
        print(f"Total available: {corpus_stats.total_papers + quarantined_analysis.total_quarantined} papers")
        print(f"Metadata files: {corpus_stats.metadata_files}")
        print(f"Ground truth files: {corpus_stats.ground_truth_files}")
        print(f"Compilation success rate: {corpus_stats.compilation_success_rate:.1%}")
        
        print("\nEstimated issue distribution:")
        for rule, count in sorted(corpus_stats.estimated_issue_distribution.items()):
            print(f"  {rule}: {count} papers")
        
        print(f"\nQuarantined paper value assessment:")
        for category, count in quarantined_analysis.value_assessment.items():
            print(f"  {category}: {count} papers")
        
        print(f"\nRecommended validator targets from quarantined papers:")
        for target in quarantined_analysis.potential_validator_targets:
            print(f"  {target}")

def main():
    parser = argparse.ArgumentParser(description='Analyze Enterprise Corpus')
    parser.add_argument('--corpus', type=str, default='corpus',
                      help='Path to corpus directory')
    parser.add_argument('--output', type=str, default='results/corpus_analysis.json',
                      help='Output file for analysis results')
    parser.add_argument('--quarantined-only', action='store_true',
                      help='Analyze only quarantined papers')
    
    args = parser.parse_args()
    
    # Create results directory
    Path("results").mkdir(exist_ok=True)
    
    # Initialize analyzer
    analyzer = EnterpriseCorpusAnalyzer(args.corpus)
    
    if args.quarantined_only:
        print("Analyzing quarantined papers only...")
        quarantined_analysis = analyzer.analyze_quarantined_papers()
        
        with open(args.output, 'w') as f:
            json.dump(asdict(quarantined_analysis), f, indent=2)
    else:
        print("Analyzing full enterprise corpus...")
        report = analyzer.generate_corpus_report(args.output)
    
    print(f"\nAnalysis complete. Results saved to: {args.output}")

if __name__ == '__main__':
    main()