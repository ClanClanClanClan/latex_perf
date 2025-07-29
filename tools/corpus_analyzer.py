#!/usr/bin/env python3
"""
Comprehensive Corpus Analyzer for LaTeX Perfectionist v24
Analyzes corpus structure, identifies issues, and generates metadata
"""

import json
import time
import os
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Set
import hashlib
import argparse

@dataclass
class PaperInfo:
    paper_id: str
    path: str
    has_main_tex: bool
    has_nested_tex: bool
    tex_files: List[str]
    tex_count: int
    total_files: int
    total_size: int
    structure_type: str  # "simple", "nested", "complex", "broken"
    main_tex_path: Optional[str]
    estimated_complexity: str  # "low", "medium", "high"
    has_math: bool
    has_figures: bool
    has_bibliography: bool
    issues: List[str]

@dataclass
class CorpusAnalysis:
    total_directories: int
    total_papers: int
    total_tex_files: int
    valid_papers: int
    broken_papers: int
    structure_distribution: Dict[str, int]
    complexity_distribution: Dict[str, int]
    size_distribution: Dict[str, int]
    issues_found: List[str]
    quarantined_papers: List[str]
    analysis_time: float
    papers: List[PaperInfo]

class CorpusAnalyzer:
    def __init__(self, corpus_path: str):
        self.corpus_path = Path(corpus_path)
        self.papers = []
        self.issues = []
        self.quarantined = []
        
    def analyze_paper(self, paper_dir: Path) -> PaperInfo:
        """Analyze a single paper directory."""
        paper_id = paper_dir.name
        issues = []
        
        # Find all tex files
        tex_files = []
        for tex_file in paper_dir.rglob("*.tex"):
            tex_files.append(str(tex_file.relative_to(paper_dir)))
        
        # Check for main tex file
        main_tex_path = None
        has_main_tex = False
        has_nested_tex = False
        
        # Priority order for main tex file
        main_candidates = [
            "main.tex",
            "paper.tex", 
            "manuscript.tex",
            "document.tex"
        ]
        
        # Check direct tex files first
        for candidate in main_candidates:
            if (paper_dir / candidate).exists():
                main_tex_path = candidate
                has_main_tex = True
                break
        
        # Check nested tex files
        if not has_main_tex:
            for tex_file in tex_files:
                if any(candidate in tex_file for candidate in main_candidates):
                    main_tex_path = tex_file
                    has_nested_tex = True
                    break
        
        # If no main candidates, use first tex file
        if not main_tex_path and tex_files:
            main_tex_path = tex_files[0]
            if "/" in main_tex_path:
                has_nested_tex = True
            else:
                has_main_tex = True
        
        # Calculate total size
        total_size = 0
        total_files = 0
        for file_path in paper_dir.rglob("*"):
            if file_path.is_file():
                total_files += 1
                try:
                    total_size += file_path.stat().st_size
                except:
                    pass
        
        # Determine structure type
        if not tex_files:
            structure_type = "broken"
            issues.append("No tex files found")
        elif len(tex_files) == 1 and has_main_tex:
            structure_type = "simple"
        elif has_nested_tex:
            structure_type = "nested"
        else:
            structure_type = "complex"
        
        # Estimate complexity
        if total_size < 50000:  # < 50KB
            complexity = "low"
        elif total_size < 200000:  # < 200KB
            complexity = "medium"
        else:
            complexity = "high"
        
        # Check for math, figures, bibliography
        has_math = any("math" in f or "equation" in f for f in tex_files)
        has_figures = any([(paper_dir / "figures").exists(),
                          (paper_dir / "figs").exists(),
                          (paper_dir / "images").exists()])
        bib_files = list(paper_dir.rglob("*.bib"))
        has_bibliography = len(bib_files) > 0
        
        # Additional checks
        if total_files > 100:
            issues.append("Many files (>100)")
        if total_size > 1000000:  # > 1MB
            issues.append("Large size (>1MB)")
        if len(tex_files) > 20:
            issues.append("Many tex files (>20)")
            
        return PaperInfo(
            paper_id=paper_id,
            path=str(paper_dir),
            has_main_tex=has_main_tex,
            has_nested_tex=has_nested_tex,
            tex_files=tex_files,
            tex_count=len(tex_files),
            total_files=total_files,
            total_size=total_size,
            structure_type=structure_type,
            main_tex_path=main_tex_path,
            estimated_complexity=complexity,
            has_math=has_math,
            has_figures=has_figures,
            has_bibliography=has_bibliography,
            issues=issues
        )
    
    def analyze_corpus(self) -> CorpusAnalysis:
        """Analyze the entire corpus."""
        start_time = time.time()
        
        print(f"Analyzing corpus at: {self.corpus_path}")
        
        # Find all paper directories
        paper_dirs = [d for d in self.corpus_path.iterdir() if d.is_dir()]
        print(f"Found {len(paper_dirs)} paper directories")
        
        # Analyze each paper
        valid_papers = 0
        broken_papers = 0
        structure_dist = {}
        complexity_dist = {}
        size_dist = {"small": 0, "medium": 0, "large": 0}
        
        for i, paper_dir in enumerate(paper_dirs):
            if i % 100 == 0:
                print(f"Analyzing paper {i}/{len(paper_dirs)}: {paper_dir.name}")
            
            try:
                paper_info = self.analyze_paper(paper_dir)
                self.papers.append(paper_info)
                
                if paper_info.structure_type == "broken":
                    broken_papers += 1
                else:
                    valid_papers += 1
                
                # Update distributions
                structure_dist[paper_info.structure_type] = structure_dist.get(paper_info.structure_type, 0) + 1
                complexity_dist[paper_info.estimated_complexity] = complexity_dist.get(paper_info.estimated_complexity, 0) + 1
                
                # Size distribution
                if paper_info.total_size < 100000:  # < 100KB
                    size_dist["small"] += 1
                elif paper_info.total_size < 500000:  # < 500KB
                    size_dist["medium"] += 1
                else:
                    size_dist["large"] += 1
                    
                # Collect issues
                for issue in paper_info.issues:
                    if issue not in self.issues:
                        self.issues.append(issue)
                        
            except Exception as e:
                print(f"Error analyzing {paper_dir.name}: {e}")
                broken_papers += 1
        
        end_time = time.time()
        
        # Count total tex files
        total_tex_files = sum(len(paper.tex_files) for paper in self.papers)
        
        return CorpusAnalysis(
            total_directories=len(paper_dirs),
            total_papers=len(self.papers),
            total_tex_files=total_tex_files,
            valid_papers=valid_papers,
            broken_papers=broken_papers,
            structure_distribution=structure_dist,
            complexity_distribution=complexity_dist,
            size_distribution=size_dist,
            issues_found=self.issues,
            quarantined_papers=self.quarantined,
            analysis_time=end_time - start_time,
            papers=self.papers
        )
    
    def generate_report(self, analysis: CorpusAnalysis, output_file: str):
        """Generate detailed analysis report."""
        with open(output_file, 'w') as f:
            json.dump(asdict(analysis), f, indent=2)
        print(f"Analysis report saved to: {output_file}")
    
    def print_summary(self, analysis: CorpusAnalysis):
        """Print summary statistics."""
        print("\n" + "="*60)
        print("CORPUS ANALYSIS SUMMARY")
        print("="*60)
        print(f"Total directories: {analysis.total_directories}")
        print(f"Total papers: {analysis.total_papers}")
        print(f"Total tex files: {analysis.total_tex_files}")
        print(f"Valid papers: {analysis.valid_papers}")
        print(f"Broken papers: {analysis.broken_papers}")
        print(f"Success rate: {analysis.valid_papers/analysis.total_papers*100:.1f}%")
        print(f"Analysis time: {analysis.analysis_time:.1f} seconds")
        
        print(f"\nStructure Distribution:")
        for struct_type, count in analysis.structure_distribution.items():
            print(f"  {struct_type}: {count} papers")
        
        print(f"\nComplexity Distribution:")
        for complexity, count in analysis.complexity_distribution.items():
            print(f"  {complexity}: {count} papers")
        
        print(f"\nSize Distribution:")
        for size_type, count in analysis.size_distribution.items():
            print(f"  {size_type}: {count} papers")
        
        if analysis.issues_found:
            print(f"\nIssues Found:")
            for issue in analysis.issues_found:
                count = sum(1 for p in analysis.papers if issue in p.issues)
                print(f"  {issue}: {count} papers")
        
        # Performance projections
        print(f"\nPerformance Projections:")
        simple_papers = analysis.structure_distribution.get("simple", 0)
        nested_papers = analysis.structure_distribution.get("nested", 0)
        complex_papers = analysis.structure_distribution.get("complex", 0)
        
        # Estimated times based on current performance
        simple_time = simple_papers * 0.1  # 0.1s per simple paper
        nested_time = nested_papers * 0.5   # 0.5s per nested paper
        complex_time = complex_papers * 2.0  # 2.0s per complex paper
        total_time = simple_time + nested_time + complex_time
        
        print(f"  Simple papers ({simple_papers}): {simple_time:.1f}s")
        print(f"  Nested papers ({nested_papers}): {nested_time:.1f}s")
        print(f"  Complex papers ({complex_papers}): {complex_time:.1f}s")
        print(f"  Total estimated time: {total_time:.1f}s ({total_time/60:.1f} minutes)")
        
        # Recommendations
        print(f"\nRecommendations:")
        if analysis.broken_papers > 0:
            print(f"  - Fix {analysis.broken_papers} broken papers")
        if simple_papers > 0:
            print(f"  - Use fast path for {simple_papers} simple papers")
        if complex_papers > 0:
            print(f"  - Use slow path for {complex_papers} complex papers")
        print(f"  - Consider parallel processing for {analysis.valid_papers} valid papers")

def main():
    parser = argparse.ArgumentParser(description='Corpus Analyzer')
    parser.add_argument('--corpus', type=str, default='corpus/papers',
                      help='Path to corpus directory')
    parser.add_argument('--output', type=str, default='results/corpus_analysis.json',
                      help='Output file for analysis report')
    parser.add_argument('--summary-only', action='store_true',
                      help='Only print summary, do not save full report')
    
    args = parser.parse_args()
    
    # Create results directory
    Path("results").mkdir(exist_ok=True)
    
    # Initialize analyzer
    analyzer = CorpusAnalyzer(args.corpus)
    
    # Run analysis
    analysis = analyzer.analyze_corpus()
    
    # Print summary
    analyzer.print_summary(analysis)
    
    # Save report
    if not args.summary_only:
        analyzer.generate_report(analysis, args.output)

if __name__ == '__main__':
    main()