#!/usr/bin/env python3
"""
Smart Paper Selector for LaTeX Perfectionist

Systematically selects papers from corpus based on specific features
to ensure comprehensive coverage of edge cases.
"""

import re
import json
import sqlite3
from pathlib import Path
from typing import Dict, List, Set, Tuple
from collections import defaultdict


class SmartPaperSelector:
    """Intelligently selects papers for testing based on features."""
    
    def __init__(self, corpus_dir: str = "corpus"):
        self.corpus_dir = Path(corpus_dir)
        self.db_path = self.corpus_dir / "corpus_metadata.db"
        self.papers_dir = self.corpus_dir / "papers"
    
    def select_papers_by_features(self, feature_requirements: Dict[str, int]) -> List[str]:
        """
        Select papers that have specific features.
        
        Example:
            feature_requirements = {
                'has_verbatim': 10,      # 10 papers with verbatim environments
                'has_math_quotes': 5,    # 5 papers with quotes near math
                'has_code_blocks': 10,   # 10 papers with code
                'clean_baseline': 5,     # 5 papers with no quotes at all
            }
        """
        selected_papers = defaultdict(list)
        
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT arxiv_id, features FROM papers")
            
            for arxiv_id, features_json in cursor.fetchall():
                features = json.loads(features_json)
                
                # Check each requirement
                for requirement, needed_count in feature_requirements.items():
                    if len(selected_papers[requirement]) >= needed_count:
                        continue
                    
                    if self._paper_matches_requirement(features, requirement, arxiv_id):
                        selected_papers[requirement].append(arxiv_id)
        
        # Combine all selected papers (removing duplicates)
        all_papers = set()
        for papers in selected_papers.values():
            all_papers.update(papers)
        
        return list(all_papers)
    
    def _paper_matches_requirement(self, features: Dict, requirement: str, arxiv_id: str) -> bool:
        """Check if a paper matches a specific requirement."""
        
        # Load the actual paper content for complex checks
        paper_path = self.papers_dir / arxiv_id / features.get('main_tex_file', 'main.tex')
        if not paper_path.exists():
            return False
        
        try:
            content = paper_path.read_text()
        except:
            return False
        
        # Define requirement checks
        if requirement == 'has_verbatim':
            return bool(re.search(r'\\begin\{verbatim\}', content))
        
        elif requirement == 'has_lstlisting':
            return bool(re.search(r'\\begin\{lstlisting', content))
        
        elif requirement == 'has_texttt':
            return bool(re.search(r'\\texttt\{', content))
        
        elif requirement == 'has_math_quotes':
            # Papers with quotes near math environments
            has_quotes = features.get('straight_quotes', 0) > 0
            has_math = features.get('inline_math', 0) > 0 or features.get('equations', 0) > 0
            return has_quotes and has_math
        
        elif requirement == 'has_code_blocks':
            return (features.get('listings', 0) > 0 or 
                   bool(re.search(r'\\texttt\{', content)) or
                   bool(re.search(r'\\verb', content)))
        
        elif requirement == 'clean_baseline':
            # Papers with no quotes at all (good for false positive testing)
            return features.get('straight_quotes', 0) == 0
        
        elif requirement == 'heavy_quotes':
            # Papers with lots of quotes
            return features.get('straight_quotes', 0) > 10
        
        elif requirement == 'heavy_math':
            # Math-heavy papers
            return features.get('inline_math', 0) > 50
        
        elif requirement == 'has_comments':
            return features.get('comments', 0) > 10
        
        elif requirement == 'complex_structure':
            # Papers with complex LaTeX structure
            return features.get('complexity_score', 0) > 0.2
        
        return False
    
    def analyze_coverage_gaps(self) -> Dict[str, List[str]]:
        """Analyze what edge cases we're missing in our corpus."""
        coverage_gaps = {
            'missing_contexts': [],
            'untested_combinations': [],
            'recommendations': []
        }
        
        # Check what contexts we have coverage for
        context_coverage = {
            'verbatim': 0,
            'lstlisting': 0,
            'math_inline': 0,
            'math_display': 0,
            'comments': 0,
            'texttt': 0,
            'verb': 0,
        }
        
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT features FROM papers")
            
            for (features_json,) in cursor.fetchall():
                features = json.loads(features_json)
                if features.get('listings', 0) > 0:
                    context_coverage['lstlisting'] += 1
                if features.get('inline_math', 0) > 0:
                    context_coverage['math_inline'] += 1
                if features.get('comments', 0) > 0:
                    context_coverage['comments'] += 1
        
        # Identify gaps
        for context, count in context_coverage.items():
            if count < 5:
                coverage_gaps['missing_contexts'].append(
                    f"Low coverage for {context}: only {count} papers"
                )
        
        return coverage_gaps
    
    def create_test_matrix(self) -> List[Dict[str, str]]:
        """Create a comprehensive test matrix for systematic validation."""
        test_matrix = []
        
        # Define all contexts where quotes can appear
        contexts = [
            'normal_text',
            'verbatim_env',
            'lstlisting_env', 
            'math_inline',
            'math_display',
            'equation_env',
            'comment_line',
            'texttt_command',
            'verb_command',
            'section_title',
            'caption',
            'footnote'
        ]
        
        # Define quote types
        quote_types = [
            'double_straight',  # "..."
            'single_straight',  # '...'
            'mixed_quotes',     # "...'...'"
            'empty_quotes',     # ""
            'unicode_quotes',   # "..."
        ]
        
        # Create test cases for each combination
        for context in contexts:
            for quote_type in quote_types:
                test_matrix.append({
                    'context': context,
                    'quote_type': quote_type,
                    'test_name': f"{context}_{quote_type}",
                    'expected_behavior': self._get_expected_behavior(context, quote_type)
                })
        
        return test_matrix
    
    def _get_expected_behavior(self, context: str, quote_type: str) -> str:
        """Determine expected behavior for a context/quote combination."""
        # Contexts where quotes should NOT be matched
        no_match_contexts = {
            'verbatim_env', 'lstlisting_env', 'math_inline', 
            'math_display', 'equation_env', 'comment_line',
            'texttt_command', 'verb_command'
        }
        
        if context in no_match_contexts:
            return 'no_match'
        else:
            return 'match_and_fix'


def main():
    """Demonstrate smart paper selection."""
    selector = SmartPaperSelector()
    
    # Define what we want to test
    requirements = {
        'has_verbatim': 5,
        'has_lstlisting': 5,
        'has_texttt': 5,
        'has_math_quotes': 5,
        'clean_baseline': 5,
        'heavy_quotes': 3,
        'complex_structure': 3,
    }
    
    print("Selecting papers for comprehensive testing...")
    selected = selector.select_papers_by_features(requirements)
    print(f"Selected {len(selected)} papers for testing")
    
    # Analyze coverage
    print("\nAnalyzing coverage gaps...")
    gaps = selector.analyze_coverage_gaps()
    for gap_type, issues in gaps.items():
        if issues:
            print(f"\n{gap_type}:")
            for issue in issues:
                print(f"  - {issue}")
    
    # Create test matrix
    print("\nGenerating test matrix...")
    matrix = selector.create_test_matrix()
    print(f"Created {len(matrix)} test combinations to verify")


if __name__ == "__main__":
    main()