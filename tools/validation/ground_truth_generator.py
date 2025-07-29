#!/usr/bin/env python3
"""
Ground Truth Generator for LaTeX Perfectionist

Generates systematically crafted test documents with known issues
for 100% accurate validation of rules.
"""

import json
from pathlib import Path
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass, asdict
from datetime import datetime


@dataclass
class GroundTruthSection:
    """A section of a test document with known behavior."""
    content: str
    description: str
    rule_behaviors: Dict[str, Dict[str, any]]  # rule_id -> expected behavior


class GroundTruthGenerator:
    """Generates ground truth test documents systematically."""
    
    def __init__(self):
        self.output_dir = Path("validation/synthetic_ground_truth")
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def generate_typo_001_test_document(self) -> Tuple[str, List[Dict]]:
        """Generate comprehensive test document for TYPO-001 (smart quotes)."""
        
        sections = []
        
        # Section 1: Basic quote usage (SHOULD match)
        sections.append(GroundTruthSection(
            content='This is a "simple quote" test.',
            description="Simple quotes in normal text",
            rule_behaviors={
                "TYPO-001": {
                    "should_match": True,
                    "expected_matches": [{"start": 10, "end": 24, "text": '"simple quote"'}],
                    "expected_fix": 'This is a "simple quote" test.'
                }
            }
        ))
        
        # Section 2: Quotes in verbatim (should NOT match)
        sections.append(GroundTruthSection(
            content='\\begin{verbatim}\nHe said "hello"\n\\end{verbatim}',
            description="Quotes inside verbatim environment",
            rule_behaviors={
                "TYPO-001": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 3: Quotes in math mode (should NOT match)
        sections.append(GroundTruthSection(
            content='In math: $x = "value"$ is wrong.',
            description="Quotes inside inline math",
            rule_behaviors={
                "TYPO-001": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 4: Quotes in \texttt{} (should NOT match)
        sections.append(GroundTruthSection(
            content='Use \\texttt{"quotedString"} in code.',
            description="Quotes inside texttt (code formatting)",
            rule_behaviors={
                "TYPO-001": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 5: Mixed contexts
        sections.append(GroundTruthSection(
            content='Normal "quote" then \\texttt{"code"} then "another".',
            description="Mixed contexts - only non-code quotes should match",
            rule_behaviors={
                "TYPO-001": {
                    "should_match": True,
                    "expected_matches": [
                        {"start": 7, "end": 14, "text": '"quote"'},
                        {"start": 42, "end": 51, "text": '"another"'}
                    ]
                }
            }
        ))
        
        # Section 6: Nested quotes
        sections.append(GroundTruthSection(
            content='She said "he told me \'hello\' yesterday".',
            description="Nested quotes with single inside double",
            rule_behaviors={
                "TYPO-001": {
                    "should_match": True,
                    "expected_matches": [
                        {"start": 9, "end": 40, "text": '"he told me \'hello\' yesterday"'}
                    ]
                }
            }
        ))
        
        # Section 7: Quotes in listings environment
        sections.append(GroundTruthSection(
            content='\\begin{lstlisting}\nprint("hello world")\n\\end{lstlisting}',
            description="Quotes in code listing environment",
            rule_behaviors={
                "TYPO-001": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 8: Quotes in comments
        sections.append(GroundTruthSection(
            content='% This is a comment with "quotes"\nNormal text here.',
            description="Quotes in LaTeX comments",
            rule_behaviors={
                "TYPO-001": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 9: Edge case - empty quotes
        sections.append(GroundTruthSection(
            content='Empty quotes: "" should work.',
            description="Empty quote marks",
            rule_behaviors={
                "TYPO-001": {
                    "should_match": True,
                    "expected_matches": [{"start": 14, "end": 16, "text": '""'}]
                }
            }
        ))
        
        # Section 10: Quotes at line boundaries
        sections.append(GroundTruthSection(
            content='"Quote at start"\nAnd "quote\nat line break" too.',
            description="Quotes at line boundaries",
            rule_behaviors={
                "TYPO-001": {
                    "should_match": True,
                    "expected_matches": [
                        {"start": 0, "end": 16, "text": '"Quote at start"'},
                        {"start": 21, "end": 38, "text": '"quote\nat line break"'}
                    ]
                }
            }
        ))
        
        # Build complete document
        document_parts = []
        ground_truth = []
        current_pos = 0
        
        for i, section in enumerate(sections):
            # Add section comment
            comment = f"% TEST SECTION {i+1}: {section.description}\n"
            document_parts.append(comment)
            current_pos += len(comment)
            
            # Add section content
            document_parts.append(section.content)
            
            # Adjust positions for ground truth
            for rule_id, behavior in section.rule_behaviors.items():
                if 'expected_matches' in behavior:
                    for match in behavior['expected_matches']:
                        match['absolute_start'] = current_pos + match['start']
                        match['absolute_end'] = current_pos + match['end']
            
            ground_truth.append({
                'section': i + 1,
                'description': section.description,
                'start_pos': current_pos,
                'end_pos': current_pos + len(section.content),
                'content': section.content,
                'rule_behaviors': section.rule_behaviors
            })
            
            current_pos += len(section.content)
            document_parts.append('\n\n')
            current_pos += 2
        
        document = ''.join(document_parts)
        
        # Save files
        test_name = "TYPO-001_comprehensive"
        self._save_test_document(test_name, document, ground_truth)
        
        return document, ground_truth
    
    def generate_typo_002_test_document(self) -> Tuple[str, List[Dict]]:
        """Generate comprehensive test document for TYPO-002 (ellipsis)."""
        
        sections = []
        
        # Section 1: Basic ellipsis (SHOULD match)
        sections.append(GroundTruthSection(
            content='Wait... what happened?',
            description="Three dots in normal text",
            rule_behaviors={
                "TYPO-002": {
                    "should_match": True,
                    "expected_matches": [{"start": 4, "end": 7, "text": '...'}],
                    "expected_fix": 'Wait… what happened?'
                }
            }
        ))
        
        # Section 2: Ellipsis in verbatim (should NOT match)
        sections.append(GroundTruthSection(
            content='\\begin{verbatim}\ncode...\n\\end{verbatim}',
            description="Ellipsis in verbatim environment",
            rule_behaviors={
                "TYPO-002": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 3: Ellipsis in math (should NOT match)
        sections.append(GroundTruthSection(
            content='$1, 2, 3, ..., n$',
            description="Ellipsis in math mode",
            rule_behaviors={
                "TYPO-002": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 4: File extension (should NOT match)
        sections.append(GroundTruthSection(
            content='Save the file as document.tex',
            description="Period in file extension",
            rule_behaviors={
                "TYPO-002": {"should_match": False, "expected_matches": []}
            }
        ))
        
        # Section 5: Multiple ellipses
        sections.append(GroundTruthSection(
            content='First... second... third...',
            description="Multiple ellipses in one line",
            rule_behaviors={
                "TYPO-002": {
                    "should_match": True,
                    "expected_matches": [
                        {"start": 5, "end": 8, "text": '...'},
                        {"start": 15, "end": 18, "text": '...'},
                        {"start": 25, "end": 28, "text": '...'}
                    ]
                }
            }
        ))
        
        # Build and save document
        document_parts = []
        ground_truth = []
        current_pos = 0
        
        for i, section in enumerate(sections):
            comment = f"% TEST SECTION {i+1}: {section.description}\n"
            document_parts.append(comment)
            current_pos += len(comment)
            
            document_parts.append(section.content)
            
            for rule_id, behavior in section.rule_behaviors.items():
                if 'expected_matches' in behavior:
                    for match in behavior['expected_matches']:
                        match['absolute_start'] = current_pos + match['start']
                        match['absolute_end'] = current_pos + match['end']
            
            ground_truth.append({
                'section': i + 1,
                'description': section.description,
                'start_pos': current_pos,
                'end_pos': current_pos + len(section.content),
                'content': section.content,
                'rule_behaviors': section.rule_behaviors
            })
            
            current_pos += len(section.content)
            document_parts.append('\n\n')
            current_pos += 2
        
        document = ''.join(document_parts)
        
        test_name = "TYPO-002_comprehensive"
        self._save_test_document(test_name, document, ground_truth)
        
        return document, ground_truth
    
    def _save_test_document(self, name: str, document: str, ground_truth: List[Dict]):
        """Save test document and its ground truth."""
        # Save LaTeX document
        tex_path = self.output_dir / f"{name}.tex"
        tex_path.write_text(document)
        
        # Save ground truth
        truth_path = self.output_dir / f"{name}_ground_truth.json"
        with open(truth_path, 'w') as f:
            json.dump({
                'generated_date': datetime.now().isoformat(),
                'document_name': name,
                'sections': ground_truth
            }, f, indent=2)
        
        print(f"✓ Generated {name}: {len(ground_truth)} test sections")
    
    def generate_edge_case_corpus(self):
        """Generate documents targeting specific edge cases."""
        # TODO: Add more edge case generators
        pass


def main():
    """Generate all ground truth documents."""
    generator = GroundTruthGenerator()
    
    print("Generating systematic ground truth documents...")
    
    # Generate comprehensive test documents
    generator.generate_typo_001_test_document()
    generator.generate_typo_002_test_document()
    
    print("\nGround truth generation complete!")
    print(f"Documents saved to: {generator.output_dir}")


if __name__ == "__main__":
    main()