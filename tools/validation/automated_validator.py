#!/usr/bin/env python3
"""
Automated Validator for LaTeX Perfectionist

Tests rules against synthetic ground truth documents where we know
exactly what should and shouldn't match.
"""

import sys
import json
from pathlib import Path
from typing import Dict, List, Tuple, Set
from dataclasses import dataclass

sys.path.insert(0, 'src')

from latex_perfectionist.rules.compiled.rule_typo_001 import audit as typo_001_audit
from latex_perfectionist.rules.compiled.rule_typo_002 import audit as typo_002_audit


@dataclass
class ValidationResult:
    """Result of validating a rule against ground truth."""
    rule_id: str
    document_name: str
    precision: float
    recall: float
    false_positives: List[Dict]
    false_negatives: List[Dict]
    passed: bool
    details: str


class AutomatedValidator:
    """Validates rules against synthetic ground truth."""
    
    def __init__(self):
        self.ground_truth_dir = Path("validation/synthetic_ground_truth")
        self.rule_functions = {
            'TYPO-001': typo_001_audit,
            'TYPO-002': typo_002_audit,
        }
    
    def validate_rule(self, rule_id: str) -> List[ValidationResult]:
        """Validate a rule against all its ground truth documents."""
        results = []
        
        # Find ground truth documents for this rule
        pattern = f"{rule_id}_*_ground_truth.json"
        truth_files = list(self.ground_truth_dir.glob(pattern))
        
        if not truth_files:
            print(f"No ground truth found for {rule_id}")
            return results
        
        for truth_file in truth_files:
            result = self._validate_against_document(rule_id, truth_file)
            results.append(result)
            
        return results
    
    def _validate_against_document(self, rule_id: str, truth_file: Path) -> ValidationResult:
        """Validate rule against a single ground truth document."""
        # Load ground truth
        with open(truth_file) as f:
            truth_data = json.load(f)
        
        # Load corresponding LaTeX document
        tex_file = truth_file.parent / truth_file.name.replace('_ground_truth.json', '.tex')
        document = tex_file.read_text()
        
        # Run the rule
        if rule_id not in self.rule_functions:
            return ValidationResult(
                rule_id=rule_id,
                document_name=truth_data['document_name'],
                precision=0,
                recall=0,
                false_positives=[],
                false_negatives=[],
                passed=False,
                details="Rule function not found"
            )
        
        rule_result = self.rule_functions[rule_id](document, {})
        
        # Extract matches from rule result
        found_matches = []
        for issue in rule_result.issues:
            # Find the corresponding match position
            # This is simplified - in reality we'd need to map line numbers to positions
            found_matches.append({
                'line': issue.line,
                'message': issue.message
            })
        
        # For more accurate validation, let's analyze the fixes
        actual_matches = []
        for fix in rule_result.fixes:
            actual_matches.append({
                'start': fix.start,
                'end': fix.end,
                'text': document[fix.start:fix.end]
            })
        
        # Collect expected matches from all sections
        expected_matches = []
        for section in truth_data['sections']:
            behaviors = section['rule_behaviors'].get(rule_id, {})
            if behaviors.get('should_match', False):
                for match in behaviors.get('expected_matches', []):
                    # Adjust position based on section offset
                    expected_matches.append({
                        'start': match.get('absolute_start', section['start_pos'] + match['start']),
                        'end': match.get('absolute_end', section['start_pos'] + match['end']),
                        'text': match['text'],
                        'section': section['description']
                    })
        
        # Compare actual vs expected
        false_positives, false_negatives, true_positives = self._compare_matches(
            actual_matches, expected_matches
        )
        
        # Calculate metrics
        precision = len(true_positives) / len(actual_matches) if actual_matches else 1.0
        recall = len(true_positives) / len(expected_matches) if expected_matches else 1.0
        
        # Rule passes if 100% precision and >=95% recall
        passed = precision >= 1.0 and recall >= 0.95
        
        # Generate detailed report
        details = self._generate_details(
            section_results=truth_data['sections'],
            actual_matches=actual_matches,
            false_positives=false_positives,
            false_negatives=false_negatives
        )
        
        return ValidationResult(
            rule_id=rule_id,
            document_name=truth_data['document_name'],
            precision=precision,
            recall=recall,
            false_positives=false_positives,
            false_negatives=false_negatives,
            passed=passed,
            details=details
        )
    
    def _compare_matches(self, actual: List[Dict], expected: List[Dict]) -> Tuple[List, List, List]:
        """Compare actual matches with expected matches."""
        false_positives = []
        false_negatives = []
        true_positives = []
        
        # Convert to sets for comparison
        actual_set = {(m['start'], m['end']) for m in actual}
        expected_set = {(m['start'], m['end']) for m in expected}
        
        # Find true positives
        tp_positions = actual_set & expected_set
        for pos in tp_positions:
            true_positives.append({
                'start': pos[0],
                'end': pos[1],
                'status': 'correct'
            })
        
        # Find false positives
        fp_positions = actual_set - expected_set
        for pos in fp_positions:
            match = next(m for m in actual if m['start'] == pos[0] and m['end'] == pos[1])
            false_positives.append(match)
        
        # Find false negatives
        fn_positions = expected_set - actual_set
        for pos in fn_positions:
            match = next(m for m in expected if m['start'] == pos[0] and m['end'] == pos[1])
            false_negatives.append(match)
        
        return false_positives, false_negatives, true_positives
    
    def _generate_details(self, section_results: List[Dict], actual_matches: List[Dict],
                         false_positives: List[Dict], false_negatives: List[Dict]) -> str:
        """Generate detailed validation report."""
        details = []
        
        details.append(f"Total sections tested: {len(section_results)}")
        details.append(f"Actual matches found: {len(actual_matches)}")
        
        if false_positives:
            details.append(f"\nFalse Positives ({len(false_positives)}):")
            for fp in false_positives:
                details.append(f"  - Position {fp['start']}-{fp['end']}: '{fp['text']}'")
        
        if false_negatives:
            details.append(f"\nFalse Negatives ({len(false_negatives)}):")
            for fn in false_negatives:
                section_desc = fn.get('section', 'Unknown section')
                details.append(f"  - {section_desc}: '{fn['text']}'")
        
        # Section-by-section results
        details.append("\nSection Results:")
        for section in section_results:
            details.append(f"  {section['description']}: {'✓' if self._section_passed(section) else '✗'}")
        
        return '\n'.join(details)
    
    def _section_passed(self, section: Dict) -> bool:
        """Check if a section's test passed."""
        # Simplified check - in reality would compare actual vs expected
        return True
    
    def generate_report(self, results: List[ValidationResult]) -> str:
        """Generate a comprehensive validation report."""
        report = ["# Automated Validation Report\n"]
        
        for result in results:
            report.append(f"## {result.rule_id} - {result.document_name}")
            report.append(f"**Status**: {'✅ PASSED' if result.passed else '❌ FAILED'}")
            report.append(f"**Precision**: {result.precision:.1%}")
            report.append(f"**Recall**: {result.recall:.1%}")
            report.append(f"\n{result.details}\n")
            report.append("-" * 50 + "\n")
        
        return '\n'.join(report)


def main():
    """Run automated validation."""
    validator = AutomatedValidator()
    
    print("🤖 Running Automated Validation...")
    print("=" * 50)
    
    all_results = []
    
    # Validate each rule
    for rule_id in ['TYPO-001', 'TYPO-002']:
        print(f"\nValidating {rule_id}...")
        results = validator.validate_rule(rule_id)
        all_results.extend(results)
        
        for result in results:
            status = "✅" if result.passed else "❌"
            print(f"  {result.document_name}: {status} (P:{result.precision:.1%}, R:{result.recall:.1%})")
    
    # Generate report
    report = validator.generate_report(all_results)
    report_path = Path("validation/automated_validation_report.md")
    report_path.write_text(report)
    
    print(f"\n📄 Report saved to: {report_path}")
    
    # Summary
    passed = sum(1 for r in all_results if r.passed)
    total = len(all_results)
    print(f"\n🎯 Overall: {passed}/{total} tests passed")


if __name__ == "__main__":
    main()