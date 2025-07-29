#!/usr/bin/env python3
"""
🎯 RULE ID MAPPING SYSTEM
LaTeX Perfectionist v24-R3: Bridge Our Validators ↔ Ground Truth Format

This system maps our 80 validator rule IDs to the ground truth format used by the corpus,
enabling accurate precision/recall metrics for corpus validation.
"""

from typing import Dict, Set, List, Optional
from dataclasses import dataclass

@dataclass
class RuleMapping:
    our_rule_id: str
    ground_truth_rule: str
    confidence: float  # 0.0-1.0 how confident we are in this mapping
    notes: str

class RuleMappingSystem:
    """Maps between our validator rule IDs and corpus ground truth format"""
    
    def __init__(self):
        self.mappings = self._initialize_mappings()
        self.reverse_mappings = self._build_reverse_mappings()
    
    def _initialize_mappings(self) -> List[RuleMapping]:
        """Initialize rule mappings based on analysis of ground truth and our validators"""
        
        return [
            # DIRECT MATCHES (High Confidence)
            RuleMapping(
                our_rule_id="POST-037", 
                ground_truth_rule="double_dollar_math",
                confidence=0.95,
                notes="Both detect obsolete $$ display math. POST-037 found 23, ground truth expects 12."
            ),
            
            # PARTIAL MATCHES (Medium Confidence)  
            RuleMapping(
                our_rule_id="MATH-001",
                ground_truth_rule="straight_quotes", 
                confidence=0.30,
                notes="MATH-001 detects $ vs \\( \\) but may overlap with quote issues. 531 detected vs 1 expected."
            ),
            
            RuleMapping(
                our_rule_id="SCRIPT-005",
                ground_truth_rule="wrong_dashes",
                confidence=0.40, 
                notes="SCRIPT-005 detects typography issues including dashes. 420 detected vs 936 expected."
            ),
            
            # NO GROUND TRUTH EQUIVALENT (Our validators are more comprehensive)
            RuleMapping(
                our_rule_id="MATH-029",
                ground_truth_rule="differential_operators", 
                confidence=0.00,
                notes="Our validator detects differential operator issues not tracked in ground truth. 413 detected."
            ),
            
            RuleMapping(
                our_rule_id="MATH-007", 
                ground_truth_rule="decimal_notation",
                confidence=0.00,
                notes="Our validator detects decimal notation issues not tracked in ground truth. 169 detected."
            ),
            
            RuleMapping(
                our_rule_id="MATH-005",
                ground_truth_rule="function_names",
                confidence=0.00, 
                notes="Our validator detects function name issues not tracked in ground truth. 11 detected."
            ),
            
            # GROUND TRUTH ISSUES WE DON'T DETECT YET
            RuleMapping(
                our_rule_id="UNMAPPED",
                ground_truth_rule="bad_ellipsis",
                confidence=0.00,
                notes="Ground truth expects 9 ellipsis fixes - none of our active validators detect this."
            ),
            
            RuleMapping(
                our_rule_id="UNMAPPED", 
                ground_truth_rule="missing_tilde_cite",
                confidence=0.00,
                notes="Ground truth expects 8 citation fixes - none of our active validators detect this."
            ),
            
            RuleMapping(
                our_rule_id="UNMAPPED",
                ground_truth_rule="complex_macros",
                confidence=0.00,
                notes="Ground truth expects 43 macro fixes - none of our active validators detect this."
            ),
            
            RuleMapping(
                our_rule_id="UNMAPPED",
                ground_truth_rule="nested_environments", 
                confidence=0.00,
                notes="Ground truth expects 4 environment fixes - none of our active validators detect this."
            )
        ]
    
    def _build_reverse_mappings(self) -> Dict[str, List[RuleMapping]]:
        """Build reverse lookup from ground truth rules to our rule IDs"""
        reverse = {}
        for mapping in self.mappings:
            if mapping.ground_truth_rule not in reverse:
                reverse[mapping.ground_truth_rule] = []
            reverse[mapping.ground_truth_rule].append(mapping)
        return reverse
    
    def map_our_rule_to_ground_truth(self, our_rule_id: str) -> Optional[str]:
        """Map our rule ID to ground truth format (returns highest confidence match)"""
        candidates = [m for m in self.mappings if m.our_rule_id == our_rule_id]
        if not candidates:
            return None
        
        # Return highest confidence mapping
        best_match = max(candidates, key=lambda m: m.confidence)
        return best_match.ground_truth_rule if best_match.confidence > 0.5 else None
    
    def map_ground_truth_to_our_rules(self, ground_truth_rule: str) -> List[str]:
        """Map ground truth rule to our rule IDs"""
        if ground_truth_rule not in self.reverse_mappings:
            return []
        
        return [m.our_rule_id for m in self.reverse_mappings[ground_truth_rule] 
                if m.confidence > 0.5 and m.our_rule_id != "UNMAPPED"]
    
    def calculate_adjusted_metrics(self, our_issues: Set[str], ground_truth_issues: Set[str]) -> Dict:
        """Calculate precision/recall using rule mappings"""
        
        # Map our issues to ground truth format
        mapped_our_issues = set()
        for our_rule in our_issues:
            gt_rule = self.map_our_rule_to_ground_truth(our_rule)
            if gt_rule:
                mapped_our_issues.add(gt_rule)
        
        # Calculate metrics using mapped rules
        true_positives = len(mapped_our_issues & ground_truth_issues)
        false_positives = len(mapped_our_issues - ground_truth_issues)  
        false_negatives = len(ground_truth_issues - mapped_our_issues)
        
        precision = true_positives / len(mapped_our_issues) if mapped_our_issues else 0.0
        recall = true_positives / len(ground_truth_issues) if ground_truth_issues else 0.0
        f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0.0
        
        return {
            'true_positives': true_positives,
            'false_positives': false_positives,
            'false_negatives': false_negatives,
            'precision': precision,
            'recall': recall, 
            'f1_score': f1,
            'mapped_our_issues': mapped_our_issues,
            'ground_truth_issues': ground_truth_issues,
            'mapping_coverage': len(mapped_our_issues) / len(our_issues) if our_issues else 0.0
        }
    
    def analyze_coverage_gaps(self, our_issues: Set[str], ground_truth_issues: Set[str]) -> Dict:
        """Analyze what issues we're missing and what extra issues we're finding"""
        
        mapped_our_issues = set()
        unmapped_our_issues = set()
        
        for our_rule in our_issues:
            gt_rule = self.map_our_rule_to_ground_truth(our_rule)
            if gt_rule:
                mapped_our_issues.add(gt_rule)
            else:
                unmapped_our_issues.add(our_rule)
        
        missing_from_ground_truth = ground_truth_issues - mapped_our_issues
        extra_beyond_ground_truth = unmapped_our_issues
        
        return {
            'missing_rules': missing_from_ground_truth,
            'extra_rules': extra_beyond_ground_truth,
            'coverage_analysis': {
                'we_detect': len(mapped_our_issues),
                'ground_truth_expects': len(ground_truth_issues), 
                'we_miss': len(missing_from_ground_truth),
                'we_find_extra': len(extra_beyond_ground_truth)
            }
        }
    
    def print_mapping_report(self):
        """Print comprehensive mapping analysis"""
        print("🎯 RULE MAPPING ANALYSIS")
        print("=" * 50)
        
        high_confidence = [m for m in self.mappings if m.confidence > 0.7]
        medium_confidence = [m for m in self.mappings if 0.3 <= m.confidence <= 0.7] 
        low_confidence = [m for m in self.mappings if m.confidence < 0.3]
        
        print(f"✅ High Confidence Mappings ({len(high_confidence)}):")
        for mapping in high_confidence:
            print(f"   {mapping.our_rule_id} → {mapping.ground_truth_rule} ({mapping.confidence:.0%})")
        
        print(f"\n🔸 Medium Confidence Mappings ({len(medium_confidence)}):")
        for mapping in medium_confidence:
            print(f"   {mapping.our_rule_id} → {mapping.ground_truth_rule} ({mapping.confidence:.0%})")
        
        print(f"\n❓ Unmapped Issues ({len(low_confidence)}):")
        for mapping in low_confidence:
            if mapping.our_rule_id == "UNMAPPED":
                print(f"   Missing: {mapping.ground_truth_rule} (not detected by our validators)")
            else:
                print(f"   Extra: {mapping.our_rule_id} (not in ground truth)")

if __name__ == "__main__":
    # Test the mapping system
    mapper = RuleMappingSystem()
    mapper.print_mapping_report()
    
    # Test with sample data
    our_issues = {"POST-037", "MATH-001", "SCRIPT-005", "MATH-029", "MATH-007", "MATH-005"}
    ground_truth_issues = {"double_dollar_math", "straight_quotes", "wrong_dashes", "bad_ellipsis", "missing_tilde_cite", "complex_macros", "nested_environments"}
    
    print("\n🧪 SAMPLE METRICS TEST")
    print("=" * 50)
    metrics = mapper.calculate_adjusted_metrics(our_issues, ground_truth_issues)
    
    print(f"Precision: {metrics['precision']:.2%}")
    print(f"Recall: {metrics['recall']:.2%}") 
    print(f"F1 Score: {metrics['f1_score']:.3f}")
    print(f"Mapping Coverage: {metrics['mapping_coverage']:.2%}")
    
    coverage = mapper.analyze_coverage_gaps(our_issues, ground_truth_issues)
    print(f"\nCoverage Analysis:")
    print(f"  We detect: {coverage['coverage_analysis']['we_detect']} ground truth issues")
    print(f"  Ground truth expects: {coverage['coverage_analysis']['ground_truth_expects']} issues")
    print(f"  We miss: {coverage['coverage_analysis']['we_miss']} issues") 
    print(f"  We find extra: {coverage['coverage_analysis']['we_find_extra']} issues")