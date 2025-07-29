#!/usr/bin/env python3
"""
ACCURACY ANALYSIS TOOL - Precision/Recall Measurement
Analyzes manual verification results to compute validator accuracy metrics.
"""

import json
import sys
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from typing import Dict, List, Tuple, Any
from collections import defaultdict

class AccuracyAnalyzer:
    def __init__(self, ground_truth_file: str):
        self.ground_truth_file = Path(ground_truth_file)
        self.ground_truth = self.load_ground_truth()
        self.metrics = self.compute_metrics()
    
    def load_ground_truth(self) -> Dict[str, Any]:
        """Load ground truth data"""
        if not self.ground_truth_file.exists():
            raise FileNotFoundError(f"Ground truth file not found: {self.ground_truth_file}")
        
        with open(self.ground_truth_file, 'r') as f:
            return json.load(f)
    
    def compute_metrics(self) -> Dict[str, Any]:
        """Compute comprehensive accuracy metrics"""
        metrics = {
            "overall": {},
            "by_rule": {},
            "by_severity": {},
            "confidence_intervals": {}
        }
        
        # Overall metrics
        total_issues = 0
        true_positives = 0
        false_positives = 0
        
        # Rule-specific metrics
        rule_metrics = defaultdict(lambda: {"tp": 0, "fp": 0, "total": 0})
        
        # Severity-specific metrics  
        severity_metrics = defaultdict(lambda: {"tp": 0, "fp": 0, "total": 0})
        
        # Process all verified issues
        for filename, file_data in self.ground_truth["verified_files"].items():
            for issue_key, issue_data in file_data.items():
                if not issue_data.get("verified", False):
                    continue
                
                rule_id = issue_data["rule_id"]
                severity = issue_data["severity"]
                is_tp = issue_data["is_true_positive"]
                
                total_issues += 1
                rule_metrics[rule_id]["total"] += 1
                severity_metrics[severity]["total"] += 1
                
                if is_tp:
                    true_positives += 1
                    rule_metrics[rule_id]["tp"] += 1
                    severity_metrics[severity]["tp"] += 1
                else:
                    false_positives += 1
                    rule_metrics[rule_id]["fp"] += 1
                    severity_metrics[severity]["fp"] += 1
        
        # Compute overall metrics
        if total_issues > 0:
            precision = true_positives / (true_positives + false_positives) if (true_positives + false_positives) > 0 else 0
            recall = 1.0  # We can't compute recall without false negatives
            f1_score = 2 * (precision * recall) / (precision + recall) if (precision + recall) > 0 else 0
            
            metrics["overall"] = {
                "total_verified_issues": total_issues,
                "true_positives": true_positives,
                "false_positives": false_positives,
                "precision": precision,
                "recall": "N/A (requires false negatives)",
                "f1_score": f1_score,
                "false_positive_rate": false_positives / total_issues
            }
        
        # Compute rule-specific metrics
        for rule_id, data in rule_metrics.items():
            if data["total"] > 0:
                precision = data["tp"] / (data["tp"] + data["fp"]) if (data["tp"] + data["fp"]) > 0 else 0
                metrics["by_rule"][rule_id] = {
                    "total_issues": data["total"],
                    "true_positives": data["tp"],
                    "false_positives": data["fp"],
                    "precision": precision,
                    "false_positive_rate": data["fp"] / data["total"]
                }
        
        # Compute severity-specific metrics
        for severity, data in severity_metrics.items():
            if data["total"] > 0:
                precision = data["tp"] / (data["tp"] + data["fp"]) if (data["tp"] + data["fp"]) > 0 else 0
                metrics["by_severity"][severity] = {
                    "total_issues": data["total"],
                    "true_positives": data["tp"],
                    "false_positives": data["fp"],
                    "precision": precision,
                    "false_positive_rate": data["fp"] / data["total"]
                }
        
        # Compute confidence intervals (using Wilson score interval)
        metrics["confidence_intervals"] = self.compute_confidence_intervals(true_positives, false_positives)
        
        return metrics
    
    def compute_confidence_intervals(self, tp: int, fp: int) -> Dict[str, Tuple[float, float]]:
        """Compute 95% confidence intervals for precision"""
        if tp + fp == 0:
            return {"precision_95ci": (0.0, 0.0)}
        
        n = tp + fp
        p = tp / n
        z = 1.96  # 95% confidence
        
        # Wilson score interval
        denominator = 1 + (z**2 / n)
        center = (p + (z**2 / (2*n))) / denominator
        margin = (z / denominator) * np.sqrt((p * (1-p) / n) + (z**2 / (4*n**2)))
        
        lower = max(0.0, center - margin)
        upper = min(1.0, center + margin)
        
        return {"precision_95ci": (lower, upper)}
    
    def generate_report(self) -> str:
        """Generate comprehensive accuracy report"""
        report = []
        report.append("# LATEX VALIDATOR ACCURACY ANALYSIS")
        report.append("=" * 50)
        report.append("")
        
        # Overall metrics
        overall = self.metrics["overall"]
        if overall:
            report.append("## OVERALL ACCURACY METRICS")
            report.append("-" * 30)
            report.append(f"Total Verified Issues: {overall['total_verified_issues']}")
            report.append(f"True Positives: {overall['true_positives']}")
            report.append(f"False Positives: {overall['false_positives']}")
            report.append(f"Precision: {overall['precision']:.1%}")
            report.append(f"False Positive Rate: {overall['false_positive_rate']:.1%}")
            
            # Confidence interval
            ci = self.metrics["confidence_intervals"]["precision_95ci"]
            report.append(f"Precision 95% CI: [{ci[0]:.1%}, {ci[1]:.1%}]")
            report.append("")
            
            # Quality assessment
            if overall['precision'] >= 0.95:
                quality = "EXCELLENT ✅"
            elif overall['precision'] >= 0.90:
                quality = "GOOD ✅"
            elif overall['precision'] >= 0.80:
                quality = "ACCEPTABLE ⚠️"
            else:
                quality = "POOR ❌"
            
            report.append(f"**OVERALL QUALITY: {quality}**")
            report.append("")
        
        # Rule-specific analysis
        report.append("## RULE-SPECIFIC ACCURACY")
        report.append("-" * 30)
        
        # Sort rules by precision (worst first for attention)
        sorted_rules = sorted(
            self.metrics["by_rule"].items(),
            key=lambda x: x[1]["precision"]
        )
        
        for rule_id, data in sorted_rules:
            precision = data["precision"]
            fp_rate = data["false_positive_rate"]
            
            if precision >= 0.95:
                status = "✅ EXCELLENT"
            elif precision >= 0.90:
                status = "✅ GOOD"
            elif precision >= 0.80:
                status = "⚠️  ACCEPTABLE"
            else:
                status = "❌ POOR"
            
            report.append(f"**{rule_id}**: {precision:.1%} precision | {fp_rate:.1%} FP rate | {data['total_issues']} issues | {status}")
        
        report.append("")
        
        # Severity analysis
        report.append("## SEVERITY-BASED ACCURACY")
        report.append("-" * 30)
        
        for severity, data in self.metrics["by_severity"].items():
            precision = data["precision"]
            report.append(f"**{severity}**: {precision:.1%} precision ({data['true_positives']} TP, {data['false_positives']} FP)")
        
        report.append("")
        
        # Recommendations
        report.append("## RECOMMENDATIONS")
        report.append("-" * 20)
        
        poor_rules = [rule for rule, data in self.metrics["by_rule"].items() if data["precision"] < 0.80]
        if poor_rules:
            report.append("### URGENT: Rules needing improvement")
            for rule in poor_rules:
                data = self.metrics["by_rule"][rule]
                report.append(f"- **{rule}**: {data['precision']:.1%} precision - high false positive rate")
        
        acceptable_rules = [rule for rule, data in self.metrics["by_rule"].items() if 0.80 <= data["precision"] < 0.90]
        if acceptable_rules:
            report.append("### Rules needing attention")
            for rule in acceptable_rules:
                data = self.metrics["by_rule"][rule]
                report.append(f"- **{rule}**: {data['precision']:.1%} precision - room for improvement")
        
        # Production readiness
        report.append("")
        report.append("## PRODUCTION READINESS ASSESSMENT")
        report.append("-" * 40)
        
        overall_precision = overall.get('precision', 0) if overall else 0
        if overall_precision >= 0.95:
            readiness = "✅ READY FOR PRODUCTION"
            recommendation = "Validators show excellent precision. Safe to deploy."
        elif overall_precision >= 0.90:
            readiness = "✅ READY WITH MONITORING"
            recommendation = "Good precision. Deploy with monitoring and user feedback system."
        elif overall_precision >= 0.80:
            readiness = "⚠️  CAUTION RECOMMENDED"
            recommendation = "Acceptable but needs improvement. Consider beta testing first."
        else:
            readiness = "❌ NOT READY"
            recommendation = "Poor precision. Significant improvements needed before deployment."
        
        report.append(f"**STATUS: {readiness}**")
        report.append(f"**RECOMMENDATION**: {recommendation}")
        
        return "\n".join(report)
    
    def generate_charts(self, output_dir: str = "accuracy_charts"):
        """Generate visualization charts"""
        output_path = Path(output_dir)
        output_path.mkdir(exist_ok=True)
        
        # Rule precision chart
        if self.metrics["by_rule"]:
            rules = list(self.metrics["by_rule"].keys())
            precisions = [self.metrics["by_rule"][rule]["precision"] for rule in rules]
            
            plt.figure(figsize=(12, 8))
            bars = plt.bar(range(len(rules)), precisions, color=['red' if p < 0.8 else 'orange' if p < 0.9 else 'green' for p in precisions])
            plt.xlabel('Validation Rules')
            plt.ylabel('Precision')
            plt.title('Validator Precision by Rule')
            plt.xticks(range(len(rules)), rules, rotation=45, ha='right')
            plt.ylim(0, 1)
            plt.axhline(y=0.8, color='orange', linestyle='--', alpha=0.7, label='Acceptable (80%)')
            plt.axhline(y=0.9, color='green', linestyle='--', alpha=0.7, label='Good (90%)')
            plt.legend()
            plt.tight_layout()
            plt.savefig(output_path / "rule_precision.png", dpi=300, bbox_inches='tight')
            plt.close()
        
        # Overall metrics pie chart
        if self.metrics["overall"]:
            tp = self.metrics["overall"]["true_positives"]
            fp = self.metrics["overall"]["false_positives"]
            
            plt.figure(figsize=(8, 8))
            plt.pie([tp, fp], labels=['True Positives', 'False Positives'], 
                   autopct='%1.1f%%', colors=['green', 'red'])
            plt.title('Overall Issue Classification')
            plt.savefig(output_path / "overall_classification.png", dpi=300, bbox_inches='tight')
            plt.close()
        
        print(f"📊 Charts saved to {output_path}/")
    
    def export_metrics(self, output_file: str = "accuracy_metrics.json"):
        """Export metrics to JSON for automated processing"""
        export_data = {
            "analysis_metadata": {
                "ground_truth_file": str(self.ground_truth_file),
                "total_files_analyzed": len(self.ground_truth["verified_files"]),
                "analysis_timestamp": str(Path(__file__).stat().st_mtime)
            },
            "metrics": self.metrics,
            "raw_ground_truth_stats": self.ground_truth.get("statistics", {})
        }
        
        with open(output_file, 'w') as f:
            json.dump(export_data, f, indent=2)
        
        print(f"📈 Accuracy metrics exported to {output_file}")

def main():
    """Main analysis function"""
    if len(sys.argv) != 2:
        print("Usage: python analyze_accuracy.py <ground_truth_file>")
        sys.exit(1)
    
    ground_truth_file = sys.argv[1]
    
    print("📊 VALIDATOR ACCURACY ANALYSIS")
    print("=" * 40)
    print(f"Ground truth file: {ground_truth_file}")
    print()
    
    try:
        analyzer = AccuracyAnalyzer(ground_truth_file)
        
        # Generate and display report
        report = analyzer.generate_report()
        print(report)
        
        # Save report to file
        with open("accuracy_report.md", 'w') as f:
            f.write(report)
        print(f"\n📄 Report saved to accuracy_report.md")
        
        # Generate charts
        analyzer.generate_charts()
        
        # Export metrics
        analyzer.export_metrics()
        
        print("\n🎯 ACCURACY ANALYSIS COMPLETE!")
        
    except Exception as e:
        print(f"❌ ERROR: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()