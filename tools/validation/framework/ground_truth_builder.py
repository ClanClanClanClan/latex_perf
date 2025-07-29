#!/usr/bin/env python3
"""
Ground Truth Builder for LaTeX Perfectionist Corpus

This system creates manually verified "ground truth" versions of corpus files
where ALL issues have been correctly fixed according to our rules. This enables
100% accuracy validation through differential testing.
"""

import os
import sys
import json
import hashlib
import importlib.util
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

@dataclass
class GroundTruthIssue:
    """Represents a manually verified issue and its correct fix."""
    rule_id: str
    line_number: int
    column_start: int
    column_end: int
    original_text: str
    corrected_text: str
    issue_type: str
    severity: str
    verified_by: str
    verification_date: str
    notes: str

@dataclass
class GroundTruthFile:
    """Represents a manually verified LaTeX file."""
    arxiv_id: str
    original_file: str
    corrected_file: str
    original_checksum: str
    corrected_checksum: str
    issues_fixed: List[GroundTruthIssue]
    verification_complete: bool
    verifier: str
    verification_date: str
    notes: str

class GroundTruthBuilder:
    """Builds and manages ground truth corpus for accuracy validation."""
    
    def __init__(self, corpus_dir: str = "corpus"):
        self.corpus_dir = Path(corpus_dir)
        self.ground_truth_dir = self.corpus_dir / "ground_truth"
        self.ground_truth_dir.mkdir(exist_ok=True)
        
        # Directories for different phases
        self.original_dir = self.ground_truth_dir / "original"
        self.corrected_dir = self.ground_truth_dir / "corrected"
        self.metadata_dir = self.ground_truth_dir / "metadata"
        
        for dir_path in [self.original_dir, self.corrected_dir, self.metadata_dir]:
            dir_path.mkdir(exist_ok=True)
        
        # Load existing ground truth data
        self.ground_truth_files = {}
        self._load_existing_ground_truth()
        
        # Load compiled rules for reference
        self.compiled_rules = self._load_compiled_rules()
    
    def _load_compiled_rules(self) -> Dict:
        """Load compiled rules for reference during manual verification."""
        rules = {}
        rule_files = [
            ('rule_typo_001.py', 'TYPO-001'),
            ('rule_typo_002.py', 'TYPO-002'),
            ('rule_typo_003.py', 'TYPO-003'),
            ('rule_math_001.py', 'MATH-001'),
            ('rule_menv_001.py', 'MENV-001'),
            ('rule_menv_002.py', 'MENV-002'),
            ('rule_menv_003.py', 'MENV-003'),
        ]
        
        for rule_file, rule_id in rule_files:
            rule_path = Path(f'src/latex_perfectionist/compiled_rules/{rule_file}')
            if rule_path.exists():
                try:
                    spec = importlib.util.spec_from_file_location(rule_id, rule_path)
                    module = importlib.util.module_from_spec(spec)
                    spec.loader.exec_module(module)
                    rules[rule_id] = module
                except Exception as e:
                    print(f"Warning: Could not load rule {rule_id}: {e}")
        
        return rules
    
    def _load_existing_ground_truth(self):
        """Load existing ground truth metadata."""
        for metadata_file in self.metadata_dir.glob("*.json"):
            try:
                with open(metadata_file) as f:
                    data = json.load(f)
                    # Convert dict back to GroundTruthFile
                    issues = [GroundTruthIssue(**issue) for issue in data.get('issues_fixed', [])]
                    data['issues_fixed'] = issues
                    self.ground_truth_files[data['arxiv_id']] = GroundTruthFile(**data)
            except Exception as e:
                print(f"Warning: Could not load ground truth file {metadata_file}: {e}")
    
    def select_papers_for_ground_truth(self, count: int = 5) -> List[str]:
        """Select papers for ground truth creation based on issue diversity."""
        papers_dir = self.corpus_dir / "papers"
        
        if not papers_dir.exists():
            print("No corpus found - please build corpus first")
            return []
        
        # Analyze papers to find diverse set of issues
        paper_analysis = {}
        
        for paper_dir in papers_dir.iterdir():
            if not paper_dir.is_dir():
                continue
                
            arxiv_id = paper_dir.name
            
            # Load metadata
            metadata_file = paper_dir / "metadata.json"
            if not metadata_file.exists():
                continue
            
            try:
                with open(metadata_file) as f:
                    metadata = json.load(f)
                
                # Load main tex file
                main_tex_file = paper_dir / metadata['main_tex_file']
                if not main_tex_file.exists():
                    tex_files = list(paper_dir.glob("*.tex"))
                    if not tex_files:
                        continue
                    main_tex_file = tex_files[0]
                
                content = main_tex_file.read_text(encoding='utf-8', errors='ignore')
                
                # Run all rules to get issue diversity
                issue_types = {}
                total_issues = 0
                
                for rule_id, rule_module in self.compiled_rules.items():
                    try:
                        result = rule_module.audit(content, {'locale': 'en-US'})
                        issue_count = len(result.issues)
                        issue_types[rule_id] = issue_count
                        total_issues += issue_count
                    except Exception:
                        issue_types[rule_id] = 0
                
                paper_analysis[arxiv_id] = {
                    'total_issues': total_issues,
                    'issue_types': issue_types,
                    'file_size': len(content),
                    'complexity': metadata.get('complexity_score', 0),
                    'main_tex_file': main_tex_file.name
                }
                
            except Exception as e:
                print(f"Warning: Could not analyze paper {arxiv_id}: {e}")
        
        # Select diverse papers
        selected_papers = []
        
        # Sort by total issues (descending) and select papers with diverse issue types
        sorted_papers = sorted(paper_analysis.items(), 
                             key=lambda x: x[1]['total_issues'], 
                             reverse=True)
        
        # Take papers with different dominant issue types
        rule_coverage = {rule_id: 0 for rule_id in self.compiled_rules.keys()}
        
        for arxiv_id, analysis in sorted_papers:
            if len(selected_papers) >= count:
                break
            
            # Check if this paper adds new rule coverage
            dominant_rules = [rule_id for rule_id, count in analysis['issue_types'].items() 
                            if count > 0]
            
            # Select if it has good coverage and reasonable size
            if (len(dominant_rules) >= 3 and 
                analysis['total_issues'] >= 10 and 
                analysis['file_size'] < 100000):  # Not too large for manual verification
                selected_papers.append(arxiv_id)
                
                # Update rule coverage
                for rule_id in dominant_rules:
                    rule_coverage[rule_id] += 1
        
        return selected_papers
    
    def create_ground_truth_file(self, arxiv_id: str, verifier: str = "manual") -> bool:
        """Create ground truth file for a paper."""
        papers_dir = self.corpus_dir / "papers"
        paper_dir = papers_dir / arxiv_id
        
        if not paper_dir.exists():
            print(f"Paper {arxiv_id} not found in corpus")
            return False
        
        # Load paper metadata
        metadata_file = paper_dir / "metadata.json"
        if not metadata_file.exists():
            print(f"No metadata found for paper {arxiv_id}")
            return False
        
        with open(metadata_file) as f:
            metadata = json.load(f)
        
        # Load main tex file
        main_tex_file = paper_dir / metadata['main_tex_file']
        if not main_tex_file.exists():
            tex_files = list(paper_dir.glob("*.tex"))
            if not tex_files:
                print(f"No TeX files found for paper {arxiv_id}")
                return False
            main_tex_file = tex_files[0]
        
        original_content = main_tex_file.read_text(encoding='utf-8', errors='ignore')
        
        # Copy original file to ground truth directory
        original_path = self.original_dir / f"{arxiv_id}.tex"
        original_path.write_text(original_content, encoding='utf-8')
        
        # Create initial corrected file (copy of original)
        corrected_path = self.corrected_dir / f"{arxiv_id}.tex"
        corrected_path.write_text(original_content, encoding='utf-8')
        
        # Run all rules to identify issues for manual verification
        issues_to_verify = []
        
        for rule_id, rule_module in self.compiled_rules.items():
            try:
                result = rule_module.audit(original_content, {'locale': 'en-US'})
                
                for issue in result.issues:
                    # Find the text around the issue
                    lines = original_content.split('\n')
                    if issue.line <= len(lines):
                        line_text = lines[issue.line - 1]
                        
                        # Create issue record for manual verification
                        issue_record = GroundTruthIssue(
                            rule_id=rule_id,
                            line_number=issue.line,
                            column_start=0,  # Will be filled manually
                            column_end=len(line_text),  # Will be filled manually
                            original_text=line_text,
                            corrected_text="",  # To be filled manually
                            issue_type=issue.type,
                            severity=issue.level,
                            verified_by="",  # To be filled manually
                            verification_date="",  # To be filled manually
                            notes=""  # To be filled manually
                        )
                        issues_to_verify.append(issue_record)
                        
            except Exception as e:
                print(f"Warning: Could not run rule {rule_id} on {arxiv_id}: {e}")
        
        # Create ground truth file record
        ground_truth_file = GroundTruthFile(
            arxiv_id=arxiv_id,
            original_file=str(original_path),
            corrected_file=str(corrected_path),
            original_checksum=hashlib.md5(original_content.encode()).hexdigest(),
            corrected_checksum=hashlib.md5(original_content.encode()).hexdigest(),
            issues_fixed=issues_to_verify,
            verification_complete=False,
            verifier=verifier,
            verification_date="",
            notes=""
        )
        
        # Save metadata
        metadata_path = self.metadata_dir / f"{arxiv_id}.json"
        with open(metadata_path, 'w') as f:
            # Convert to dict for JSON serialization
            data = asdict(ground_truth_file)
            json.dump(data, f, indent=2)
        
        self.ground_truth_files[arxiv_id] = ground_truth_file
        
        print(f"Created ground truth template for {arxiv_id}")
        print(f"Found {len(issues_to_verify)} issues to verify")
        print(f"Original file: {original_path}")
        print(f"Corrected file: {corrected_path}")
        print(f"Metadata: {metadata_path}")
        
        return True
    
    def create_verification_report(self, arxiv_id: str) -> str:
        """Create a detailed verification report for manual correction."""
        if arxiv_id not in self.ground_truth_files:
            return f"No ground truth file found for {arxiv_id}"
        
        gt_file = self.ground_truth_files[arxiv_id]
        
        # Load original content
        original_content = Path(gt_file.original_file).read_text(encoding='utf-8')
        lines = original_content.split('\n')
        
        # Group issues by rule
        issues_by_rule = {}
        for issue in gt_file.issues_fixed:
            if issue.rule_id not in issues_by_rule:
                issues_by_rule[issue.rule_id] = []
            issues_by_rule[issue.rule_id].append(issue)
        
        # Create report
        report = f"""
# Ground Truth Verification Report
## Paper: {arxiv_id}

### Instructions:
1. Review each issue identified by the rules
2. Manually verify if the issue is a true positive
3. If true positive, provide the EXACT corrected text
4. Update the corrected file: {gt_file.corrected_file}
5. Fill in verification metadata

### Issues to Verify:
"""
        
        for rule_id, issues in issues_by_rule.items():
            rule_module = self.compiled_rules.get(rule_id)
            rule_name = getattr(rule_module, 'MESSAGE', rule_id) if rule_module else rule_id
            
            report += f"""
## Rule: {rule_id}
**Description:** {rule_name}
**Issues found:** {len(issues)}

"""
            
            for i, issue in enumerate(issues):
                line_num = issue.line_number
                if line_num <= len(lines):
                    line_text = lines[line_num - 1]
                    
                    # Show context (3 lines before and after)
                    context_start = max(0, line_num - 4)
                    context_end = min(len(lines), line_num + 3)
                    context = lines[context_start:context_end]
                    
                    report += f"""
### Issue {i+1}
**Line {line_num}:** `{line_text}`

**Context:**
```latex
{chr(10).join(f"{context_start + j + 1:3d}: {line}" for j, line in enumerate(context))}
```

**Rule violation:** {issue.issue_type}
**Severity:** {issue.severity}

**Manual verification needed:**
- [ ] Is this a true positive? (Y/N)
- [ ] Corrected text: _________________
- [ ] Verification notes: _________________

---
"""
        
        report += f"""
### Final Steps:
1. Edit the corrected file: `{gt_file.corrected_file}`
2. Apply ALL verified corrections
3. Update metadata with verification status
4. Run validation to ensure 100% accuracy

### Verification Checklist:
- [ ] All issues reviewed
- [ ] Corrected file updated
- [ ] Metadata updated
- [ ] Validation passed
"""
        
        return report
    
    def generate_ground_truth_corpus(self, count: int = 5):
        """Generate ground truth corpus for selected papers."""
        print("LaTeX Perfectionist Ground Truth Generation")
        print("=" * 50)
        
        # Select papers for ground truth
        print(f"Selecting {count} papers for ground truth generation...")
        selected_papers = self.select_papers_for_ground_truth(count)
        
        if not selected_papers:
            print("No suitable papers found for ground truth generation")
            return
        
        print(f"Selected papers: {selected_papers}")
        
        # Create ground truth files
        for arxiv_id in selected_papers:
            print(f"\nProcessing paper: {arxiv_id}")
            
            if self.create_ground_truth_file(arxiv_id):
                # Generate verification report
                report = self.create_verification_report(arxiv_id)
                report_path = self.ground_truth_dir / f"{arxiv_id}_verification_report.md"
                report_path.write_text(report, encoding='utf-8')
                
                print(f"✓ Ground truth template created")
                print(f"✓ Verification report: {report_path}")
            else:
                print(f"✗ Failed to create ground truth for {arxiv_id}")
        
        print(f"\nGround truth generation complete!")
        print(f"Next steps:")
        print(f"1. Review verification reports in {self.ground_truth_dir}")
        print(f"2. Manually verify and correct each issue")
        print(f"3. Update corrected files with verified fixes")
        print(f"4. Run validation to ensure 100% accuracy")


def main():
    """Main function to generate ground truth corpus."""
    builder = GroundTruthBuilder()
    builder.generate_ground_truth_corpus(count=3)  # Start with 3 papers

if __name__ == "__main__":
    main()