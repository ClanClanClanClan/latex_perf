#!/usr/bin/env python3
"""
Rule Executor for v21 Workflow

This module loads and executes compiled rules for validation testing.
"""

import sys
import os
sys.path.insert(0, 'src')

import re
import importlib.util
from pathlib import Path
from typing import List, Dict, Any, Tuple, Optional

class RuleExecutor:
    """Executes compiled rules for validation testing."""
    
    def __init__(self):
        self.rules_dir = Path("src/latex_perfectionist/rules/compiled")
        self.loaded_rules = {}
    
    def load_rule(self, rule_id: str) -> Optional[Any]:
        """Load a compiled rule module."""
        if rule_id in self.loaded_rules:
            return self.loaded_rules[rule_id]
        
        # Convert rule ID to filename
        rule_filename = f"rule_{rule_id.lower().replace('-', '_')}.py"
        rule_path = self.rules_dir / rule_filename
        
        if not rule_path.exists():
            print(f"⚠️ Rule file not found: {rule_path}")
            return None
        
        try:
            # Load the rule module
            spec = importlib.util.spec_from_file_location(f"rule_{rule_id}", rule_path)
            rule_module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(rule_module)
            
            self.loaded_rules[rule_id] = rule_module
            return rule_module
            
        except Exception as e:
            print(f"❌ Error loading rule {rule_id}: {e}")
            return None
    
    def execute_rule(self, rule_id: str, text: str) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
        """Execute a rule on text and return matches and fixes."""
        rule_module = self.load_rule(rule_id)
        if not rule_module:
            return [], []
        
        try:
            # Get the pattern from the rule
            pattern = getattr(rule_module, 'PATTERN', None)
            if not pattern:
                print(f"⚠️ No PATTERN found in rule {rule_id}")
                return [], []
            
            # Find all matches
            matches = []
            fixes = []
            
            for match in pattern.finditer(text):
                # Check if match should be excluded based on context
                if self._should_exclude_match(rule_module, text, match):
                    continue
                
                match_info = {
                    "start": match.start(),
                    "end": match.end(),
                    "text": match.group()
                }
                matches.append(match_info)
                
                # Generate fix if rule supports it
                fix = self._generate_fix(rule_module, match, text)
                if fix:
                    fixes.append(fix)
            
            return matches, fixes
            
        except Exception as e:
            print(f"❌ Error executing rule {rule_id}: {e}")
            return [], []
    
    def _should_exclude_match(self, rule_module: Any, text: str, match: re.Match) -> bool:
        """Check if a match should be excluded based on context."""
        start = match.start()
        end = match.end()
        
        # Check for verbatim context
        if hasattr(rule_module, '_is_in_verbatim'):
            if rule_module._is_in_verbatim(text, start, end):
                return True
        
        # Check for math context
        if hasattr(rule_module, '_is_in_math'):
            if rule_module._is_in_math(text, start, end):
                return True
        
        # Check for code context
        if hasattr(rule_module, '_is_in_code'):
            if rule_module._is_in_code(text, start, end):
                return True
        
        return False
    
    def _generate_fix(self, rule_module: Any, match: re.Match, text: str) -> Optional[Dict[str, Any]]:
        """Generate a fix for a match."""
        # For TYPO-001, convert straight quotes to curly quotes
        if hasattr(rule_module, 'RULE_ID') and rule_module.RULE_ID == 'TYPO-001':
            return self._fix_typo_001(match, text)
        
        # For TYPO-002, convert ... to ellipsis
        if hasattr(rule_module, 'RULE_ID') and rule_module.RULE_ID == 'TYPO-002':
            return self._fix_typo_002(match, text)
        
        return None
    
    def _fix_typo_001(self, match: re.Match, text: str) -> Dict[str, Any]:
        """Fix TYPO-001 by converting straight quotes to curly quotes."""
        matched_text = match.group()
        
        # Convert straight quotes to curly quotes
        if matched_text.startswith('"') and matched_text.endswith('"'):
            # Double quotes
            inner_text = matched_text[1:-1]
            replacement = f"\u201c{inner_text}\u201d"
        elif matched_text.startswith("'") and matched_text.endswith("'"):
            # Single quotes
            inner_text = matched_text[1:-1]
            replacement = f"\u2018{inner_text}\u2019"
        else:
            replacement = matched_text
        
        return {
            "start": match.start(),
            "end": match.end(),
            "replacement": replacement
        }
    
    def _fix_typo_002(self, match: re.Match, text: str) -> Dict[str, Any]:
        """Fix TYPO-002 by converting ... to ellipsis."""
        return {
            "start": match.start(),
            "end": match.end(),
            "replacement": "\u2026"
        }

# Test the rule executor
def test_rule_executor():
    """Test the rule executor with sample text."""
    executor = RuleExecutor()
    
    # Test TYPO-001
    test_text = 'This is a "quoted text" example.'
    matches, fixes = executor.execute_rule("TYPO-001", test_text)
    print(f"TYPO-001 matches: {matches}")
    print(f"TYPO-001 fixes: {fixes}")
    
    # Test TYPO-002
    test_text = 'This has three dots...'
    matches, fixes = executor.execute_rule("TYPO-002", test_text)
    print(f"TYPO-002 matches: {matches}")
    print(f"TYPO-002 fixes: {fixes}")

if __name__ == "__main__":
    test_rule_executor()