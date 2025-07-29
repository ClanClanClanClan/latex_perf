')[0].strip()
        return "Unnamed rule"
    
    def _determine_category(self, python_file: Path) -> str:
        """Determine category from file path."""
        path_str = str(python_file)
        if 'math' in path_str:
            if 'canonical' in path_str or 'env' in path_str:
                return 'math.environments'
            elif 'script' in path_str:
                return 'math.scripts'
            elif 'spacing' in path_str:
                return 'math.spacing'
            else:
                return 'math.core'
        elif 'typography' in path_str:
            return 'typography'
        elif 'structure' in path_str:
            return 'structure'
        else:
            return 'general'
    
    def _extract_patterns(self, content: str) -> List[str]:
        """Extract regex patterns from code."""
        patterns = []
        
        # Look for re.compile patterns
        compile_matches = re.findall(r're\.compile\(r["\'](.+?)["\']', content)
        patterns.extend(compile_matches)
        
        # Look for direct regex patterns
        regex_matches = re.findall(r'pattern\s*=\s*r["\'](.+?)["\']', content)
        patterns.extend(regex_matches)
        
        # Look for BAD patterns in tests
        bad_matches = re.findall(r'BAD\s*=\s*["\'](.+?)["\']', content)
        if bad_matches and not patterns:
            # Try to infer pattern from BAD example
            pass
        
        return patterns
    
    def _extract_message(self, content: str) -> Optional[str]:
        """Extract error message from code."""
        # Look for message in Issue creation
        message_match = re.search(r'message\s*=\s*["\'](.+?)["\']', content)
        if message_match:
            return message_match.group(1)
        
        # Look for f-string messages
        fstring_match = re.search(r'message\s*=\s*f["\'](.+?)["\']', content)
        if fstring_match:
            return fstring_match.group(1)
        
        return None
    
    def _extract_tests(self, python_file: Path) -> List[Dict[str, str]]:
        """Extract test cases from test file."""
        tests = []
        
        # Look for corresponding test file
        test_file = Path('tests') / f"test_{python_file.stem}.py"
        if not test_file.exists():
            test_file = Path('tests') / 'rules' / f"test_{python_file.stem}.py"
        
        if test_file.exists():
            with open(test_file, 'r') as f:
                test_content = f.read()
            
            # Extract BAD/GOOD patterns
            bad_match = re.search(r'BAD\s*=\s*["\'](.+?)["\']', test_content)
            good_match = re.search(r'GOOD\s*=\s*["\'](.+?)["\']', test_content)
            
            if bad_match and good_match:
                tests.append({
                    'name': 'Basic test',
                    'input': bad_match.group(1),
                    'expect': 'error',
                    'fixed': good_match.group(1)
                })
        
        return tests


def migrate_all_rules():
    """Migrate all existing Python rules to DSL."""
    migrator = RuleMigrator()
    legacy_dir = Path('legacy/latex_perfectionist/rules')
    output_dir = Path('src/rules')
    
    for python_file in legacy_dir.glob('*.py'):
        if python_file.name.startswith('_'):
            continue
            
        print(f"Migrating {python_file.name}...")
        
        try:
            rule_data = migrator.migrate_rule(python_file)
            if rule_data:
                # Determine output path
                category_parts = rule_data['category'].split('.')
                if len(category_parts) > 1:
                    output_path = output_dir / category_parts[0] / category_parts[1]
                else:
                    output_path = output_dir / category_parts[0]
                
                output_path.mkdir(parents=True, exist_ok=True)
                output_file = output_path / f"{rule_data['id']}.yaml"
                
                # Write YAML
                with open(output_file, 'w') as f:
                    yaml.dump(rule_data, f, default_flow_style=False, sort_keys=False)
                
                print(f"  → Created {output_file}")
        
        except Exception as e:
            print(f"  ✗ Error: {e}")


if __name__ == "__main__":
    migrate_all_rules()