#!/usr/bin/env python3
"""Final merge of rules files, handling duplicates properly."""

def main():
    rules1_path = '/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/rules/rules.yaml'
    rules2_path = '/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/rules/rules_v2.yaml'
    output_path = '/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/rules/rules_unified.yaml'
    
    # Read both files
    with open(rules1_path, 'r', encoding='utf-8') as f:
        content1 = f.read()
    
    with open(rules2_path, 'r', encoding='utf-8') as f:
        content2 = f.read()
    
    # Extract rule blocks
    def extract_rules(content):
        blocks = []
        current_rule = []
        in_rule = False
        
        for line in content.split('\n'):
            if line.startswith('- id:'):
                if current_rule and in_rule:
                    blocks.append('\n'.join(current_rule))
                current_rule = [line]
                in_rule = True
            elif in_rule:
                current_rule.append(line)
        
        if current_rule and in_rule:
            blocks.append('\n'.join(current_rule))
        
        return blocks
    
    # Extract ID from a rule block
    def get_id(rule_block):
        for line in rule_block.split('\n'):
            if 'id:' in line:
                start = line.find('"') + 1
                end = line.find('"', start)
                if start > 0 and end > start:
                    return line[start:end]
        return None
    
    # Process both files
    rules1_blocks = extract_rules(content1)
    rules2_blocks = extract_rules(content2)
    
    print(f"Total rule blocks found:")
    print(f"- rules.yaml: {len(rules1_blocks)}")
    print(f"- rules_v2.yaml: {len(rules2_blocks)}")
    
    # Build list of all rules, keeping duplicates for now
    all_rules = []
    seen_ids = {}
    
    # Add all rules from rules_v2.yaml first (higher priority)
    for block in rules2_blocks:
        rule_id = get_id(block)
        if rule_id:
            all_rules.append((rule_id, block, 'v2'))
            seen_ids[rule_id] = 'v2'
    
    # Add rules from rules.yaml that aren't already in v2
    duplicate_within_rules1 = []
    for block in rules1_blocks:
        rule_id = get_id(block)
        if rule_id:
            if rule_id not in seen_ids:
                all_rules.append((rule_id, block, 'v1'))
                seen_ids[rule_id] = 'v1'
            elif seen_ids[rule_id] == 'v1':
                # Duplicate within rules.yaml itself
                duplicate_within_rules1.append(rule_id)
    
    # Report statistics
    print(f"\nStatistics:")
    print(f"- Rules from rules_v2.yaml: {len([r for r in all_rules if r[2] == 'v2'])}")
    print(f"- Unique rules from rules.yaml: {len([r for r in all_rules if r[2] == 'v1'])}")
    print(f"- Total unique rules: {len(all_rules)}")
    
    if duplicate_within_rules1:
        print(f"\nNote: Found duplicate IDs within rules.yaml itself: {set(duplicate_within_rules1)}")
        print("(These duplicates have been deduplicated in the output)")
    
    # Sort by ID and write output
    all_rules.sort(key=lambda x: x[0])
    
    with open(output_path, 'w', encoding='utf-8') as f:
        # Write header
        f.write("# Unified rules file combining rules.yaml and rules_v2.yaml\n")
        f.write(f"# Total unique rules: {len(all_rules)}\n")
        f.write(f"# Generated on: {__import__('datetime').datetime.now()}\n")
        f.write("#\n")
        f.write("# Notes:\n")
        f.write("# - Rules from rules_v2.yaml take precedence over rules.yaml for duplicate IDs\n")
        f.write("# - Duplicate IDs within rules.yaml have been deduplicated\n")
        f.write("\n")
        
        # Write rules
        for i, (rule_id, block, source) in enumerate(all_rules):
            if i > 0:
                f.write('\n')
            f.write(block)
    
    print(f"\nMerged rules written to: {output_path}")
    
    # Verify
    with open(output_path, 'r') as f:
        verify_content = f.read()
    verify_count = verify_content.count('- id:')
    print(f"Verification: Output file contains {verify_count} rules")

if __name__ == '__main__':
    main()