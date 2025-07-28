#!/usr/bin/env python3
"""
Script to add soundness proofs for ENC and CHAR rules.
"""

import re

def create_soundness_proof(category, rule_num):
    """Generate a soundness proof for ENC or CHAR rule."""
    rule_id = f"{category.lower()}_{rule_num}"
    return f"""(** ** {category}-{rule_num} Soundness Proof *)
Theorem {rule_id}_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue ({rule_id}_validator doc) ->
  (exists tok : latex_token, 
    In tok doc.(tokens) /\\
    match tok with
    | TText s => {rule_id}_check s = true
    | _ => False
    end).
Proof.
  intros doc Hlayer issue Hin.
  unfold {rule_id}_validator in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [tok [Htok_in Hissue_in]].
  exists tok. split. exact Htok_in.
  destruct tok; simpl in Hissue_in.
  - (* TCommand case *) 
    contradiction.
  - (* TBeginGroup case *)
    contradiction.
  - (* TEndGroup case *)
    contradiction.
  - (* TMathShift case *)
    contradiction.
  - (* TAlignment case *)
    contradiction.
  - (* TParameter case *)
    contradiction.
  - (* TSuperscript case *)
    contradiction.
  - (* TSubscript case *)
    contradiction.
  - (* TText case *)
    destruct ({rule_id}_check s) eqn:Hcheck.
    + reflexivity.
    + contradiction.
  - (* TSpace case *)
    contradiction.
  - (* TComment case *)
    contradiction.
  - (* TNewline case *)
    contradiction.
  - (* TEOF case *)
    contradiction.
Qed.

"""

def add_category_proofs(category, rule_count):
    """Add soundness proofs for a category of rules."""
    filename = "src/rules/phase1/TypoRules.v"
    
    with open(filename, 'r') as f:
        content = f.read()
    
    for rule_num in range(2, rule_count + 1):  # Skip 001 since it's done
        rule_num_str = f"{rule_num:03d}"
        rule_id = f"{category.lower()}_{rule_num_str}"
        
        # Check if proof already exists
        if f"Theorem {rule_id}_soundness" in content:
            print(f"Proof for {category}-{rule_num_str} already exists, skipping")
            continue
        
        # Find the rule definition
        rule_pattern = f"Definition {rule_id}_rule : validation_rule := \\{{\\|"
        match = re.search(rule_pattern, content)
        
        if not match:
            print(f"Rule definition for {category}-{rule_num_str} not found")
            continue
        
        # Insert the proof before the rule definition
        insert_pos = match.start()
        proof = create_soundness_proof(category, rule_num_str)
        content = content[:insert_pos] + proof + content[insert_pos:]
        
        # Update rule_sound := None to include ProofRef
        old_text = 'rule_sound := None'
        new_text = f'rule_sound := Some (ProofRef "{rule_id}_soundness")'
        
        # Find the rule definition again and update it
        rule_end = content.find('|}.', insert_pos + len(proof)) + 3
        rule_start = content.rfind(f'Definition {rule_id}_rule', 0, rule_end)
        rule_content = content[rule_start:rule_end]
        
        if old_text in rule_content:
            updated_rule = rule_content.replace(old_text, new_text)
            content = content[:rule_start] + updated_rule + content[rule_end:]
        
        print(f"Added soundness proof for {category}-{rule_num_str}")
    
    # Write the updated content back
    with open(filename, 'w') as f:
        f.write(content)
    
    print(f"Done! All {category} soundness proofs added.")

if __name__ == "__main__":
    # Add proofs for ENC-002 through ENC-005
    add_category_proofs("ENC", 5)
    
    # Add proofs for CHAR-001 through CHAR-005  
    add_category_proofs("CHAR", 5)