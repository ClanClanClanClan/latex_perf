#!/usr/bin/env python3
"""
Script to add the missing soundness proofs for TYPO-016 through TYPO-025
in their correct locations (before their rule definitions).
"""

import re

def create_soundness_proof(rule_num):
    """Generate a soundness proof for a given TYPO rule number."""
    return f"""(** ** TYPO-{rule_num} Soundness Proof *)
Theorem typo_{rule_num}_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue (typo_{rule_num}_validator doc) ->
  (exists tok : latex_token, 
    In tok doc.(tokens) /\\
    match tok with
    | TText s => typo_{rule_num}_check s = true
    | _ => False
    end).
Proof.
  intros doc Hlayer issue Hin.
  unfold typo_{rule_num}_validator in Hin.
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
    destruct (typo_{rule_num}_check s) eqn:Hcheck.
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

def add_missing_proofs():
    """Add missing soundness proofs for TYPO-016 through TYPO-025."""
    filename = "src/rules/phase1/TypoRules.v"
    
    with open(filename, 'r') as f:
        content = f.read()
    
    # Add proofs for TYPO-016 through TYPO-025
    for rule_num in range(16, 26):
        rule_num_str = f"{rule_num:03d}"
        
        # Check if proof already exists
        if f"Theorem typo_{rule_num_str}_soundness" in content:
            print(f"Proof for TYPO-{rule_num_str} already exists, skipping")
            continue
        
        # Find the rule definition
        rule_pattern = f"Definition typo_{rule_num_str}_rule : validation_rule := \\{{\\|"
        match = re.search(rule_pattern, content)
        
        if not match:
            print(f"Rule definition for TYPO-{rule_num_str} not found")
            continue
        
        # Insert the proof before the rule definition
        insert_pos = match.start()
        proof = create_soundness_proof(rule_num_str)
        content = content[:insert_pos] + proof + content[insert_pos:]
        
        print(f"Added soundness proof for TYPO-{rule_num_str}")
    
    # Write the updated content back
    with open(filename, 'w') as f:
        f.write(content)
    
    print("Done! All missing TYPO soundness proofs have been added.")

if __name__ == "__main__":
    add_missing_proofs()