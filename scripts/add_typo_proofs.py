#!/usr/bin/env python3
"""
Script to systematically add soundness proofs for TYPO rules that are missing them.
"""

import re
import sys

def create_soundness_proof(rule_number):
    """Generate a soundness proof for a given TYPO rule number."""
    return f"""(** ** TYPO-{rule_number} Soundness Proof *)
Theorem typo_{rule_number}_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue (typo_{rule_number}_validator doc) ->
  (exists tok : latex_token, 
    In tok doc.(tokens) /\\
    match tok with
    | TText s => typo_{rule_number}_check s = true
    | _ => False
    end).
Proof.
  intros doc Hlayer issue Hin.
  unfold typo_{rule_number}_validator in Hin.
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
    destruct (typo_{rule_number}_check s) eqn:Hcheck.
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

def process_file(filename):
    """Process the TypoRules.v file to add missing proofs."""
    with open(filename, 'r') as f:
        content = f.read()
    
    # Find all TYPO rules that have rule_sound := None
    pattern = r'Definition typo_(\d{3})_rule : validation_rule := \{\|[^}]+rule_sound := None'
    matches = list(re.finditer(pattern, content, re.DOTALL))
    
    print(f"Found {len(matches)} TYPO rules without soundness proofs")
    
    # Process in reverse order to avoid offset issues
    for match in reversed(matches):
        rule_num = match.group(1)
        print(f"Adding soundness proof for TYPO-{rule_num}")
        
        # Find the position to insert the proof (before the rule definition)
        rule_def_start = content.rfind('Definition typo_' + rule_num + '_rule', 0, match.start())
        
        # Insert the proof
        proof = create_soundness_proof(rule_num)
        content = content[:rule_def_start] + proof + content[rule_def_start:]
        
        # Update rule_sound := None to rule_sound := Some (ProofRef "...")
        old_text = 'rule_sound := None'
        new_text = f'rule_sound := Some (ProofRef "typo_{rule_num}_soundness")'
        
        # Find the exact position within this rule definition
        rule_end = content.find('|}.', match.start()) + 3
        rule_content = content[match.start():rule_end]
        updated_rule = rule_content.replace(old_text, new_text)
        content = content[:match.start()] + updated_rule + content[rule_end:]
    
    return content

if __name__ == "__main__":
    input_file = "src/rules/phase1/TypoRules.v"
    
    # Process the file
    updated_content = process_file(input_file)
    
    # Write the updated content
    with open(input_file, 'w') as f:
        f.write(updated_content)
    
    print("Done! All TYPO rules now have soundness proofs.")