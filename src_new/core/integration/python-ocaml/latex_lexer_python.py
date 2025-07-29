#!/usr/bin/env python3
"""
LaTeX Perfectionist - Python interface to verified Coq lexer
"""

import json
import subprocess
import os
from pathlib import Path
from typing import List, Dict, Any

class LatexToken:
    """Represents a LaTeX token from the verified lexer"""
    
    def __init__(self, token_type: str, content: str = ""):
        self.type = token_type
        self.content = content
    
    def __str__(self):
        if self.content:
            return f"{self.type}({self.content})"
        return self.type
    
    def __repr__(self):
        return self.__str__()
    
    def __eq__(self, other):
        if not isinstance(other, LatexToken):
            return False
        return self.type == other.type and self.content == other.content

class VerifiedLatexLexer:
    """Python interface to the verified Coq LaTeX lexer"""
    
    def __init__(self):
        self.bridge_path = Path(__file__).parent / "lexer_bridge_working.ml"
        if not self.bridge_path.exists():
            raise FileNotFoundError(f"OCaml bridge not found at {self.bridge_path}")
    
    def tokenize(self, latex_input: str) -> List[LatexToken]:
        """
        Tokenize LaTeX input using the verified Coq lexer
        
        Args:
            latex_input: LaTeX source code to tokenize
            
        Returns:
            List of LatexToken objects
            
        Raises:
            RuntimeError: If the OCaml lexer fails
        """
        try:
            # Call the OCaml bridge
            process = subprocess.Popen(
                ['ocaml', str(self.bridge_path)],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                cwd=self.bridge_path.parent
            )
            
            stdout, stderr = process.communicate(input=latex_input)
            
            if process.returncode != 0:
                raise RuntimeError(f"OCaml lexer failed: {stderr}")
            
            # Parse JSON output
            tokens_json = json.loads(stdout.strip())
            
            # Convert to LatexToken objects
            tokens = []
            for token_dict in tokens_json:
                token_type = token_dict["type"]
                content = token_dict.get("content", "")
                tokens.append(LatexToken(token_type, content))
            
            return tokens
            
        except json.JSONDecodeError as e:
            raise RuntimeError(f"Failed to parse lexer output: {e}")
        except Exception as e:
            raise RuntimeError(f"Lexer error: {e}")

# Replacement for MockBatchLexer 
class RealBatchLexer:
    """Real batch lexer using verified Coq implementation"""
    
    def __init__(self):
        self.lexer = VerifiedLatexLexer()
    
    def tokenize(self, content: str) -> List[Dict]:
        """
        Tokenize content and return tokens in dictionary format
        (compatible with existing mock interface)
        """
        tokens = self.lexer.tokenize(content)
        return [{"type": token.type, "content": token.content} for token in tokens]

def test_lexer():
    """Test the verified lexer"""
    lexer = VerifiedLatexLexer()
    
    test_cases = [
        "hello world",
        "\\frac{1}{2}",
        "\\section{Introduction}",
        "$x^2 + y^2 = z^2$",
        "% This is a comment",
        "{hello} world",
        "\\begin{equation}\\n x = y \\n\\end{equation}"
    ]
    
    print("=== VERIFIED LATEX LEXER TEST ===")
    for i, test_input in enumerate(test_cases, 1):
        print(f"\nTest {i}: {repr(test_input)}")
        try:
            tokens = lexer.tokenize(test_input)
            print(f"Tokens: {tokens}")
        except Exception as e:
            print(f"Error: {e}")

if __name__ == "__main__":
    test_lexer()