#!/usr/bin/env python3

from fixed_integration import RobustOCamlBridge
from pathlib import Path

def debug_simple():
    """Debug the exact tokenization sequence for the failing case"""
    
    test_input = "Text % $math$"
    
    print(f"🔍 DEBUGGING COMMENT TOKENIZATION")
    print(f"Input: '{test_input}'")
    print("=" * 50)
    
    bridge = RobustOCamlBridge(Path('.'))
    tokens = bridge.tokenize_file(test_input)
    
    print("Tokens generated:")
    for i, token in enumerate(tokens, 1):
        if token.content:
            print(f"{i:2d}. {token.type}('{token.content}')")
        else:
            print(f"{i:2d}. {token.type}")
    
    print()
    print("Analysis:")
    text_tokens = [t.content for t in tokens if t.type == 'TEXT']
    comment_tokens = [t.content for t in tokens if t.type == 'COMMENT']
    
    print(f"TEXT tokens: {text_tokens}")
    print(f"COMMENT tokens: {comment_tokens}")
    
    # Check for the specific problem
    text_with_dollar = [t for t in text_tokens if '$' in t]
    print(f"TEXT tokens containing '$': {text_with_dollar}")
    
    if text_with_dollar:
        print("❌ PROBLEM: $ symbol found in TEXT tokens!")
        print("This means comment content is leaking into TEXT tokens")
        
        # Show which TEXT token contains the dollar
        for i, token in enumerate(tokens, 1):
            if token.type == 'TEXT' and '$' in token.content:
                print(f"   Token {i}: TEXT('{token.content}') contains '$'")
    else:
        print("✅ Good: No $ symbols in TEXT tokens")

if __name__ == "__main__":
    debug_simple()