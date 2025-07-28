#!/usr/bin/env python3
# Check if straight quotes are in the curly list
curly_chars = ['„', '"', '«', '»', ''', ''', '"', '"']
print('Curly chars:')
for c in curly_chars:
    print(f'  {repr(c)} U+{ord(c):04X}')
    
print('\nChecking if straight quote is in list:')
print('  " in curly_chars:', '"' in curly_chars)
print('  \' in curly_chars:', "'" in curly_chars)