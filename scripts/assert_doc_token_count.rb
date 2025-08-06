#!/usr/bin/env ruby
# assert_doc_token_count.rb - Check documentation for correct token constructor count
# Part of LaTeX Perfectionist v25 CI infrastructure

require 'find'

# Files to check
DOC_FILES = [
  'specs/Appendices v25.md',
  'specs/v25_master.md',
  'specs/v25_master.yaml',
  'specs/v25/PLANNER.yaml',
  'docs/**/*.md'
]

# Patterns that indicate wrong constructor count
WRONG_PATTERNS = [
  /nine[- ]constructor/i,
  /9[- ]constructor/i,
  /nine constructor/i,
  /9 constructor/i,
  /Token ADT.*Nine/,
  /24 B on 64.*bit.*3 words/
]

# Patterns that indicate correct constructor count
CORRECT_PATTERNS = [
  /six[- ]constructor/i,
  /6[- ]constructor/i,
  /six constructor/i,
  /6 constructor/i
]

errors = []
correct_found = false

# Expand glob patterns and check each file
DOC_FILES.each do |pattern|
  Dir.glob(pattern).each do |file|
    next unless File.file?(file)
    
    content = File.read(file)
    lines = content.lines
    
    lines.each_with_index do |line, idx|
      # Check for wrong patterns
      WRONG_PATTERNS.each do |pattern|
        if line.match?(pattern)
          errors << "#{file}:#{idx+1}: Found wrong pattern '#{pattern}': #{line.strip}"
        end
      end
      
      # Check if we have any correct patterns
      CORRECT_PATTERNS.each do |pattern|
        correct_found = true if line.match?(pattern)
      end
    end
  end
end

# Report results
if errors.empty? && correct_found
  puts "✅ Documentation check passed!"
  puts "   Found correct 'six-constructor' references"
  puts "   No 'nine-constructor' references found"
  exit 0
elsif !errors.empty?
  puts "❌ Documentation check failed!"
  puts "   Found #{errors.length} incorrect references:"
  errors.each { |e| puts "   #{e}" }
  exit 1
else
  puts "⚠️  Warning: No token constructor references found in documentation"
  exit 0
end