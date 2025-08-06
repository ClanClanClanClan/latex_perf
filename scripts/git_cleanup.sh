#!/bin/bash

# Git cleanup script to reduce repository size
# LaTeX Perfectionist v25 - Achieving 1GB compliance

set -e

echo "🧹 Git Repository Cleanup for v25 Compliance"
echo "==========================================="
echo ""
echo "Current .git size: $(du -sh .git | cut -f1)"
echo ""

# First, remove refs to deleted remote branches
echo "Step 1: Pruning remote tracking branches..."
git remote prune origin 2>/dev/null || true

# Remove all reflogs
echo "Step 2: Expiring reflogs..."
git reflog expire --expire=now --all

# Garbage collection with aggressive settings
echo "Step 3: Aggressive garbage collection..."
git gc --aggressive --prune=now

# Remove large files from history using filter-branch
echo "Step 4: Removing large files from history..."

# List of patterns for large files to remove
PATTERNS=(
    "*.pdf"
    "*.exe" 
    "*.bin"
    "*_native"
    "*_optimized"
    "perf_audit"
    "vsna_test_suite"
    "latex_validator"
    "file_tokenizer_native"
    "tokenizer_optimized"
)

# Create a list of files to remove
echo "Finding large files in history..."
> /tmp/large_files.txt
for pattern in "${PATTERNS[@]}"; do
    git rev-list --all --objects | grep "$pattern" | cut -d' ' -f2- >> /tmp/large_files.txt || true
done

# Remove duplicates
sort -u /tmp/large_files.txt -o /tmp/large_files.txt

echo "Found $(wc -l < /tmp/large_files.txt) large files to remove"

if [ -s /tmp/large_files.txt ]; then
    echo "Running BFG-like cleanup..."
    
    # Use git filter-repo if available, otherwise fallback to filter-branch
    if command -v git-filter-repo >/dev/null 2>&1; then
        # git-filter-repo is more efficient
        git filter-repo --invert-paths --paths-from-file /tmp/large_files.txt --force
    else
        # Fallback to filter-branch
        echo "WARNING: git-filter-repo not found, using slower filter-branch method"
        
        # Create script for filter-branch
        cat > /tmp/filter_script.sh << 'EOF'
#!/bin/bash
while IFS= read -r file; do
    git rm --cached --ignore-unmatch "$file" >/dev/null 2>&1 || true
done < /tmp/large_files.txt
EOF
        chmod +x /tmp/filter_script.sh
        
        git filter-branch --force --index-filter '/tmp/filter_script.sh' \
            --prune-empty --tag-name-filter cat -- --all
    fi
fi

# Final cleanup
echo "Step 5: Final cleanup..."
rm -rf .git/refs/original/ 2>/dev/null || true
git reflog expire --expire=now --all
git gc --aggressive --prune=now

# Pack refs
echo "Step 6: Packing refs..."
git pack-refs --all --prune

# Show results
echo ""
echo "✅ Cleanup complete!"
echo "New .git size: $(du -sh .git | cut -f1)"
echo ""
echo "Repository size breakdown:"
du -sh * .[^.]* 2>/dev/null | sort -hr | head -10
echo ""
echo "Total repository size: $(du -sh . | cut -f1)"

# Cleanup temp files
rm -f /tmp/large_files.txt /tmp/filter_script.sh

echo ""
echo "⚠️  WARNING: This has rewritten git history!"
echo "If you have a remote, you'll need to force push:"
echo "  git push --force-with-lease origin main"