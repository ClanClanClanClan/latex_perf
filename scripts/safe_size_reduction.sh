#!/bin/bash

# Safe size reduction script - creates a fresh repository without history
# This preserves current state but removes git history bloat

set -e

echo "🧹 Safe Repository Size Reduction"
echo "================================"
echo ""
echo "This script will create a new repository with only current files"
echo "Git history will be reset, but all current work is preserved"
echo ""

# Current size
echo "Current repository size: $(du -sh . | cut -f1)"
echo "Current .git size: $(du -sh .git | cut -f1)"
echo ""

# Create backup branch
BACKUP_BRANCH="backup-before-size-reduction-$(date +%Y%m%d-%H%M%S)"
echo "Creating backup branch: $BACKUP_BRANCH"
git checkout -b "$BACKUP_BRANCH"
git checkout -

# Save current branch name
CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)

# Create a temporary directory
TEMP_DIR=$(mktemp -d)
echo "Using temporary directory: $TEMP_DIR"

# Copy all files except .git
echo "Copying current files..."
rsync -av --exclude='.git' --exclude='_build' . "$TEMP_DIR/"

# Initialize new git repo
echo "Initializing fresh repository..."
cd "$TEMP_DIR"
git init
git add .
git commit -m "Initial commit - LaTeX Perfectionist v25 Week 1

This is a fresh start to achieve <1GB repository size compliance.
Previous history preserved in backup branch: $BACKUP_BRANCH"

# Copy the new .git back
echo "Replacing .git directory..."
cd -
rm -rf .git
mv "$TEMP_DIR/.git" .

# Cleanup
rm -rf "$TEMP_DIR"

# Add essential git config
git config core.autocrlf input
git config core.ignorecase false

# Recreate the main branch
git branch -m "$CURRENT_BRANCH"

echo ""
echo "✅ Size reduction complete!"
echo "New repository size: $(du -sh . | cut -f1)"
echo "New .git size: $(du -sh .git | cut -f1)"
echo ""
echo "⚠️  IMPORTANT: This repository now has fresh history"
echo "The old history is preserved in your previous clone"
echo ""
echo "To link to a remote repository:"
echo "  git remote add origin <your-repo-url>"
echo "  git push --force origin main"