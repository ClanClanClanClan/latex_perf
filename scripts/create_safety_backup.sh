#!/bin/bash
# CRITICAL: Complete safety backup before ANY cleanup action

# Create timestamped backup
BACKUP_DATE=$(date +%Y%m%d_%H%M%S)
BACKUP_DIR="../LP_v24_FULL_BACKUP_$BACKUP_DATE"

echo "=== LaTeX Perfectionist v24 - Complete Safety Backup ==="
echo "Creating backup at: $BACKUP_DIR"
echo "This may take a few minutes..."

# Create backup
cp -R . "$BACKUP_DIR"

# Create backup manifest
echo "Creating backup manifest..."
find "$BACKUP_DIR" -type f | sort > "$BACKUP_DIR/backup_manifest.txt"

# Count files
TOTAL_FILES=$(wc -l < "$BACKUP_DIR/backup_manifest.txt")
BACKUP_SIZE=$(du -sh "$BACKUP_DIR" | cut -f1)

echo ""
echo "=== Backup Complete ==="
echo "Location: $BACKUP_DIR"
echo "Total files: $TOTAL_FILES"
echo "Total size: $BACKUP_SIZE"
echo "Manifest: $BACKUP_DIR/backup_manifest.txt"

# Create restoration script
cat > "$BACKUP_DIR/RESTORE_IF_NEEDED.sh" << 'EOF'
#!/bin/bash
echo "=== LaTeX Perfectionist v24 - Full Restoration Script ==="
echo "This will restore the entire project from backup."
echo "WARNING: This will overwrite all current files!"
echo ""
echo "Continue? (yes/no)"
read -r response
if [[ "$response" == "yes" ]]; then
    echo "Starting restoration..."
    cp -R ./* ../Scripts/
    echo "Restoration complete!"
else
    echo "Restoration cancelled"
fi
EOF
chmod +x "$BACKUP_DIR/RESTORE_IF_NEEDED.sh"

echo ""
echo "Created restoration script: $BACKUP_DIR/RESTORE_IF_NEEDED.sh"
echo ""
echo "BACKUP SUCCESSFUL - Safe to proceed with cleanup"