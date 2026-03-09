#!/bin/bash
# ============================================================================
# Claude Code Session Backup Script
# ============================================================================
# Copies all session JSONL transcript files from Claude Code's storage to a
# safe location inside the repo. Prevents loss from VSCode extension updates.
#
# Usage:  bash backup_claude_sessions.sh
#         ./backup_claude_sessions.sh
#
# Source: ~/.claude/projects/d--Documents-Nyquist-Consciousness/*.jsonl
# Dest:   .claude-session-backups/ (gitignored)
# ============================================================================

SOURCE_DIR="C:/Users/Stephen/.claude/projects/d--Documents-Nyquist-Consciousness"
BACKUP_DIR="d:/Documents/Nyquist_Consciousness/.claude-session-backups"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

mkdir -p "$BACKUP_DIR"

echo "=== Claude Session Backup ==="
echo "Source: $SOURCE_DIR"
echo "Backup: $BACKUP_DIR"
echo ""

copied=0
skipped=0

for src in "$SOURCE_DIR"/*.jsonl; do
    [ -f "$src" ] || continue

    filename=$(basename "$src")
    uuid="${filename%.jsonl}"
    dest_latest="$BACKUP_DIR/${uuid}.jsonl"
    dest_timestamped="$BACKUP_DIR/${uuid}_${TIMESTAMP}.jsonl"

    # Get source size for display
    src_size=$(du -h "$src" 2>/dev/null | cut -f1)

    # Only copy if source is newer than the latest backup
    if [ -f "$dest_latest" ]; then
        if [ "$src" -nt "$dest_latest" ]; then
            # Source is newer - make a timestamped backup of the old one, then copy new
            mv "$dest_latest" "$dest_timestamped.old"
            cp "$src" "$dest_latest"
            echo "[UPDATED] $uuid ($src_size)"
            copied=$((copied + 1))
        else
            echo "[SKIP]    $uuid ($src_size) - backup is current"
            skipped=$((skipped + 1))
        fi
    else
        # First backup of this session
        cp "$src" "$dest_latest"
        echo "[NEW]     $uuid ($src_size)"
        copied=$((copied + 1))
    fi
done

echo ""
echo "Done. Copied: $copied, Skipped: $skipped"
echo "Backups stored in: $BACKUP_DIR"
