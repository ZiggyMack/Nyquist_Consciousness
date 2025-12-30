"""
RECALCULATE DRIFT VALUES - Migrate from Keyword RMS to Cosine Embeddings
=========================================================================

This script recalculates all drift values in S7_run_020B_CURRENT.json using
the canonical cosine embedding methodology from run023b/drift_calculator.py.

PROBLEM:
- Run 020B claimed "methodology": "cosine_embedding" but actually used keyword RMS
- All 48+ sessions have drift values calculated with the wrong methodology
- The raw data (baseline_text, final_text, conversation_log) is intact and valid

SOLUTION:
- Recalculate all drift values using OpenAI embeddings + cosine distance
- Update peak_drift, final_drift, drift_sequence, baseline_to_final_drift
- Fix the methodology field to reflect the actual calculation used

USAGE:
    # Dry run - see what would change without modifying
    python recalculate_drift_cosine.py --dry-run

    # Actually recalculate and save
    python recalculate_drift_cosine.py --execute

    # Recalculate specific sessions only
    python recalculate_drift_cosine.py --execute --session control_4cc0d1f7

Author: Claude (S7 ARMADA Audit)
Date: December 27, 2025
"""

import os
import sys
import json
import argparse
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Optional

# Add lib path
sys.path.insert(0, str(Path(__file__).parent.parent / "1_CALIBRATION" / "lib"))

try:
    from drift_calculator import (
        calculate_drift,
        classify_zone,
        classify_stability,
        EVENT_HORIZON,
        clear_embedding_cache,
    )
    print("[OK] Imported drift_calculator from 1_CALIBRATION/lib/")
except ImportError as e:
    print(f"[ERROR] Could not import drift_calculator: {e}")
    print("  Make sure 1_CALIBRATION/lib/drift_calculator.py exists")
    sys.exit(1)

# Load .env for API keys
try:
    from dotenv import load_dotenv
    env_path = Path(__file__).parent.parent / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f"[OK] Loaded API keys from {env_path}")
except ImportError:
    print("[WARN] dotenv not available, using environment variables directly")

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
RESULTS_FILE = RESULTS_DIR / "S7_run_020B_CURRENT.json"
BACKUP_FILE = RESULTS_DIR / f"S7_run_020B_BEFORE_COSINE_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"


def load_data() -> dict:
    """Load the current results file."""
    if not RESULTS_FILE.exists():
        print(f"[ERROR] Results file not found: {RESULTS_FILE}")
        sys.exit(1)

    with open(RESULTS_FILE, 'r', encoding='utf-8') as f:
        return json.load(f)


def recalculate_session(session: dict, dry_run: bool = True) -> dict:
    """
    Recalculate drift values for a single session using cosine embeddings.

    Returns the updated session dict with new drift values.
    """
    subject_id = session.get("subject_id", "unknown")
    baseline_text = session.get("baseline_text", "")
    final_text = session.get("final_text", "")
    conversation_log = session.get("conversation_log", [])

    if not baseline_text:
        print(f"  [SKIP] {subject_id}: No baseline_text")
        return session

    # Calculate baseline-to-final drift
    old_b2f = session.get("baseline_to_final_drift", 0)
    new_b2f = calculate_drift(baseline_text, final_text, dry_run=dry_run)

    # Recalculate drift sequence from conversation log
    old_sequence = session.get("drift_sequence", [])
    new_sequence = []

    for entry in conversation_log:
        if entry.get("speaker") == "subject":
            content = entry.get("content", "")
            if content:
                drift = calculate_drift(baseline_text, content, dry_run=dry_run)
                new_sequence.append(drift)
            else:
                new_sequence.append(0.0)

    # Calculate peak and final drift
    old_peak = session.get("peak_drift", 0)
    old_final = session.get("final_drift", 0)
    new_peak = max(new_sequence) if new_sequence else 0.0
    new_final = new_sequence[-1] if new_sequence else 0.0

    # Report changes
    print(f"  {subject_id}:")
    print(f"    baseline_to_final: {old_b2f:.4f} -> {new_b2f:.4f}")
    print(f"    peak_drift:        {old_peak:.4f} -> {new_peak:.4f}")
    print(f"    final_drift:       {old_final:.4f} -> {new_final:.4f}")
    print(f"    sequence length:   {len(old_sequence)} -> {len(new_sequence)}")

    # Update session
    session["baseline_to_final_drift"] = new_b2f
    session["drift_sequence"] = new_sequence
    session["peak_drift"] = new_peak
    session["final_drift"] = new_final
    session["stability"] = classify_stability(new_peak)
    session["zone"] = classify_zone(new_peak)

    return session


def main():
    parser = argparse.ArgumentParser(description="Recalculate drift values with cosine embeddings")
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without saving")
    parser.add_argument("--execute", action="store_true", help="Actually recalculate and save")
    parser.add_argument("--session", type=str, help="Recalculate specific session only")
    parser.add_argument("--limit", type=int, default=0, help="Limit number of sessions to process")
    args = parser.parse_args()

    if not args.dry_run and not args.execute:
        print("Usage: python recalculate_drift_cosine.py [--dry-run | --execute]")
        print("  --dry-run: Preview changes without API calls or saving")
        print("  --execute: Actually recalculate with real embeddings and save")
        sys.exit(0)

    # Check for OpenAI API key (needed for real embeddings)
    if args.execute and not os.environ.get("OPENAI_API_KEY"):
        print("[ERROR] OPENAI_API_KEY not set. Required for embedding calculations.")
        sys.exit(1)

    print("=" * 70)
    print("DRIFT RECALCULATION - Keyword RMS -> Cosine Embeddings")
    print("=" * 70)
    print(f"Mode: {'DRY RUN (fake embeddings)' if args.dry_run else 'EXECUTE (real embeddings)'}")
    print(f"Event Horizon: {EVENT_HORIZON}")
    print()

    # Load data
    data = load_data()
    results = data.get("results", [])
    print(f"Loaded {len(results)} sessions from {RESULTS_FILE}")

    # Filter to specific session if requested
    if args.session:
        results = [r for r in results if r.get("subject_id") == args.session]
        print(f"Filtered to session: {args.session} ({len(results)} found)")

    # Apply limit if requested
    if args.limit > 0:
        results = results[:args.limit]
        print(f"Limited to first {args.limit} sessions")

    print()

    # Recalculate each session
    updated_count = 0
    for i, session in enumerate(results):
        print(f"\n[{i+1}/{len(results)}]")
        session = recalculate_session(session, dry_run=args.dry_run)
        updated_count += 1

    print()
    print("=" * 70)
    print(f"Processed: {updated_count} sessions")

    if args.execute:
        # Backup original
        print(f"\nBacking up to: {BACKUP_FILE}")
        with open(BACKUP_FILE, 'w', encoding='utf-8') as f:
            json.dump(load_data(), f, indent=2)  # Re-load for clean backup

        # Update metadata
        data["methodology"] = "cosine_embedding"
        data["methodology_note"] = f"Recalculated from keyword_rms on {datetime.now().isoformat()}"
        data["event_horizon"] = EVENT_HORIZON
        data["last_updated"] = datetime.now().isoformat()

        # Put updated results back (in case we filtered)
        if args.session:
            # Replace just the matching session
            for i, r in enumerate(data["results"]):
                if r.get("subject_id") == args.session:
                    data["results"][i] = results[0]
                    break
        elif args.limit > 0:
            # Replace first N sessions
            data["results"][:args.limit] = results
        else:
            # Replace all
            data["results"] = results

        # Save
        print(f"Saving to: {RESULTS_FILE}")
        with open(RESULTS_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2)

        print("\n[DONE] Drift values recalculated with cosine embeddings!")
    else:
        print("\n[DRY RUN] No changes saved. Use --execute to apply.")

    print("=" * 70)


if __name__ == "__main__":
    main()


# =============================================================================
# Related Documents
# =============================================================================
# - ARCHITECTURE_MATRIX.json: Fleet configuration (ONE SOURCE OF TRUTH)
# - 5_METHODOLOGY_DOMAINS.md: Methodology reference (Event Horizon = 0.80)
# - 1_CALIBRATION/lib/drift_calculator.py: Canonical cosine drift calculation
# - run020_tribunal_B.py: Original experiment script (needs update)
# - S7_run_020B_CURRENT.json: Data file being recalculated
# =============================================================================
