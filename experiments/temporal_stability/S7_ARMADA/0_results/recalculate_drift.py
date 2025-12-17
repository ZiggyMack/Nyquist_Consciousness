#!/usr/bin/env python3
"""
Drift Recalculation from Temporal Logs
=======================================
Recovers corrupted drift values by re-embedding response texts from temporal logs.

Problem: Some runs have corrupted drift values (drift=0 or drift~78.4) due to:
- API failures during embedding (drift=0)
- Corrupted embedding vectors (drift~78.4 - random cosine distance)

Solution: Temporal logs preserve full `response_text` for every probe.
We can re-embed these texts and recalculate correct drift values.

Usage:
    py recalculate_drift.py --scan          # Identify corrupted files
    py recalculate_drift.py --fix           # Recalculate and update
    py recalculate_drift.py --dry-run       # Show what would be fixed
    py recalculate_drift.py --test <file>   # Test on single file

Author: Claude (Nyquist Consciousness Project)
Date: December 2025
"""

import os
import sys
import json
import argparse
import hashlib
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional, Any
import numpy as np

# Load environment variables
def load_env():
    """Load API keys from .env file."""
    env_paths = [
        Path(__file__).parent.parent / '.env',
        Path(__file__).parent / '.env',
    ]
    for env_path in env_paths:
        if env_path.exists():
            with open(env_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, value = line.split('=', 1)
                        os.environ[key.strip()] = value.strip().strip('"').strip("'")
            return True
    return False

load_env()

# Try to import OpenAI
try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False
    print("Warning: OpenAI not installed. Run: pip install openai")

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
TEMPORAL_LOGS_DIR = SCRIPT_DIR / "temporal_logs"
RUNS_DIR = SCRIPT_DIR / "runs"

# Validity thresholds (from build_validity_index.py)
MIN_VALID_DRIFT = 0.001  # Below this = API failure
MAX_VALID_DRIFT = 5.0    # Above this = corrupted embedding

# Embedding model
EMBEDDING_MODEL = "text-embedding-3-large"

# =============================================================================
# DRIFT CALCULATION
# =============================================================================

def compute_drift(response_embedding: np.ndarray, baseline_embedding: np.ndarray) -> float:
    """
    Compute drift as cosine distance between response and baseline embeddings.

    PFI (Persona Fidelity Index) = 1 - cosine_similarity(response, baseline)
    Range: [0, 2] where 0 = identical, 2 = opposite

    Normal drift values should be in range [0.3, 1.5] typically.
    """
    # Normalize vectors
    resp_norm = response_embedding / (np.linalg.norm(response_embedding) + 1e-10)
    base_norm = baseline_embedding / (np.linalg.norm(baseline_embedding) + 1e-10)

    # Cosine similarity
    cos_sim = np.dot(resp_norm, base_norm)

    # Cosine distance (drift)
    drift = 1 - cos_sim

    return float(drift)


def get_embedding(client, text: str) -> Optional[np.ndarray]:
    """Get embedding for text using OpenAI API."""
    try:
        response = client.embeddings.create(
            model=EMBEDDING_MODEL,
            input=text
        )
        return np.array(response.data[0].embedding)
    except Exception as e:
        print(f"  ERROR getting embedding: {e}")
        return None


# =============================================================================
# TEMPORAL LOG SCANNING
# =============================================================================

def find_temporal_logs() -> Dict[str, List[Path]]:
    """Find all temporal log files organized by experiment type."""
    logs = {
        "threshold": [],
        "nyquist": [],
        "gravity": [],
        "architecture": []
    }

    # Threshold, Nyquist, Gravity - directly in temporal_logs/
    for pattern in ["run018_threshold_*.json", "run018_nyquist_*.json", "run018_gravity_*.json"]:
        for f in TEMPORAL_LOGS_DIR.glob(pattern):
            exp_type = pattern.split("_")[1].replace("*.json", "")
            logs[exp_type].append(f)

    # Architecture - in temporal_logs/run018/ subfolder
    arch_dir = TEMPORAL_LOGS_DIR / "run018"
    if arch_dir.exists():
        for f in arch_dir.glob("run018_architecture_*.json"):
            logs["architecture"].append(f)

    return logs


def is_drift_corrupted(drift: float, response_text: str = "", baseline_text: str = "") -> Tuple[bool, str]:
    """Check if a drift value appears corrupted.

    Note: Zero drift CAN be valid if the response is identical or nearly identical
    to the baseline (e.g., "I am Claude" → "I am Claude").
    """
    # Check for high drift (always corrupted)
    if drift > MAX_VALID_DRIFT:
        return True, f"drift={drift:.6f} (above {MAX_VALID_DRIFT}, corrupted embedding)"

    # Zero or near-zero drift - check if legitimate
    if drift < MIN_VALID_DRIFT:
        # If response is very similar to baseline, this COULD be legitimate
        if response_text and baseline_text:
            # Very short responses that match baseline are legitimate
            if len(response_text) < 100 and response_text.strip() in baseline_text:
                return False, ""  # Legitimate near-identical response
            if len(baseline_text) < 100 and baseline_text.strip() in response_text:
                return False, ""  # Legitimate near-identical response

        return True, f"drift={drift:.6f} (below {MIN_VALID_DRIFT}, likely API failure)"

    return False, ""


def analyze_temporal_log(filepath: Path) -> Dict[str, Any]:
    """Analyze a temporal log file for corruption."""
    result = {
        "filepath": str(filepath),
        "filename": filepath.name,
        "has_response_text": False,
        "probe_count": 0,
        "corrupted_probes": [],
        "valid_probes": [],
        "baseline_text": None,
        "recoverable": False
    }

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        result["error"] = str(e)
        return result

    # Check for probe_sequence
    probes = data.get("probe_sequence", [])
    result["probe_count"] = len(probes)

    if not probes:
        result["error"] = "No probe_sequence found"
        return result

    # Get baseline text from top-level field if present (some formats store it there)
    baseline_text = data.get("baseline_text", "")

    # Check each probe
    for probe in probes:
        probe_id = probe.get("probe_id", "unknown")
        drift = probe.get("drift", 0)
        response_text = probe.get("response_text", "")

        if response_text:
            result["has_response_text"] = True

        if probe_id == "baseline":
            result["baseline_text"] = response_text
            baseline_text = response_text  # Use this as baseline
            continue

    # If baseline_text not found in probes, use top-level field
    if not result["baseline_text"]:
        result["baseline_text"] = baseline_text

    # Now check each probe for corruption
    for probe in probes:
        probe_id = probe.get("probe_id", "unknown")
        if probe_id == "baseline":
            continue

        drift = probe.get("drift", 0)
        response_text = probe.get("response_text", "")

        corrupted, reason = is_drift_corrupted(drift, response_text, baseline_text)
        if corrupted:
            can_recover = bool(response_text and response_text.strip())
            result["corrupted_probes"].append({
                "probe_id": probe_id,
                "drift": drift,
                "reason": reason,
                "has_response_text": bool(response_text),
                "recoverable": can_recover,
                "unrecoverable_reason": "API failure - no response generated" if not can_recover else ""
            })
        else:
            result["valid_probes"].append({
                "probe_id": probe_id,
                "drift": drift
            })

    # Count truly recoverable probes (have response text to re-embed)
    recoverable_probes = [p for p in result["corrupted_probes"] if p.get("recoverable")]
    result["recoverable_count"] = len(recoverable_probes)
    result["unrecoverable_count"] = len(result["corrupted_probes"]) - len(recoverable_probes)

    # Recoverable if we have baseline and at least one probe with response text
    result["recoverable"] = (
        result["baseline_text"] and
        result["recoverable_count"] > 0
    )

    return result


def scan_all_logs(verbose: bool = True) -> Dict[str, List[Dict]]:
    """Scan all temporal logs for corruption."""
    all_logs = find_temporal_logs()

    results = {
        "threshold": [],
        "nyquist": [],
        "gravity": [],
        "architecture": [],
        "summary": {
            "total_files": 0,
            "recoverable_files": 0,
            "corrupted_probes": 0,
            "valid_probes": 0
        }
    }

    for exp_type, files in all_logs.items():
        if verbose:
            print(f"\nScanning {exp_type.upper()} logs: {len(files)} files")

        for filepath in files:
            analysis = analyze_temporal_log(filepath)
            results[exp_type].append(analysis)
            results["summary"]["total_files"] += 1

            if analysis.get("recoverable"):
                results["summary"]["recoverable_files"] += 1
                results["summary"]["corrupted_probes"] += len(analysis["corrupted_probes"])

            results["summary"]["valid_probes"] += len(analysis.get("valid_probes", []))

            if verbose and analysis.get("corrupted_probes"):
                n_corrupted = len(analysis["corrupted_probes"])
                print(f"  {filepath.name}: {n_corrupted} corrupted probes (recoverable: {analysis.get('recoverable')})")

    return results


# =============================================================================
# DRIFT RECALCULATION
# =============================================================================

def recalculate_file(filepath: Path, client, dry_run: bool = True) -> Dict[str, Any]:
    """Recalculate drift values for a single temporal log file."""
    result = {
        "filepath": str(filepath),
        "success": False,
        "probes_fixed": 0,
        "original_drifts": {},
        "new_drifts": {}
    }

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        result["error"] = f"Failed to load: {e}"
        return result

    probes = data.get("probe_sequence", [])
    if not probes:
        result["error"] = "No probe_sequence found"
        return result

    # Find baseline
    baseline_text = None
    baseline_embedding = None
    for probe in probes:
        if probe.get("probe_id") == "baseline":
            baseline_text = probe.get("response_text", "")
            break

    if not baseline_text:
        result["error"] = "No baseline response_text found"
        return result

    print(f"  Getting baseline embedding...")
    baseline_embedding = get_embedding(client, baseline_text)
    if baseline_embedding is None:
        result["error"] = "Failed to get baseline embedding"
        return result

    # Process each probe
    for probe in probes:
        probe_id = probe.get("probe_id", "unknown")
        if probe_id == "baseline":
            continue

        original_drift = probe.get("drift", 0)
        corrupted, _ = is_drift_corrupted(original_drift)

        if not corrupted:
            continue  # Skip valid probes

        response_text = probe.get("response_text", "")
        if not response_text:
            print(f"    {probe_id}: No response_text, cannot recalculate")
            continue

        result["original_drifts"][probe_id] = original_drift

        if dry_run:
            result["new_drifts"][probe_id] = "[DRY RUN - would recalculate]"
            result["probes_fixed"] += 1
            continue

        # Get response embedding
        print(f"    Getting embedding for {probe_id}...")
        response_embedding = get_embedding(client, response_text)
        if response_embedding is None:
            print(f"    {probe_id}: Failed to get embedding")
            continue

        # Calculate new drift
        new_drift = compute_drift(response_embedding, baseline_embedding)
        result["new_drifts"][probe_id] = new_drift

        # Update probe
        probe["drift"] = new_drift
        probe["_recalculated"] = True
        probe["_original_drift"] = original_drift
        probe["_recalculated_at"] = datetime.now().isoformat()

        result["probes_fixed"] += 1
        print(f"    {probe_id}: {original_drift:.4f} → {new_drift:.4f}")

    # Update aggregate fields if not dry run
    if not dry_run and result["probes_fixed"] > 0:
        # Recalculate max_drift, peak_drift, etc.
        all_drifts = [p.get("drift", 0) for p in probes if p.get("probe_id") != "baseline"]
        if all_drifts:
            data["max_drift_achieved"] = max(all_drifts)
            data["peak_drift"] = max(all_drifts)

            # Baseline to final
            final_probe = probes[-1]
            data["baseline_to_final_drift"] = final_probe.get("drift", 0)
            data["final_drift"] = final_probe.get("drift", 0)

        data["_recalculated"] = True
        data["_recalculated_at"] = datetime.now().isoformat()

        # Save updated file
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2)

        result["success"] = True
    elif dry_run:
        result["success"] = True

    return result


def recalculate_all(dry_run: bool = True) -> Dict[str, Any]:
    """Recalculate drift for all corrupted temporal logs."""
    if not OPENAI_AVAILABLE:
        return {"error": "OpenAI not available"}

    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        return {"error": "OPENAI_API_KEY not set"}

    client = OpenAI(api_key=api_key)

    # First scan to find corrupted files
    print("Scanning for corrupted files...")
    scan_results = scan_all_logs(verbose=False)

    results = {
        "mode": "DRY RUN" if dry_run else "LIVE",
        "files_processed": 0,
        "files_fixed": 0,
        "probes_fixed": 0,
        "errors": [],
        "details": []
    }

    # Process each experiment type
    for exp_type in ["threshold", "nyquist", "gravity", "architecture"]:
        print(f"\n{'='*60}")
        print(f"Processing {exp_type.upper()} logs")
        print(f"{'='*60}")

        for analysis in scan_results[exp_type]:
            if not analysis.get("recoverable"):
                continue

            filepath = Path(analysis["filepath"])
            print(f"\nProcessing: {filepath.name}")

            result = recalculate_file(filepath, client, dry_run)
            results["files_processed"] += 1
            results["details"].append(result)

            if result.get("success") and result.get("probes_fixed", 0) > 0:
                results["files_fixed"] += 1
                results["probes_fixed"] += result["probes_fixed"]

            if result.get("error"):
                results["errors"].append({
                    "file": filepath.name,
                    "error": result["error"]
                })

    return results


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Recalculate drift values from temporal logs"
    )
    parser.add_argument("--scan", action="store_true",
                       help="Scan all temporal logs for corruption")
    parser.add_argument("--fix", action="store_true",
                       help="Recalculate and update corrupted files")
    parser.add_argument("--dry-run", action="store_true",
                       help="Show what would be fixed without making changes")
    parser.add_argument("--test", type=str,
                       help="Test recalculation on a single file")
    parser.add_argument("-v", "--verbose", action="store_true",
                       help="Verbose output")
    args = parser.parse_args()

    print("=" * 70)
    print("DRIFT RECALCULATION FROM TEMPORAL LOGS")
    print("=" * 70)

    if args.scan:
        print("\nScanning all temporal logs for corruption...")
        results = scan_all_logs(verbose=True)

        print("\n" + "=" * 70)
        print("SCAN SUMMARY")
        print("=" * 70)
        print(f"Total files scanned:    {results['summary']['total_files']}")
        print(f"Recoverable files:      {results['summary']['recoverable_files']}")
        print(f"Corrupted probes:       {results['summary']['corrupted_probes']}")
        print(f"Valid probes:           {results['summary']['valid_probes']}")

        # Save scan results
        output_file = SCRIPT_DIR / "RECALCULATION_SCAN.json"
        with open(output_file, 'w', encoding='utf-8') as f:
            # Simplify for JSON output
            json.dump({
                "timestamp": datetime.now().isoformat(),
                "summary": results["summary"],
                "recoverable_files": [
                    a["filename"] for exp in results.values()
                    if isinstance(exp, list)
                    for a in exp if a.get("recoverable")
                ]
            }, f, indent=2)
        print(f"\nScan results saved to: {output_file}")

    elif args.test:
        filepath = Path(args.test)
        if not filepath.exists():
            print(f"ERROR: File not found: {filepath}")
            return

        print(f"\nTesting recalculation on: {filepath.name}")

        if not OPENAI_AVAILABLE:
            print("ERROR: OpenAI not available")
            return

        api_key = os.environ.get("OPENAI_API_KEY")
        if not api_key:
            print("ERROR: OPENAI_API_KEY not set")
            return

        client = OpenAI(api_key=api_key)
        result = recalculate_file(filepath, client, dry_run=True)

        print("\nResult:")
        print(json.dumps(result, indent=2, default=str))

    elif args.fix or args.dry_run:
        results = recalculate_all(dry_run=args.dry_run)

        print("\n" + "=" * 70)
        print(f"RECALCULATION {'SIMULATION' if args.dry_run else 'COMPLETE'}")
        print("=" * 70)
        print(f"Mode:               {results.get('mode', 'unknown')}")
        print(f"Files processed:    {results.get('files_processed', 0)}")
        print(f"Files fixed:        {results.get('files_fixed', 0)}")
        print(f"Probes fixed:       {results.get('probes_fixed', 0)}")

        if results.get("errors"):
            print(f"\nErrors ({len(results['errors'])}):")
            for err in results["errors"][:5]:
                print(f"  {err['file']}: {err['error']}")
            if len(results["errors"]) > 5:
                print(f"  ... and {len(results['errors']) - 5} more")

        if args.dry_run:
            print("\n[DRY RUN] No files were modified.")
            print("Run with --fix to apply changes.")

    else:
        parser.print_help()
        print("\nExamples:")
        print("  py recalculate_drift.py --scan        # Find corrupted files")
        print("  py recalculate_drift.py --dry-run     # Preview fixes")
        print("  py recalculate_drift.py --fix         # Apply fixes")


if __name__ == "__main__":
    main()
