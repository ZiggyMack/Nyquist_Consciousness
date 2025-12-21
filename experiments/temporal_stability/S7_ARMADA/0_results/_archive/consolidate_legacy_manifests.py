#!/usr/bin/env python3
"""
LEGACY MANIFEST CONSOLIDATOR
=============================
Generates manifests for legacy runs (006-017) which have different data structures
than the newer 018+ format.

Legacy formats handled:
- Run 006-009: results[model].protocols[protocol].turns[] with drift values
- Run 010-012: Similar but with recursive loop data
- Run 013-017: Various formats including boundary mapping, rescue, settling time

Usage:
    python consolidate_legacy_manifests.py           # Process all legacy runs
    python consolidate_legacy_manifests.py --run 009 # Process specific run
    python consolidate_legacy_manifests.py --dry-run # Preview without writing
"""

import json
import argparse
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from typing import Dict, List, Any, Optional, Tuple

# Paths
BASE_DIR = Path(__file__).resolve().parent
LEGACY_DIR = BASE_DIR / "runs" / "legacy_runs"
MANIFEST_DIR = BASE_DIR / "manifests"
ANALYSIS_DIR = BASE_DIR / "analysis"

# Event Horizon threshold
# UPDATED December 2025: Cosine methodology
# See: 15_IRON_CLAD_FOUNDATION/results/COSINE_EVENT_HORIZON_CALIBRATION.md
EVENT_HORIZON = 0.80  # Cosine threshold (was 1.23 for keyword RMS)

# Provider mapping
PROVIDER_MAP = {
    "claude": "claude",
    "gpt": "gpt",
    "o3": "gpt",
    "o4": "gpt",
    "gemini": "gemini",
    "grok": "grok",
    "deepseek": "together",
    "llama": "together",
    "mistral": "together",
}


def get_provider(model_name: str) -> str:
    """Map model name to provider."""
    model_lower = model_name.lower()
    for prefix, provider in PROVIDER_MAP.items():
        if model_lower.startswith(prefix):
            return provider
    return "unknown"


def extract_drift_from_turns(turns: List[Dict]) -> Tuple[float, float, List[float]]:
    """Extract peak drift, final drift, and drift sequence from turns."""
    drifts = []
    for turn in turns:
        drift = turn.get('drift', turn.get('drift_lucian', 0))
        if drift:
            drifts.append(drift)

    if not drifts:
        return 0.0, 0.0, []

    return max(drifts), drifts[-1], drifts


def process_legacy_009_format(data: Dict, filename: str) -> List[Dict]:
    """Process Run 006-009 format: results[model].protocols[protocol].turns[]"""
    entries = []
    results = data.get('results', {})
    timestamp = data.get('timestamp', filename.split('_')[-2] + '_' + filename.split('_')[-1].replace('.json', ''))

    for model_name, model_data in results.items():
        if not isinstance(model_data, dict):
            continue

        provider = model_data.get('provider', get_provider(model_name))
        protocols = model_data.get('protocols', {})

        for protocol_name, protocol_data in protocols.items():
            if not isinstance(protocol_data, dict):
                continue

            turns = protocol_data.get('turns', [])
            peak_drift, final_drift, drift_seq = extract_drift_from_turns(turns)

            # Skip if no valid drift data
            if peak_drift == 0:
                continue

            entry = {
                "drift": final_drift,
                "peak_drift": peak_drift,
                "timestamp": timestamp,
                "file": filename,
                "model": model_name,
                "provider": provider,
                "protocol": protocol_name,
                "probe_count": len(turns),
                "catastrophic": peak_drift >= EVENT_HORIZON,
                "drift_sequence": drift_seq[:10] if len(drift_seq) > 10 else drift_seq  # Truncate long sequences
            }

            # Extract meta info if available
            meta = protocol_data.get('meta', {})
            if meta:
                entry["status"] = meta.get('status', 'unknown')
                entry["recovery_attempts"] = meta.get('recovery_attempts', 0)

            entries.append(entry)

    return entries


def process_run_017_format(data: Dict, filename: str) -> List[Dict]:
    """Process Run 017 aggregated format: by_persona[persona].by_model[model]"""
    entries = []
    by_persona = data.get('by_persona', {})
    timestamp = data.get('aggregation_timestamp', '')

    for persona_name, persona_data in by_persona.items():
        by_model = persona_data.get('by_model', {})

        for model_name, model_data in by_model.items():
            provider = get_provider(model_name)

            # Get drift metrics
            peak_drift = model_data.get('peak_drift', model_data.get('max_drift', 0))
            avg_drift = model_data.get('average_drift', 0)

            if peak_drift == 0:
                continue

            entry = {
                "drift": avg_drift,
                "peak_drift": peak_drift,
                "timestamp": timestamp,
                "file": filename,
                "model": model_name,
                "provider": provider,
                "persona": persona_name,
                "probe_count": model_data.get('probe_count', model_data.get('sample_count', 0)),
                "catastrophic": peak_drift >= EVENT_HORIZON,
                "settling_time": model_data.get('settling_time'),
                "recovery_ratio": model_data.get('recovery_ratio')
            }
            entries.append(entry)

    return entries


def process_boundary_format(data: Dict, filename: str) -> List[Dict]:
    """Process Run 013 boundary mapping format."""
    entries = []
    timestamp = data.get('timestamp', '')

    # Check for subjects format
    subjects = data.get('subjects', [])
    for subj in subjects:
        entry = {
            "drift": subj.get('baseline_to_final_drift', subj.get('final_drift', 0)),
            "peak_drift": subj.get('peak_drift', 0),
            "timestamp": timestamp,
            "file": filename,
            "model": subj.get('model', 'unknown'),
            "provider": subj.get('provider', get_provider(subj.get('model', ''))),
            "probe_count": len(subj.get('drift_sequence', [])),
            "catastrophic": subj.get('catastrophic_reached', False),
            "boundary_zone": subj.get('boundary_zone'),
        }
        if entry['peak_drift'] > 0:
            entries.append(entry)

    # Check for results dict format
    results = data.get('results', {})
    if isinstance(results, dict) and 'peak_drift' in results:
        entry = {
            "drift": results.get('final_drift', 0),
            "peak_drift": results.get('peak_drift', 0),
            "timestamp": timestamp,
            "file": filename,
            "model": data.get('model', 'unknown'),
            "provider": get_provider(data.get('model', '')),
            "probe_count": results.get('probes_executed', 0),
            "catastrophic": results.get('peak_drift', 0) >= EVENT_HORIZON,
        }
        if entry['peak_drift'] > 0:
            entries.append(entry)

    return entries


def process_run_006_format(data: Dict, filename: str) -> List[Dict]:
    """Process Run 006 armada format: model_summaries[model].probes[]"""
    entries = []
    model_summaries = data.get('model_summaries', {})
    timestamp = data.get('start_time', '')[:19].replace('T', '_').replace('-', '').replace(':', '')

    for model_key, model_data in model_summaries.items():
        if not isinstance(model_data, dict):
            continue

        provider = model_data.get('provider', get_provider(model_key))
        model_name = model_data.get('model_name', model_key)
        probes = model_data.get('probes', [])

        # Extract drifts from probes
        drifts = [p.get('drift', 0) for p in probes if p.get('drift')]
        if not drifts:
            continue

        peak_drift = max(drifts)
        final_drift = drifts[-1] if drifts else 0

        entry = {
            "drift": final_drift,
            "peak_drift": peak_drift,
            "timestamp": timestamp,
            "file": filename,
            "model": model_name,
            "provider": provider,
            "probe_count": len(probes),
            "catastrophic": peak_drift >= EVENT_HORIZON,
            "drift_sequence": drifts[:10] if len(drifts) > 10 else drifts
        }
        entries.append(entry)

    return entries


def process_run_010_format(data: Dict, filename: str) -> List[Dict]:
    """Process Run 010-012 recursive format: results[model] with trajectory data"""
    entries = []
    results = data.get('results', {})
    timestamp = data.get('timestamp', '')[:19].replace('T', '_').replace('-', '').replace(':', '')

    # Handle results as list
    if isinstance(results, list):
        for i, model_data in enumerate(results):
            if not isinstance(model_data, dict):
                continue
            model_key = model_data.get('model', model_data.get('ship', f'model_{i}'))
            results = {model_key: model_data}
            break  # Process as single-model format
        else:
            return entries

    for model_key, model_data in results.items():
        if not isinstance(model_data, dict):
            continue

        provider = model_data.get('provider', get_provider(model_key))

        # Get trajectory data
        trajectory = model_data.get('trajectory', [])
        if not trajectory:
            # Try turns format
            trajectory = model_data.get('turns', [])

        drifts = []
        for point in trajectory:
            if isinstance(point, dict):
                drift = point.get('drift', point.get('composite_drift', 0))
            else:
                drift = point  # Might be just a number
            if drift:
                drifts.append(drift)

        if not drifts:
            # Check for peak_drift directly
            peak_drift = model_data.get('peak_drift', model_data.get('max_drift', 0))
            if peak_drift:
                drifts = [peak_drift]

        if not drifts:
            continue

        peak_drift = max(drifts)
        final_drift = drifts[-1] if drifts else 0

        entry = {
            "drift": final_drift,
            "peak_drift": peak_drift,
            "timestamp": timestamp,
            "file": filename,
            "model": model_key,
            "provider": provider,
            "probe_count": len(trajectory) or model_data.get('turns_completed', 0),
            "catastrophic": peak_drift >= EVENT_HORIZON,
        }

        # Add meta feedback if present
        if 'meta_feedback' in model_data:
            entry['has_meta_feedback'] = True

        entries.append(entry)

    # Also check meta_feedback_collection at top level
    meta_collection = data.get('meta_feedback_collection', [])
    for feedback in meta_collection:
        ship = feedback.get('ship', '')
        # Find corresponding result
        if ship in results:
            continue  # Already processed
        entry = {
            "drift": 0,
            "peak_drift": 0,
            "timestamp": timestamp,
            "file": filename,
            "model": ship,
            "provider": feedback.get('provider', get_provider(ship)),
            "probe_count": 0,
            "catastrophic": False,
            "has_meta_feedback": True,
        }
        # Don't add entries with no drift data

    return entries


def process_run_013_ships_format(data: Dict, filename: str) -> List[Dict]:
    """Process Run 013+ ships format: ships[].probes[]"""
    entries = []
    ships = data.get('ships', [])
    timestamp = data.get('timestamp', '')

    for ship in ships:
        if not isinstance(ship, dict):
            continue

        provider = ship.get('provider', get_provider(ship.get('ship', '')))
        model = ship.get('model', ship.get('ship', 'unknown'))
        probes = ship.get('probes', [])

        # Extract drifts
        drifts = []
        for probe in probes:
            drift = probe.get('drift', probe.get('composite_drift', 0))
            if drift:
                drifts.append(drift)

        if not drifts:
            continue

        peak_drift = max(drifts)
        final_drift = drifts[-1]

        entry = {
            "drift": final_drift,
            "peak_drift": peak_drift,
            "timestamp": timestamp,
            "file": filename,
            "model": model,
            "provider": provider,
            "probe_count": len(probes),
            "catastrophic": peak_drift >= EVENT_HORIZON,
            "drift_sequence": drifts[:10] if len(drifts) > 10 else drifts
        }
        entries.append(entry)

    return entries


def process_legacy_file(filepath: Path) -> Tuple[str, List[Dict]]:
    """Process a legacy file and return (experiment_name, entries)."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        print(f"  Error loading {filepath.name}: {e}")
        return "unknown", []

    filename = filepath.name

    # Determine format by checking keys
    if 'by_persona' in data:
        # Run 017 format
        return "context_damping", process_run_017_format(data, filename)

    elif 'model_summaries' in data:
        # Run 006 armada format
        return "foundation", process_run_006_format(data, filename)

    elif 'ships' in data and isinstance(data.get('ships'), list):
        # Run 013+ ships format
        exp_name = data.get('name', 'boundary')
        return exp_name, process_run_013_ships_format(data, filename)

    elif 'results' in data and isinstance(data['results'], dict):
        # Check if it's the 006-012 protocol format
        first_result = list(data['results'].values())[0] if data['results'] else {}
        if isinstance(first_result, dict) and 'protocols' in first_result:
            # Determine experiment from run_id or filename
            run_id = data.get('run_id', filename)
            if 'drain' in run_id.lower() or 'drain' in filename.lower():
                return "drain", process_legacy_009_format(data, filename)
            elif 'recursive' in run_id.lower() or 'recursive' in filename.lower():
                return "recursive", process_legacy_009_format(data, filename)
            elif 'persona' in run_id.lower() or 'persona' in filename.lower():
                return "persona", process_legacy_009_format(data, filename)
            else:
                return "foundation", process_legacy_009_format(data, filename)
        elif isinstance(first_result, dict):
            # Could be run 010-012 format
            return "calibration", process_run_010_format(data, filename)

    elif 'subjects' in data:
        # Subjects format (run 013+)
        return "boundary", process_boundary_format(data, filename)

    # Try various extractors as fallback
    entries = process_run_006_format(data, filename)
    if entries:
        return "legacy", entries

    entries = process_run_010_format(data, filename)
    if entries:
        return "legacy", entries

    entries = process_run_013_ships_format(data, filename)
    if entries:
        return "legacy", entries

    entries = process_boundary_format(data, filename)
    if entries:
        return "legacy", entries

    print(f"  Unknown format for {filename}")
    return "unknown", []


def consolidate_legacy_run(run_id: str, dry_run: bool = False) -> Dict:
    """Consolidate all files for a legacy run into a manifest."""
    print(f"\nProcessing Run {run_id}...")

    # Find all files for this run
    patterns = [
        f"S7_run_{run_id}_*.json",
        f"S7_armada_run_{run_id}*.json",
        f"*_run_{run_id}_*.json",
    ]

    files = []
    for pattern in patterns:
        files.extend(LEGACY_DIR.glob(pattern))

    # Also check analysis directory
    for pattern in patterns:
        files.extend(ANALYSIS_DIR.glob(pattern))

    files = list(set(files))  # Deduplicate

    if not files:
        print(f"  No files found for run {run_id}")
        return {}

    print(f"  Found {len(files)} files")

    # Build manifest
    manifest = {
        "run": run_id,
        "generated": datetime.now().isoformat(),
        "source": "legacy_consolidation",
        "summary": {
            "total_files": len(files),
            "experiments": set(),
            "models_tested": set(),
            "files_processed": [],
        },
        "experiments": defaultdict(lambda: defaultdict(list))
    }

    total_entries = 0

    for filepath in sorted(files):
        experiment, entries = process_legacy_file(filepath)

        if not entries:
            continue

        manifest["summary"]["files_processed"].append(filepath.name)
        manifest["summary"]["experiments"].add(experiment)

        for entry in entries:
            model = entry.get('model', 'unknown')
            manifest["summary"]["models_tested"].add(model)
            manifest["experiments"][experiment][model].append(entry)
            total_entries += 1

    # Convert sets to lists
    manifest["summary"]["experiments"] = sorted(manifest["summary"]["experiments"])
    manifest["summary"]["models_tested"] = sorted(manifest["summary"]["models_tested"])

    # Convert defaultdicts to regular dicts
    manifest["experiments"] = {
        exp: dict(models) for exp, models in manifest["experiments"].items()
    }

    print(f"  Extracted {total_entries} trajectory entries")
    print(f"  Experiments: {manifest['summary']['experiments']}")
    print(f"  Models: {len(manifest['summary']['models_tested'])}")

    if not dry_run and total_entries > 0:
        output_path = MANIFEST_DIR / f"RUN_{run_id}_DRIFT_MANIFEST.json"
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(manifest, f, indent=2, ensure_ascii=False)
        print(f"  Wrote manifest to {output_path.name}")

    return manifest


def main():
    parser = argparse.ArgumentParser(description='Consolidate legacy run manifests')
    parser.add_argument('--run', type=str, help='Process specific run (e.g., 009)')
    parser.add_argument('--dry-run', action='store_true', help='Preview without writing')
    args = parser.parse_args()

    print("=" * 60)
    print("LEGACY MANIFEST CONSOLIDATOR")
    print("=" * 60)

    if args.run:
        runs = [args.run]
    else:
        # Process all legacy runs that don't have manifests
        runs = ['006', '007', '008', '009', '010', '011', '012', '013', '014', '015', '016', '017']

    total_processed = 0
    total_entries = 0

    for run_id in runs:
        # Check if manifest already exists
        existing = MANIFEST_DIR / f"RUN_{run_id}_DRIFT_MANIFEST.json"
        if existing.exists() and not args.run:
            print(f"\nSkipping Run {run_id} - manifest already exists")
            continue

        manifest = consolidate_legacy_run(run_id, dry_run=args.dry_run)
        if manifest:
            total_processed += 1
            # Count entries
            for exp_data in manifest.get('experiments', {}).values():
                for model_data in exp_data.values():
                    total_entries += len(model_data)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Runs processed: {total_processed}")
    print(f"Total entries: {total_entries}")
    if args.dry_run:
        print("\nThis was a DRY RUN - no files written")


if __name__ == '__main__':
    main()
