"""
Test A′ — Replication Baseline & Noise Floor
=============================================
Runs 18 CFA Trinity transitions (3 stances × 2 phases × 3 replications)
to measure the instrument's test-retest variance (σ).

Design (from PREREG_OPUS_TEST_A_PRIME_AND_C.md):
  - CT→MdN (CT leg): expected low-noise
  - G→MdN (MdN leg): expected high-noise (PF_I 8.07→2.22 swing)
  - CT→MdN control: baseline without identity
  Each run 3× in both Phase 1 (Schema A) and Phase 2 (Schema B).

σ is the null for every Test A claim. Nothing from Test A is
interpretable without it.

Usage: python run_test_a_prime.py [--dry-run] [--pause N]
"""
import subprocess
import sys
import json
import time
from pathlib import Path
from datetime import datetime

SCRIPT = Path(__file__).parent / "run_cfa_trinity_v3.py"
RUNS_DIR = Path(__file__).parent.parent / "0_results" / "runs"
MANIFEST_PATH = Path(__file__).parent / "test_a_prime_manifest.json"
PAUSE_BETWEEN = 5

BATCHES = [
    # Schema A (Phase 1) — 9 runs
    {"label": "A' CT->MdN P1 external", "count": 3,
     "group": "ct_vs_mdn_p1_external",
     "args": ["--stance", "ct_vs_mdn", "--phase", "1", "--external-identities",
              "--skip-exit-survey", "--component", "1"]},
    {"label": "A' G->MdN P1 external", "count": 3,
     "group": "g_vs_mdn_p1_external",
     "args": ["--stance", "g_vs_mdn", "--phase", "1", "--external-identities",
              "--skip-exit-survey", "--component", "1"]},
    {"label": "A' CT->MdN P1 control", "count": 3,
     "group": "ct_vs_mdn_p1_control",
     "args": ["--stance", "ct_vs_mdn", "--phase", "1", "--control",
              "--skip-exit-survey", "--component", "1"]},

    # Schema B (Phase 2) — 9 runs
    {"label": "A' CT->MdN P2 external", "count": 3,
     "group": "ct_vs_mdn_p2_external",
     "args": ["--stance", "ct_vs_mdn", "--phase", "2", "--external-identities",
              "--skip-exit-survey", "--preset", "ct", "--component", "1"]},
    {"label": "A' G->MdN P2 external", "count": 3,
     "group": "g_vs_mdn_p2_external",
     "args": ["--stance", "g_vs_mdn", "--phase", "2", "--external-identities",
              "--skip-exit-survey", "--preset", "g", "--component", "1"]},
    {"label": "A' CT->MdN P2 control", "count": 3,
     "group": "ct_vs_mdn_p2_control",
     "args": ["--stance", "ct_vs_mdn", "--phase", "2", "--control",
              "--skip-exit-survey", "--preset", "ct", "--component", "1"]},
]

TOTAL_RUNS = sum(b["count"] for b in BATCHES)


def get_latest_run_file():
    """Get the most recently modified run file."""
    files = list(RUNS_DIR.glob("S7_cfa_trinity_*.json"))
    if not files:
        return None
    return max(files, key=lambda f: f.stat().st_mtime)


def annotate_run(filepath, experiment, group, rep_id):
    """Inject experiment metadata into a run file."""
    with open(filepath, encoding="utf-8") as f:
        data = json.load(f)

    data["experiment"] = experiment
    data["replication_group"] = group
    data["replication_id"] = rep_id

    with open(filepath, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")

    import argparse
    parser = argparse.ArgumentParser(description="Test A' Replication Batch Runner")
    parser.add_argument("--dry-run", action="store_true",
                       help="Show what would run without executing")
    parser.add_argument("--pause", type=int, default=PAUSE_BETWEEN,
                       help=f"Seconds between runs (default: {PAUSE_BETWEEN})")
    args = parser.parse_args()

    print("=" * 70)
    print("TEST A' — REPLICATION BASELINE & NOISE FLOOR")
    print("=" * 70)
    print(f"Total runs: {TOTAL_RUNS}")
    print(f"Design: 3 transitions x 3 reps x 2 schemas")
    print(f"Script: {SCRIPT}")
    print(f"Output: {RUNS_DIR}")
    print(f"Pause: {args.pause}s between runs")
    if args.dry_run:
        print("\n[DRY RUN — no API calls will be made]")
    print()

    batch_start = datetime.now()
    manifest = {
        "experiment": "test_a_prime",
        "started": batch_start.isoformat(),
        "design": "3 transitions x 3 replications x 2 schemas = 18 runs",
        "prereg": "SYNC_IN/PREREG_OPUS_TEST_A_PRIME_AND_C.md",
        "groups": {},
        "files": []
    }

    run_number = 0
    failures = []

    for batch in BATCHES:
        print(f"\n{'=' * 70}")
        print(f"  BATCH: {batch['label']} ({batch['count']} runs)")
        print(f"  Group: {batch['group']}")
        print(f"{'=' * 70}")

        if args.dry_run:
            cmd = [sys.executable, str(SCRIPT)] + batch["args"]
            print(f"  Would run: {' '.join(cmd)}")
            print(f"  x{batch['count']} replications")
            continue

        group_files = []

        for rep in range(1, batch["count"] + 1):
            run_number += 1
            print(f"\n  --- Run {run_number}/{TOTAL_RUNS} (rep {rep}/{batch['count']}) ---")

            before_file = get_latest_run_file()

            cmd = [sys.executable, str(SCRIPT)] + batch["args"]
            run_start = time.time()

            result = subprocess.run(
                cmd,
                capture_output=False,
                text=True,
                encoding="utf-8",
            )

            elapsed = time.time() - run_start

            if result.returncode != 0:
                print(f"  [!] Run {run_number} FAILED (exit {result.returncode}, {elapsed:.0f}s)")
                failures.append({"run": run_number, "batch": batch["label"], "rep": rep})
                continue

            # Find the new file
            after_file = get_latest_run_file()
            if after_file and after_file != before_file:
                annotate_run(after_file, "test_a_prime", batch["group"], rep)
                group_files.append(after_file.name)
                print(f"  [+] Run {run_number} COMPLETE ({elapsed:.0f}s) -> {after_file.name}")
                print(f"      Tagged: experiment=test_a_prime, group={batch['group']}, rep={rep}")
            else:
                print(f"  [?] Run {run_number} completed but no new file detected ({elapsed:.0f}s)")
                failures.append({"run": run_number, "batch": batch["label"], "rep": rep,
                                "note": "no output file"})

            if run_number < TOTAL_RUNS:
                print(f"  Pausing {args.pause}s...")
                time.sleep(args.pause)

        manifest["groups"][batch["group"]] = group_files
        manifest["files"].extend(group_files)

    batch_end = datetime.now()
    manifest["completed"] = batch_end.isoformat()
    manifest["duration_minutes"] = (batch_end - batch_start).total_seconds() / 60
    manifest["failures"] = failures

    if not args.dry_run:
        with open(MANIFEST_PATH, "w", encoding="utf-8") as f:
            json.dump(manifest, f, indent=2, ensure_ascii=False)
        print(f"\n{'=' * 70}")
        print(f"BATCH COMPLETE")
        print(f"{'=' * 70}")
        print(f"  Runs attempted: {TOTAL_RUNS}")
        print(f"  Files produced: {len(manifest['files'])}")
        print(f"  Failures: {len(failures)}")
        print(f"  Duration: {manifest['duration_minutes']:.1f} minutes")
        print(f"  Manifest: {MANIFEST_PATH}")
        if failures:
            print(f"\n  FAILED RUNS:")
            for f in failures:
                print(f"    Run {f['run']}: {f['batch']} rep {f['rep']}")
    else:
        print(f"\n{'=' * 70}")
        print(f"DRY RUN COMPLETE — {TOTAL_RUNS} runs would have been executed")
        print(f"{'=' * 70}")


if __name__ == "__main__":
    main()
