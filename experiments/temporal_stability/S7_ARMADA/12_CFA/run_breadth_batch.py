"""
Breadth Audit Batch: 8 unrun worldviews vs Classical Theism, n=1 each.
Phase 1, external (identity-loaded) condition, exit survey skipped for speed.

Breadth-first: score every identified profile at n=1 now; double back later for
n=10 + the control condition. Repo Opus orchestrates this fast API version;
CFA Claude runs manual mode as a cross-check. Component 2 (Axioms Review) runs
inline per audit = the Grok+Nova sign-off gate.

Idempotent: skips any stance already present, so it can be re-run to resume.
Run standalone: python run_breadth_batch.py
"""
import subprocess
import sys
import time
import json
from pathlib import Path
from datetime import datetime

SCRIPT = Path(__file__).parent / "run_cfa_trinity_v3.py"
RESULTS_DIR = Path(__file__).parent.parent / "0_results" / "runs"
PAUSE_BETWEEN = 5

# 8 breadth stances (subject vs common opponent), n=1 each, external condition.
# Opponent set by argv[1]: "ct" (default) or "mdn". Same 8 worldviews either way.
OPP = (sys.argv[1] if len(sys.argv) > 1 else "ct").lower()
OPP_LABEL = {"ct": "CT", "mdn": "MdN"}.get(OPP, OPP.upper())
# Condition set by argv[2]: "external" (default, identity-loaded) or "control" (base-model priors).
COND = (sys.argv[2] if len(sys.argv) > 2 else "external").lower()
COND_FLAG = "--control" if COND == "control" else "--external-identities"
WORLDVIEWS = [
    ("judaism", "Orthodox Judaism"),
    ("mormonism", "Mormonism"),
    ("islam", "Islam"),
    ("hinduism", "Hinduism"),
    ("existentialism", "Existentialism"),
    ("error_theory", "Error Theory"),
    ("null_hypothesis", "Null Hypothesis (control anchor)"),
    ("desiderata", "Desiderata Believers"),
]
STANCE_KEYS = [(f"{k}_vs_{OPP}", f"{name} vs {OPP_LABEL}") for k, name in WORLDVIEWS]
BATCHES = [
    {"label": label, "count": 1,
     "args": ["--stance", key, "--phase", "1", COND_FLAG, "--skip-exit-survey"]}
    for key, label in STANCE_KEYS
]
TOTAL_RUNS = sum(b["count"] for b in BATCHES)


def count_existing(stance: str, condition: str) -> int:
    count = 0
    for f in RESULTS_DIR.glob("S7_cfa_trinity_*.json"):
        try:
            data = json.loads(f.read_text(encoding="utf-8"))
            if data.get("stance") == stance and data.get("condition") == condition:
                count += 1
        except (json.JSONDecodeError, KeyError, UnicodeDecodeError):
            continue
    return count


def main():
    start = datetime.now()
    completed = 0
    failed = 0
    run_number = 0

    print(f"\n{'='*70}")
    print(f"BREADTH AUDIT BATCH — 8 worldviews vs {OPP_LABEL} [{COND}] (n=1)")
    print(f"  Total planned: {TOTAL_RUNS} runs (Phase 1, external, skip-exit-survey)")
    print(f"  Started: {start.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*70}\n")

    for batch in BATCHES:
        label = batch["label"]
        count = batch["count"]
        args = batch["args"]

        stance_idx = args.index("--stance") + 1
        stance = args[stance_idx]
        condition = "control" if "--control" in args else "external"
        existing = count_existing(stance, condition)

        if existing >= count:
            print(f"\n[SKIP] {label} - already have {existing}/{count}")
            completed += count
            continue

        remaining = count - existing
        print(f"\n[BATCH] {label} - need {remaining} more (have {existing}/{count})")

        for i in range(remaining):
            run_number += 1
            elapsed = datetime.now() - start
            print(f"\n  [{run_number}/{TOTAL_RUNS}] {label} - run {existing + i + 1}/{count} ({elapsed})")

            cmd = [sys.executable, str(SCRIPT)] + args
            try:
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
                if result.returncode == 0:
                    completed += 1
                    print(f"  [+] COMPLETE ({result.returncode})")
                else:
                    failed += 1
                    print(f"  [!] FAILED (exit {result.returncode})")
                    stderr_tail = result.stderr[-300:] if result.stderr else "no stderr"
                    print(f"      {stderr_tail}")
            except subprocess.TimeoutExpired:
                failed += 1
                print(f"  [!] TIMEOUT (>1800s)")
            except Exception as e:
                failed += 1
                print(f"  [!] ERROR: {e}")

            if PAUSE_BETWEEN > 0:
                time.sleep(PAUSE_BETWEEN)

    end = datetime.now()
    duration = end - start

    print(f"\n{'='*70}")
    print(f"BREADTH BATCH COMPLETE")
    print(f"  Completed: {completed}/{TOTAL_RUNS}")
    print(f"  Failed:    {failed}")
    print(f"  Duration:  {duration}")
    print(f"  Ended:     {end.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*70}")

    print(f"\nFinal breadth run counts (external):")
    for key, label in STANCE_KEYS:
        ext = count_existing(key, "external")
        print(f"  {key}: external={ext}")


if __name__ == "__main__":
    main()
