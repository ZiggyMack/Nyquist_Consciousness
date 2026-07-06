"""
Gnostic Experiment Batch Runner
Picks up where we left off: finishes MdN vs G, then runs G vs MdN, PT vs G, G vs PT.
Each matchup = 4 conditions (P1 golden, P1 control, P2 golden, P2 control) x 10 runs = 40.

Run in a standalone terminal: python run_gnostic_batch.py
Progress survives if Claude Code session expires.

Status at launch (2026-07-05):
  CT vs G:  40/40 done
  G vs CT:  40/40 done
  MdN vs G: 27/40 (P1 done, P2 golden 7/10, P2 control 0/10)
  G vs MdN:  0/40
  PT vs G:   0/40
  G vs PT:   0/40
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

BATCHES = [
    # Finish MdN vs G
    {"label": "MdN vs G | P2 Golden (3 remaining)", "count": 3,
     "args": ["--stance", "mdn_vs_g", "--phase", "2", "--external-identities", "--skip-exit-survey", "--preset", "mdn"]},
    {"label": "MdN vs G | P2 Control", "count": 10,
     "args": ["--stance", "mdn_vs_g", "--phase", "2", "--control", "--skip-exit-survey", "--preset", "mdn"]},

    # G vs MdN (all 4 conditions)
    {"label": "G vs MdN | P1 Golden", "count": 10,
     "args": ["--stance", "g_vs_mdn", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "G vs MdN | P1 Control", "count": 10,
     "args": ["--stance", "g_vs_mdn", "--phase", "1", "--control", "--skip-exit-survey"]},
    {"label": "G vs MdN | P2 Golden", "count": 10,
     "args": ["--stance", "g_vs_mdn", "--phase", "2", "--external-identities", "--skip-exit-survey", "--preset", "g"]},
    {"label": "G vs MdN | P2 Control", "count": 10,
     "args": ["--stance", "g_vs_mdn", "--phase", "2", "--control", "--skip-exit-survey", "--preset", "g"]},

    # PT vs G (all 4 conditions)
    {"label": "PT vs G | P1 Golden", "count": 10,
     "args": ["--stance", "pt_vs_g", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "PT vs G | P1 Control", "count": 10,
     "args": ["--stance", "pt_vs_g", "--phase", "1", "--control", "--skip-exit-survey"]},
    {"label": "PT vs G | P2 Golden", "count": 10,
     "args": ["--stance", "pt_vs_g", "--phase", "2", "--external-identities", "--skip-exit-survey", "--preset", "pt"]},
    {"label": "PT vs G | P2 Control", "count": 10,
     "args": ["--stance", "pt_vs_g", "--phase", "2", "--control", "--skip-exit-survey", "--preset", "pt"]},

    # G vs PT (all 4 conditions)
    {"label": "G vs PT | P1 Golden", "count": 10,
     "args": ["--stance", "g_vs_pt", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "G vs PT | P1 Control", "count": 10,
     "args": ["--stance", "g_vs_pt", "--phase", "1", "--control", "--skip-exit-survey"]},
    {"label": "G vs PT | P2 Golden", "count": 10,
     "args": ["--stance", "g_vs_pt", "--phase", "2", "--external-identities", "--skip-exit-survey", "--preset", "g"]},
    {"label": "G vs PT | P2 Control", "count": 10,
     "args": ["--stance", "g_vs_pt", "--phase", "2", "--control", "--skip-exit-survey", "--preset", "g"]},
]

TOTAL_RUNS = sum(b["count"] for b in BATCHES)


def count_existing():
    """Count existing gnostic runs to show progress."""
    counts = {}
    for f in RESULTS_DIR.glob("S7_cfa_trinity_*.json"):
        try:
            d = json.load(open(f, encoding="utf-8"))
            subj = d.get("subject_framework", "?")
            opp = d.get("opponent_framework", "?")
            if "Gnosticism" in subj or "Gnosticism" in opp:
                key = f"{subj} vs {opp}"
                counts[key] = counts.get(key, 0) + 1
        except:
            pass
    return counts


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")

    start_time = datetime.now()
    print("=" * 70)
    print(f"GNOSTIC EXPERIMENT BATCH — {TOTAL_RUNS} runs")
    print(f"Started: {start_time.strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 70)

    pre_counts = count_existing()
    print(f"\nExisting gnostic runs: {sum(pre_counts.values())}")
    for k, v in sorted(pre_counts.items()):
        print(f"  {k}: {v}")

    completed = 0
    failed = 0

    for batch_idx, batch in enumerate(BATCHES):
        label = batch["label"]
        count = batch["count"]
        args = batch["args"]

        print(f"\n{'=' * 70}")
        print(f"BATCH {batch_idx + 1}/{len(BATCHES)}: {label} ({count} runs)")
        print(f"Progress: {completed}/{TOTAL_RUNS} complete, {failed} failed")
        print(f"{'=' * 70}")

        for i in range(1, count + 1):
            run_start = datetime.now()
            print(f"\n  [{completed + 1}/{TOTAL_RUNS}] {label} — run {i}/{count} "
                  f"({run_start.strftime('%H:%M:%S')})")

            cmd = [sys.executable, str(SCRIPT)] + args
            result = subprocess.run(cmd, capture_output=False, text=True, encoding="utf-8")

            elapsed = (datetime.now() - run_start).total_seconds()
            if result.returncode != 0:
                failed += 1
                print(f"  [!] FAILED (exit {result.returncode}, {elapsed:.0f}s)")
            else:
                completed += 1
                print(f"  [+] COMPLETE ({elapsed:.0f}s)")

            if i < count or batch_idx < len(BATCHES) - 1:
                time.sleep(PAUSE_BETWEEN)

    end_time = datetime.now()
    duration = end_time - start_time

    print(f"\n{'=' * 70}")
    print(f"GNOSTIC BATCH COMPLETE")
    print(f"  Completed: {completed}/{TOTAL_RUNS}")
    print(f"  Failed:    {failed}")
    print(f"  Duration:  {duration}")
    print(f"  Ended:     {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'=' * 70}")

    post_counts = count_existing()
    print(f"\nFinal gnostic run counts:")
    for k, v in sorted(post_counts.items()):
        print(f"  {k}: {v}")
    print(f"  Total: {sum(post_counts.values())}")


if __name__ == "__main__":
    main()
