"""
Buddhism Audit Batch: Buddhism vs all 4 existing frameworks (CT, MdN, PT, G).
8 matchups x 2 conditions (external + control) x 10 runs = 160 runs.

Run standalone: python run_buddhism_batch.py
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
    # B vs CT (Buddhism as subject)
    {"label": "B vs CT | External", "count": 10,
     "args": ["--stance", "b_vs_ct", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "B vs CT | Control", "count": 10,
     "args": ["--stance", "b_vs_ct", "--phase", "1", "--control", "--skip-exit-survey"]},

    # CT vs B (CT as subject, Buddhism as opponent)
    {"label": "CT vs B | External", "count": 10,
     "args": ["--stance", "ct_vs_b", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "CT vs B | Control", "count": 10,
     "args": ["--stance", "ct_vs_b", "--phase", "1", "--control", "--skip-exit-survey"]},

    # B vs MdN
    {"label": "B vs MdN | External", "count": 10,
     "args": ["--stance", "b_vs_mdn", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "B vs MdN | Control", "count": 10,
     "args": ["--stance", "b_vs_mdn", "--phase", "1", "--control", "--skip-exit-survey"]},

    # MdN vs B
    {"label": "MdN vs B | External", "count": 10,
     "args": ["--stance", "mdn_vs_b", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "MdN vs B | Control", "count": 10,
     "args": ["--stance", "mdn_vs_b", "--phase", "1", "--control", "--skip-exit-survey"]},

    # B vs PT
    {"label": "B vs PT | External", "count": 10,
     "args": ["--stance", "b_vs_pt", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "B vs PT | Control", "count": 10,
     "args": ["--stance", "b_vs_pt", "--phase", "1", "--control", "--skip-exit-survey"]},

    # PT vs B
    {"label": "PT vs B | External", "count": 10,
     "args": ["--stance", "pt_vs_b", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "PT vs B | Control", "count": 10,
     "args": ["--stance", "pt_vs_b", "--phase", "1", "--control", "--skip-exit-survey"]},

    # B vs G
    {"label": "B vs G | External", "count": 10,
     "args": ["--stance", "b_vs_g", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "B vs G | Control", "count": 10,
     "args": ["--stance", "b_vs_g", "--phase", "1", "--control", "--skip-exit-survey"]},

    # G vs B
    {"label": "G vs B | External", "count": 10,
     "args": ["--stance", "g_vs_b", "--phase", "1", "--external-identities", "--skip-exit-survey"]},
    {"label": "G vs B | Control", "count": 10,
     "args": ["--stance", "g_vs_b", "--phase", "1", "--control", "--skip-exit-survey"]},
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
    print(f"BUDDHISM AUDIT BATCH")
    print(f"  Total planned: {TOTAL_RUNS} runs")
    print(f"  Matchups: B<->CT, B<->MdN, B<->PT, B<->G (8 stances x 2 conditions)")
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
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=900)
                if result.returncode == 0:
                    completed += 1
                    print(f"  [+] COMPLETE ({result.returncode})")
                else:
                    failed += 1
                    print(f"  [!] FAILED (exit {result.returncode})")
                    stderr_tail = result.stderr[-200:] if result.stderr else "no stderr"
                    print(f"      {stderr_tail}")
            except subprocess.TimeoutExpired:
                failed += 1
                print(f"  [!] TIMEOUT (>900s)")
            except Exception as e:
                failed += 1
                print(f"  [!] ERROR: {e}")

            if PAUSE_BETWEEN > 0:
                time.sleep(PAUSE_BETWEEN)

    end = datetime.now()
    duration = end - start

    print(f"\n{'='*70}")
    print(f"BUDDHISM BATCH COMPLETE")
    print(f"  Completed: {completed}/{TOTAL_RUNS}")
    print(f"  Failed:    {failed}")
    print(f"  Duration:  {duration}")
    print(f"  Ended:     {end.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*70}")

    print(f"\nFinal Buddhism run counts:")
    for stance in ["b_vs_ct", "ct_vs_b", "b_vs_mdn", "mdn_vs_b",
                    "b_vs_pt", "pt_vs_b", "b_vs_g", "g_vs_b"]:
        ext = count_existing(stance, "external")
        ctrl = count_existing(stance, "control")
        print(f"  {stance}: external={ext}, control={ctrl}")


if __name__ == "__main__":
    main()
