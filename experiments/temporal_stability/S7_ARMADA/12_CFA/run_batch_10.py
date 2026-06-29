"""Batch runner: 10 sequential Component 1 runs with external identities."""
import subprocess
import sys
import time
from pathlib import Path

SCRIPT = Path(__file__).parent / "run_cfa_trinity_v2.py"
TOTAL_RUNS = 10
PAUSE_BETWEEN = 5

def main():
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")

    print("=" * 70)
    print(f"BATCH RUN: {TOTAL_RUNS} x Component 1 (EXTERNAL IDENTITIES)")
    print("=" * 70)

    for i in range(1, TOTAL_RUNS + 1):
        print(f"\n{'=' * 70}")
        print(f"  RUN {i}/{TOTAL_RUNS}")
        print(f"{'=' * 70}")

        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--component", "1", "--external-identities"],
            capture_output=False,
            text=True,
            encoding="utf-8",
        )

        if result.returncode != 0:
            print(f"  [!] Run {i} FAILED (exit code {result.returncode})")
        else:
            print(f"  [+] Run {i} COMPLETE")

        if i < TOTAL_RUNS:
            print(f"  Pausing {PAUSE_BETWEEN}s for rate limits...")
            time.sleep(PAUSE_BETWEEN)

    print(f"\n{'=' * 70}")
    print(f"BATCH COMPLETE: {TOTAL_RUNS} runs finished")
    print("=" * 70)

if __name__ == "__main__":
    main()
