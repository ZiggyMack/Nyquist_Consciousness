"""
Breadth Phase 2 (Trinity²) batch: YPA lever calibration for the 8 breadth worldviews.

Phase 1 gave audited philosophical-quality scores (7 metrics). This runs Phase 2 =
YPA lever calibration (6 levers: CCI/EDB/PF_I/PF_E/AR/MG), contesting the preliminary
YAML priors in PRIOR_PRESETS. External condition, n=1. Each run is fed its own Phase-1
result as context (--phase1-results), so the levers can cite Phase-1 metrics.

--component 1 only: Component 2 (Axioms Review) reviews the same static auditor doc every
run (worldview-independent, per CFA), so it adds nothing to the breadth mission here.

Idempotent: skips any (stance, external, phase==2) already present. Auto-discovers each
worldview's Phase-1 JSON in cfa_trinity/<CODE>/.
Run standalone: python run_breadth_phase2_batch.py
"""
import subprocess
import sys
import time
import json
from pathlib import Path
from datetime import datetime

SCRIPT = Path(__file__).parent / "run_cfa_trinity_v3.py"
RESULTS_DIR = Path(__file__).parent.parent / "0_results" / "runs"
CFA_TRINITY = RESULTS_DIR / "cfa_trinity"
PAUSE_BETWEEN = 5
RUN_TIMEOUT = 1800  # 30 min (Phase 1 taught us evening latency pushes runs ~20 min)

# profile_key -> (short_code folder, display label)
PROFILES = [
    ("judaism", "OJ", "Orthodox Judaism"),
    ("mormonism", "LDS", "Mormonism"),
    ("islam", "ISL", "Islam"),
    ("hinduism", "HIN", "Hinduism"),
    ("existentialism", "EXST", "Existentialism"),
    ("error_theory", "ERR", "Error Theory"),
    ("null_hypothesis", "NULL", "Null Hypothesis"),
    ("desiderata", "DES", "Desiderata"),
]

# Opponent set by argv[1]: "ct" (default) or "mdn". PROFILES/short-codes are per-subject.
OPP = (sys.argv[1] if len(sys.argv) > 1 else "ct").lower()
OPP_LABEL = {"ct": "CT", "mdn": "MdN"}.get(OPP, OPP.upper())


def find_phase1_results(stance, code):
    """Locate this stance's Phase-1 external run JSON (flat drop zone OR cfa_trinity/<code>/)."""
    search = list(RESULTS_DIR.glob("S7_cfa_trinity_*.json"))
    folder = CFA_TRINITY / code
    if folder.exists():
        search += list(folder.glob("*.json"))
    for f in search:
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError):
            continue
        if d.get("stance") == stance and d.get("phase") == 1 and d.get("condition") == "external":
            return f
    return None


def count_existing_phase2(stance):
    """Count existing Phase-2 external runs for this stance (flat drop zone)."""
    count = 0
    for f in RESULTS_DIR.glob("S7_cfa_trinity_*.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError):
            continue
        if d.get("stance") == stance and d.get("condition") == "external" and d.get("phase") == 2:
            count += 1
    return count


def main():
    start = datetime.now()
    completed = 0
    failed = 0

    print(f"\n{'='*70}")
    print(f"BREADTH PHASE 2 (Trinity²) BATCH — YPA levers vs {OPP_LABEL}, 8 worldviews (n=1)")
    print(f"  Metrics: CCI, EDB, PF_I, PF_E, AR, MG  |  external  |  --component 1")
    print(f"  Started: {start.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*70}\n")

    for key, code, label in PROFILES:
        stance = f"{key}_vs_{OPP}"
        if count_existing_phase2(stance) >= 1:
            print(f"\n[SKIP] {label} Phase 2 - already have 1")
            completed += 1
            continue

        p1 = find_phase1_results(stance, code)
        args = ["--stance", stance, "--phase", "2", "--preset", key,
                "--component", "1", "--external-identities", "--skip-exit-survey"]
        if p1:
            args += ["--phase1-results", str(p1)]
            ctx = f"(Phase-1 ctx: {p1.name})"
        else:
            ctx = "(no Phase-1 context found — running without)"

        elapsed = datetime.now() - start
        print(f"\n[BATCH] {label} Phase 2 {ctx} ({elapsed})")
        cmd = [sys.executable, str(SCRIPT)] + args
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=RUN_TIMEOUT)
            if result.returncode == 0:
                completed += 1
                print(f"  [+] COMPLETE ({result.returncode})")
            else:
                failed += 1
                print(f"  [!] FAILED (exit {result.returncode})")
                print(f"      {result.stderr[-300:] if result.stderr else 'no stderr'}")
        except subprocess.TimeoutExpired:
            failed += 1
            print(f"  [!] TIMEOUT (>{RUN_TIMEOUT}s)")
        except Exception as e:
            failed += 1
            print(f"  [!] ERROR: {e}")

        if PAUSE_BETWEEN > 0:
            time.sleep(PAUSE_BETWEEN)

    end = datetime.now()
    print(f"\n{'='*70}")
    print(f"BREADTH PHASE 2 BATCH COMPLETE")
    print(f"  Completed: {completed}/8   Failed: {failed}")
    print(f"  Duration:  {end - start}")
    print(f"{'='*70}")
    print(f"\nFinal Phase-2 external counts:")
    for key, code, label in PROFILES:
        print(f"  {key}_vs_ct: phase2 external={count_existing_phase2(f'{key}_vs_ct')}")


if __name__ == "__main__":
    main()
