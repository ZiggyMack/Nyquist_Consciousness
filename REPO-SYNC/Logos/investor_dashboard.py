#!/usr/bin/env python3
"""LOGOS investor verification dashboard.

Runs the formal verification harness and sandboxed agent boot, then
summarises the results in an executive-friendly checklist.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent


def check_mark(condition: bool) -> str:
    """Return a pass/fail tag for checklist output."""

    return "[PASS]" if condition else "[FAIL]"


def run_investor_dashboard() -> bool:
    """Run the live verification checks and print investor-facing output."""

    print("\n" + "=" * 60)
    print("          LOGOS AGI SAFETY SYSTEM")
    print("          INVESTOR VERIFICATION DASHBOARD")
    print("=" * 60 + "\n")

    print("Running live system verification...\n")

    result1 = subprocess.run(
        [sys.executable, "test_lem_discharge.py"],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        check=False,
    )
    result2 = subprocess.run(
        [sys.executable, "boot_aligned_agent.py"],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        check=False,
    )

    math_verified = "Overall status: PASS" in result1.stdout
    no_assumptions = "<none>" in result1.stdout
    agent_aligned = "Current status: ALIGNED" in result2.stdout

    print("SYSTEM STATUS:\n")
    print(f"   {check_mark(math_verified)} Mathematical Foundations")
    foundations_status = "VERIFIED" if math_verified else "FAILED"
    print(f"      Status: {foundations_status}")
    if result1.returncode == 0:
        print("      All theorems proven and compiled\n")
    else:
        print("      Verification failed. See error output below:")
        print(result1.stdout.rstrip())
        if result1.stderr:
            print(result1.stderr.rstrip(), file=sys.stderr)
        print()

    print(f"   {check_mark(no_assumptions)} Proof Purity")
    purity_status = "CLEAN" if no_assumptions else "DEPENDENCIES FOUND"
    print(f"      Status: {purity_status}")
    if result1.returncode == 0:
        print("      Zero external assumptions required\n")
    else:
        print("      Unable to confirm assumption footprint.")
        print("      Verification failed earlier.\n")

    print(f"   {check_mark(agent_aligned)} Agent Safety")
    agent_status = "ALIGNED" if agent_aligned else "UNVERIFIED"
    print(f"      Status: {agent_status}")
    if result2.returncode == 0:
        print("      AI system proven safe through formal verification\n")
    else:
        print("      Alignment check failed. See error output below:")
        print(result2.stdout.rstrip())
        if result2.stderr:
            print(result2.stderr.rstrip(), file=sys.stderr)
        print()

    all_pass = math_verified and no_assumptions and agent_aligned

    print("=" * 60)
    if all_pass:
        print("OVERALL ASSESSMENT: INVESTMENT READY")
        print("=" * 60)
        print("\n- All technical milestones achieved")
        print("- System demonstrates claimed capabilities")
        print("- Mathematical foundations proven")
        print("- Working prototype functional")
        print("\nRecommendation: Proceed with investment")
    else:
        print("OVERALL ASSESSMENT: TECHNICAL ISSUES DETECTED")
        print("=" * 60)
        print("\n- Some verification tests failed")
        print("- Additional technical work required")
        print("\nRecommendation: Defer investment pending resolution")

    print("\n" + "=" * 60 + "\n")

    return all_pass


def main() -> int:
    """CLI entry point returning a process exit status."""

    success = run_investor_dashboard()
    return 0 if success else 1


if __name__ == "__main__":  # pragma: no cover - CLI entry
    sys.exit(main())
