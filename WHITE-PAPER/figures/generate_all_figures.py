"""
Generate All Publication Figures
Nyquist Consciousness Publication

Batch runner that generates CONCEPTUAL figures only.
Data-driven figures should come from S7_ARMADA/visualizations/pics/
and are stored in figures/run023/.

DEPRECATED figures (containing hardcoded fake data) are in figures/deprecated/
and should NOT be regenerated.

OUTPUT: PNG only to conceptual/pics/ (PDFs generated on-demand for papers)
"""

import os
import sys
import subprocess
from pathlib import Path

# Ensure we're in the figures directory
FIGURES_DIR = Path(__file__).parent
os.chdir(FIGURES_DIR)

# Output directory for conceptual figures
PICS_DIR = FIGURES_DIR / "conceptual" / "pics"
PICS_DIR.mkdir(parents=True, exist_ok=True)

# List of CONCEPTUAL figure scripts to run (NO hardcoded experimental data)
# These are theoretical/illustrative diagrams only
FIGURE_SCRIPTS = [
    "conceptual/fig1_identity_manifold.py",  # Identity manifold concept diagram
    "conceptual/fig2_drift_field.py",         # Drift field geometry concept
    "conceptual/fig3_pipeline.py",            # Experimental pipeline flowchart
    "conceptual/fig4_five_pillars.py",        # Architecture diagram
]

# DEPRECATED - DO NOT USE (contain hardcoded fake data)
# These have been moved to deprecated/ with _DEPRECATED_ prefix:
# - _DEPRECATED_fig2_drift_field.py      (D=1.23 wrong, hardcoded drifts)
# - _DEPRECATED_fig5_omega_convergence.py (hardcoded drifts)
# - _DEPRECATED_fig6_82_percent.py       (hardcoded experimental data)
# - _DEPRECATED_fig7_context_damping.py  (wrong settling time)
# - _DEPRECATED_fig8_oobleck.py          (hardcoded intensity/drift)
# - _DEPRECATED_fig_workshop_combined.py (all panels hardcoded)
#
# Use figures from run023/ instead - these are VERIFIED from S7_ARMADA experiments

def run_figure_script(script_name: str) -> bool:
    """Run a single figure script and return success status."""
    print(f"\n{'='*60}")
    print(f"Generating: {script_name}")
    print('='*60)

    script_path = FIGURES_DIR / script_name
    if not script_path.exists():
        print(f"  ERROR: Script not found: {script_path}")
        return False

    try:
        # Run with matplotlib backend that doesn't require display
        env = os.environ.copy()
        env['MPLBACKEND'] = 'Agg'  # Non-interactive backend

        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=str(FIGURES_DIR),
            capture_output=True,
            text=True,
            env=env,
            timeout=120
        )

        if result.returncode == 0:
            print(f"  SUCCESS: {script_name}")
            if result.stdout:
                print(f"  Output: {result.stdout.strip()}")
            return True
        else:
            print(f"  FAILED: {script_name}")
            if result.stderr:
                print(f"  Error: {result.stderr[:500]}")
            return False

    except subprocess.TimeoutExpired:
        print(f"  TIMEOUT: {script_name} took too long")
        return False
    except Exception as e:
        print(f"  EXCEPTION: {e}")
        return False

def main():
    """Generate all figures."""
    print("="*60)
    print("GENERATING ALL PUBLICATION FIGURES")
    print("="*60)
    print(f"Working directory: {FIGURES_DIR}")
    print(f"Output: {PICS_DIR} (PNG only)")

    results = []
    for script in FIGURE_SCRIPTS:
        success = run_figure_script(script)
        results.append((script, success))

    # Summary
    print("\n" + "="*60)
    print("GENERATION SUMMARY")
    print("="*60)

    success_count = sum(1 for _, success in results if success)
    fail_count = len(results) - success_count

    print(f"\nTotal: {len(results)} scripts")
    print(f"Success: {success_count}")
    print(f"Failed: {fail_count}")

    if fail_count > 0:
        print("\nFailed scripts:")
        for script, success in results:
            if not success:
                print(f"  - {script}")

    # List generated files
    print("\nGenerated files in conceptual/pics/:")
    if PICS_DIR.exists():
        files = list(PICS_DIR.glob('*.png'))
        print(f"\n  PNG ({len(files)} files):")
        for f in sorted(files):
            print(f"    {f.name}")

if __name__ == '__main__':
    main()
