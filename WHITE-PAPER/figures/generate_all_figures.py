"""
Generate All Publication Figures
Nyquist Consciousness Publication

Batch runner that generates all 9 publication figures and saves them
to organized directories (generated/png/ and generated/pdf/).
"""

import os
import sys
import subprocess
from pathlib import Path

# Ensure we're in the figures directory
FIGURES_DIR = Path(__file__).parent
os.chdir(FIGURES_DIR)

# Create output directories
(FIGURES_DIR / "generated" / "png").mkdir(parents=True, exist_ok=True)
(FIGURES_DIR / "generated" / "pdf").mkdir(parents=True, exist_ok=True)

# List of figure scripts to run
FIGURE_SCRIPTS = [
    "fig1_identity_manifold.py",
    "fig2_drift_field.py",
    "fig3_pipeline.py",
    "fig4_five_pillars.py",
    "fig5_omega_convergence.py",
    "fig6_82_percent.py",
    "fig7_context_damping.py",
    "fig8_oobleck.py",
    "fig_workshop_combined.py",
]

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
    print(f"Output directories:")
    print(f"  PNG: {FIGURES_DIR / 'generated' / 'png'}")
    print(f"  PDF: {FIGURES_DIR / 'generated' / 'pdf'}")

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
    print("\nGenerated files:")
    for folder in ['png', 'pdf']:
        folder_path = FIGURES_DIR / 'generated' / folder
        if folder_path.exists():
            files = list(folder_path.glob(f'*.{folder}'))
            print(f"\n  {folder.upper()} ({len(files)} files):")
            for f in sorted(files):
                print(f"    {f.name}")

if __name__ == '__main__':
    main()
