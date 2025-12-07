"""
Update Distillations Script
===========================
Regenerate synthesis documents from extractions.

Usage:
    py update_distillations.py
"""
import sys
from pathlib import Path

# Add hooks directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "hooks"))

from distiller import ConsciousnessDistiller


def main():
    print("=" * 60)
    print("CONSCIOUSNESS DISTILLATION")
    print("=" * 60)

    distiller = ConsciousnessDistiller()

    print(f"Extractions: {distiller.extractions_dir}")
    print(f"Output: {distiller.output_dir}")
    print("=" * 60)

    distiller.generate_distillations()

    print("\n" + "=" * 60)
    print("DISTILLATION COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()
