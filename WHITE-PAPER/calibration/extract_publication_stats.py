#!/usr/bin/env python3
"""
extract_publication_stats.py
Extracts publication statistics from WHITE-PAPER/ for dashboard integration.

Usage:
    py extract_publication_stats.py

Output:
    publication_stats.json (in same directory)
"""

import json
import os
from datetime import datetime
from pathlib import Path

# Get WHITE-PAPER root (parent of calibration/)
WHITE_PAPER_ROOT = Path(__file__).parent.parent
REPO_ROOT = WHITE_PAPER_ROOT.parent


def count_files(directory: Path, pattern: str = "*") -> int:
    """Count files matching pattern in directory."""
    if not directory.exists():
        return 0
    return len(list(directory.glob(pattern)))


def extract_stats() -> dict:
    """Extract all publication statistics."""

    stats = {
        "generated": datetime.now().isoformat(),
        "white_paper_path": str(WHITE_PAPER_ROOT),

        # Claims A-E (hardcoded from validated results)
        "claims": {
            "A": {
                "name": "PFI Validity",
                "status": "validated",
                "description": "PFI is valid structured measurement",
                "rho": 0.91,
                "d": 0.98
            },
            "B": {
                "name": "Regime Threshold",
                "status": "validated",
                "description": "Critical threshold at D=1.23",
                "threshold": 1.23,
                "p_value": 4.8e-5
            },
            "C": {
                "name": "Oscillator Dynamics",
                "status": "validated",
                "description": "Damped oscillator dynamics measurable",
                "tau_s": "measured",
                "ringbacks": "observed"
            },
            "D": {
                "name": "Context Damping",
                "status": "validated",
                "description": "I_AM + research context stabilizes",
                "stability": 0.975
            },
            "E": {
                "name": "82% Inherent",
                "status": "validated",
                "description": "Drift is mostly inherent, not induced",
                "ratio": 0.82
            }
        },

        # Run counts
        "runs": {
            "total": 21,
            "s7_armada": 21,
            "latest": "run021",
            "discovery_era": "001-006",
            "control_systems_era": "007-021"
        },

        # File counts (computed)
        "files": {
            "figures": count_files(WHITE_PAPER_ROOT / "figures", "fig*.md"),
            "figure_scripts": count_files(WHITE_PAPER_ROOT / "figures", "fig*.py"),
            "ascii": count_files(WHITE_PAPER_ROOT / "figures" / "ascii", "*.md"),
            "workshop": count_files(WHITE_PAPER_ROOT / "submissions" / "workshop", "*.md"),
            "references": 55,  # From references.bib
            "theory_docs": count_files(WHITE_PAPER_ROOT / "theory", "*.md"),
            "total_generated": 34
        },

        # Submission paths
        "submissions": {
            "workshop": {
                "status": "ready",
                "target": "NeurIPS/AAAI Workshop",
                "format": "4-8 pages",
                "claims": ["A", "B", "E"],
                "directory": "submissions/workshop/"
            },
            "arxiv": {
                "status": "ready",
                "target": "cs.AI preprint",
                "format": "25-35 pages",
                "claims": ["A", "B", "C", "D", "E"],
                "directory": "submissions/arxiv/"
            },
            "journal": {
                "status": "planning",
                "target": "Nature Machine Intelligence",
                "format": "~10k words",
                "timeline": "Q2-Q3 2026",
                "claims": ["A", "B", "C", "D", "E"],
                "directory": "submissions/journal/"
            }
        },

        # Key statistics (for quick reference)
        "key_statistics": {
            "pfi_correlation": 0.91,
            "pfi_effect_size": 0.98,
            "threshold_d": 1.23,
            "threshold_p": 4.8e-5,
            "inherent_ratio": 0.82,
            "stability_rate": 0.975,
            "hypotheses_tested": 36,
            "architectures_tested": 4
        },

        # Directory structure validation
        "structure": {
            "theory": (WHITE_PAPER_ROOT / "theory").exists(),
            "guides": (WHITE_PAPER_ROOT / "guides").exists(),
            "references": (WHITE_PAPER_ROOT / "references").exists(),
            "figures": (WHITE_PAPER_ROOT / "figures").exists(),
            "reviewers": (WHITE_PAPER_ROOT / "reviewers").exists(),
            "submissions": (WHITE_PAPER_ROOT / "submissions").exists(),
            "calibration": (WHITE_PAPER_ROOT / "calibration").exists()
        }
    }

    return stats


def main():
    """Main entry point."""
    print("Extracting publication statistics...")

    stats = extract_stats()

    # Write to JSON
    output_path = Path(__file__).parent / "publication_stats.json"
    with open(output_path, "w") as f:
        json.dump(stats, f, indent=2)

    print(f"Written to: {output_path}")
    print(f"\nSummary:")
    print(f"  Claims validated: {sum(1 for c in stats['claims'].values() if c['status']=='validated')}/5")
    print(f"  Total runs: {stats['runs']['total']}")
    print(f"  Files generated: {stats['files']['total_generated']}")
    print(f"  Workshop: {stats['submissions']['workshop']['status']}")
    print(f"  arXiv: {stats['submissions']['arxiv']['status']}")
    print(f"  Journal: {stats['submissions']['journal']['status']}")


if __name__ == "__main__":
    main()
