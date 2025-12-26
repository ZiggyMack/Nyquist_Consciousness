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

        # Claims A-E (IRON CLAD validated - Cosine methodology)
        "claims": {
            "A": {
                "name": "PFI Validity",
                "status": "validated",
                "description": "PFI is valid structured measurement",
                "rho": 0.91,
                "d": 0.698,  # Model-level aggregate from Run 023d Phase 3B
                "pcs_90_variance": 2  # Key finding: only 2 PCs needed
            },
            "B": {
                "name": "Regime Threshold",
                "status": "validated",
                "description": "Critical threshold at D=0.80 (cosine)",
                "threshold": 0.80,  # Updated from 1.23 (Euclidean)
                "p_value": 2.40e-23  # Updated from 4.8e-5
            },
            "C": {
                "name": "Oscillator Dynamics",
                "status": "validated",
                "description": "Damped oscillator dynamics measurable",
                "tau_s": "9.9-10.2",  # Updated from 5.2-6.1
                "ringbacks": "observed"
            },
            "D": {
                "name": "Context Damping",
                "status": "validated",
                "description": "I_AM + research context stabilizes",
                "stability": 0.975
            },
            "E": {
                "name": "92% Inherent",  # Updated from 82%
                "status": "validated",
                "description": "Drift is mostly inherent, not induced",
                "ratio": 0.92  # Updated from 0.82
            }
        },

        # Run counts (IRON CLAD era)
        "runs": {
            "total_experiments": 750,  # Updated from 21 runs
            "s7_armada": "run023",  # Current IRON CLAD run
            "latest": "run023",
            "providers": 5,  # Updated from 4
            "models": 25,
            "methodology": "cosine"
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

        # Key statistics (IRON CLAD - Cosine methodology)
        "key_statistics": {
            "pfi_correlation": 0.91,
            "pfi_effect_size": 0.698,  # Model-level aggregate from Run 023d Phase 3B
            "threshold_d": 0.80,  # Updated from 1.23 (cosine, not Euclidean)
            "threshold_p": 2.40e-23,  # Updated from 4.8e-5
            "inherent_ratio": 0.92,  # Updated from 0.82
            "stability_rate": 0.975,
            "pcs_for_90_variance": 2,  # Key finding
            "experiments": 750,
            "providers_tested": 5,  # Updated from 4
            "models_tested": 25
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
    print(f"\nSummary (IRON CLAD - Cosine methodology):")
    print(f"  Claims validated: {sum(1 for c in stats['claims'].values() if c['status']=='validated')}/5")
    print(f"  Experiments: {stats['runs']['total_experiments']}")
    print(f"  Providers: {stats['runs']['providers']} | Models: {stats['runs']['models']}")
    print(f"  Event Horizon: D = {stats['key_statistics']['threshold_d']} (cosine)")
    print(f"  PCs for 90% variance: {stats['key_statistics']['pcs_for_90_variance']}")
    print(f"  Inherent drift: {stats['key_statistics']['inherent_ratio']*100:.0f}%")
    print(f"  Workshop: {stats['submissions']['workshop']['status']}")
    print(f"  arXiv: {stats['submissions']['arxiv']['status']}")
    print(f"  Journal: {stats['submissions']['journal']['status']}")


if __name__ == "__main__":
    main()
