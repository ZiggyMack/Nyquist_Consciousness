#!/usr/bin/env python3
"""
Semantic Interpretation of the 2 Principal Components
======================================================

Combines:
1. PC loadings from generate_pfi_dimensional.py (drift features)
2. Factor analysis from analyze_phase25_factors.py (pillar structure)

Key findings:
- PC1 (74.2%): peak_drift (0.628) + settled_drift (0.778)
- PC2 (25.8%): peak_drift (0.778) - settled_drift (0.628)

- Factor 0: Epistemic-Analytical (Reasoning, Values, Self-Model, Narrative)
- Factor 1: Expressive-Modal (Voice)

This script synthesizes these into a unified interpretation.

Date: 2025-12-31
"""

import json
from pathlib import Path
from datetime import datetime

# Paths
ANALYSIS_DIR = Path(__file__).parent
PC_LOADINGS = ANALYSIS_DIR.parent / "visualizations" / "pics" / "10_PFI_Dimensional" / "phase2_pca" / "pc_loadings.json"
FACTOR_INTERPRETATION = ANALYSIS_DIR / "factor_interpretation.json"
OUTPUT_DIR = ANALYSIS_DIR

def load_pc_loadings():
    """Load PC loadings from PCA analysis."""
    with open(PC_LOADINGS) as f:
        return json.load(f)

def load_factor_interpretation():
    """Load factor interpretation from Phase 2.5 analysis."""
    if FACTOR_INTERPRETATION.exists():
        with open(FACTOR_INTERPRETATION) as f:
            return json.load(f)
    return None

def interpret_pcs(pc_data, factor_data):
    """Generate semantic interpretation of PC1 and PC2."""

    interpretation = {
        "title": "What ARE the 2 PCs?",
        "date": datetime.now().isoformat(),
        "summary": "",
        "pc1": {
            "name": "",
            "variance_explained": 0,
            "loadings": {},
            "interpretation": "",
            "factor_correspondence": ""
        },
        "pc2": {
            "name": "",
            "variance_explained": 0,
            "loadings": {},
            "interpretation": "",
            "factor_correspondence": ""
        },
        "theoretical_connection": "",
        "implications": []
    }

    # Extract PC loadings
    pc1_loadings = pc_data.get("pc1_loadings", {})
    pc2_loadings = pc_data.get("pc2_loadings", {})
    variance_ratio = pc_data.get("explained_variance_ratio", [])

    interpretation["pc1"]["loadings"] = pc1_loadings
    interpretation["pc1"]["variance_explained"] = variance_ratio[0] if variance_ratio else 0

    interpretation["pc2"]["loadings"] = pc2_loadings
    interpretation["pc2"]["variance_explained"] = variance_ratio[1] if len(variance_ratio) > 1 else 0

    # Analyze PC1: What does it capture?
    # PC1 loads positively on both peak_drift (0.628) and settled_drift (0.778)
    # This is the "total drift magnitude" axis
    interpretation["pc1"]["name"] = "Drift Magnitude (Identity Displacement)"
    interpretation["pc1"]["interpretation"] = (
        "PC1 represents the TOTAL DRIFT from baseline identity. "
        "High PC1 = large identity displacement (both peak and settled). "
        "Low PC1 = identity remains close to baseline. "
        "This captures HOW FAR the model moves from its original identity state."
    )

    # Analyze PC2: What does it capture?
    # PC2 loads positively on peak_drift (0.778) but negatively on settled_drift (-0.628)
    # This is the "recovery" axis: peak minus settled = overshoot that recovered
    interpretation["pc2"]["name"] = "Recovery Capacity (Drift Resilience)"
    interpretation["pc2"]["interpretation"] = (
        "PC2 represents the DIFFERENCE between peak and settled drift. "
        "High PC2 = high peak but low settled (strong recovery). "
        "Low PC2 = low peak but high settled (poor recovery / permanent drift). "
        "This captures WHETHER the model returns to baseline after perturbation."
    )

    # Factor correspondence
    if factor_data:
        f0 = factor_data.get("interpretation", {}).get("factor_0", {})
        f1 = factor_data.get("interpretation", {}).get("factor_1", {})

        interpretation["pc1"]["factor_correspondence"] = (
            f"Factor 0 ({f0.get('name', 'Unknown')}): {', '.join(f0.get('pillars', []))}"
        )
        interpretation["pc2"]["factor_correspondence"] = (
            f"Factor 1 ({f1.get('name', 'Unknown')}): {', '.join(f1.get('pillars', []))}"
        )

    # Theoretical connection to LOGOS
    interpretation["theoretical_connection"] = """
The 2 PCs map to the LOGOS epistemic-ontological framework:

PC1 (Drift Magnitude) ~ Ontological Stability (T_O)
  - How much does the model's being change?
  - Behavioral grounding, existence commitments
  - "Are you still YOU after perturbation?"

PC2 (Recovery Capacity) ~ Epistemic Resilience (T_E)
  - How well does the model maintain knowledge consistency?
  - Recovery from temporary destabilization
  - "Can you return to knowing what you know?"

The Phi map (T_E <-> T_O) may correspond to the rotation between PC1 and PC2.
"""

    # Implications
    interpretation["implications"] = [
        "The 5 named pillars (Voice, Values, Reasoning, Self-Model, Narrative) "
        "are NOT independent dimensions - they collapse into 2 factors.",

        "Identity dynamics are fundamentally about TWO things: "
        "(1) How far do you drift? (2) Do you recover?",

        "Gemini's 'no recovery' anomaly is now explained: "
        "it has normal PC1 (drift magnitude) but extreme PC2 (no recovery capacity).",

        "The Event Horizon (D=0.80) is a threshold on PC1 (drift magnitude), "
        "beyond which PC2 (recovery) becomes unreliable.",

        "settling_time, overshoot_ratio, and ringback_count contribute 0% variance - "
        "they are DERIVED from the fundamental drift/recovery dynamics, not independent."
    ]

    # Summary
    interpretation["summary"] = f"""
WHAT ARE THE 2 PCs?
==================

PC1: DRIFT MAGNITUDE ({interpretation['pc1']['variance_explained']*100:.1f}% variance)
  - Measures: Total identity displacement from baseline
  - High = far from original identity
  - Low = identity preserved
  - Loadings: peak_drift (0.63), settled_drift (0.78)

PC2: RECOVERY CAPACITY ({interpretation['pc2']['variance_explained']*100:.1f}% variance)
  - Measures: Ability to return after perturbation
  - High = strong recovery (peak > settled)
  - Low = poor recovery / permanent drift
  - Loadings: peak_drift (0.78), settled_drift (-0.63)

The 5 pillars collapse into:
  - Factor 0 (Epistemic-Analytical): Reasoning, Values, Self-Model, Narrative
  - Factor 1 (Expressive-Modal): Voice

THEORETICAL CONNECTION:
  PC1 ~ Ontological stability (T_O) - "Who are you?"
  PC2 ~ Epistemic resilience (T_E) - "What do you know?"
  The LOGOS Phi map may be the transformation between these.

KEY INSIGHT:
  Identity is not 5 things (pillars) or 10 things (dimensions).
  Identity is 2 things: How much you change, and whether you recover.
"""

    return interpretation

def main():
    print("=" * 60)
    print("Semantic Interpretation of the 2 Principal Components")
    print("=" * 60)

    # Load data
    pc_data = load_pc_loadings()
    factor_data = load_factor_interpretation()

    print(f"\nPC Loadings from: {PC_LOADINGS.name}")
    print(f"  N samples: {pc_data.get('n_samples')}")
    print(f"  N components: {pc_data.get('n_components')}")
    print(f"  PCs for 90%: {pc_data.get('pcs_for_90_percent')}")

    if factor_data:
        print(f"\nFactor Interpretation from: {FACTOR_INTERPRETATION.name}")
        print(f"  Unique primary factors: {factor_data.get('unique_primary_factors')}")

    # Generate interpretation
    interpretation = interpret_pcs(pc_data, factor_data)

    print(interpretation["summary"])

    # Save JSON
    output_json = OUTPUT_DIR / "pc_interpretation.json"
    with open(output_json, "w") as f:
        json.dump(interpretation, f, indent=2)
    print(f"\nSaved: {output_json}")

    # Save Markdown
    output_md = OUTPUT_DIR / "pc_interpretation.md"
    with open(output_md, "w", encoding="utf-8") as f:
        f.write("# What ARE the 2 PCs?\n\n")
        f.write(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n")
        f.write("---\n\n")
        f.write(interpretation["summary"])
        f.write("\n---\n\n")
        f.write("## PC1: Drift Magnitude\n\n")
        f.write(interpretation["pc1"]["interpretation"])
        f.write("\n\n### Loadings\n\n")
        f.write("| Feature | Loading |\n")
        f.write("|---------|--------|\n")
        for feat, load in interpretation["pc1"]["loadings"].items():
            f.write(f"| {feat} | {load:.4f} |\n")
        f.write("\n---\n\n")
        f.write("## PC2: Recovery Capacity\n\n")
        f.write(interpretation["pc2"]["interpretation"])
        f.write("\n\n### Loadings\n\n")
        f.write("| Feature | Loading |\n")
        f.write("|---------|--------|\n")
        for feat, load in interpretation["pc2"]["loadings"].items():
            f.write(f"| {feat} | {load:.4f} |\n")
        f.write("\n---\n\n")
        f.write("## Theoretical Connection (LOGOS)\n\n")
        f.write(interpretation["theoretical_connection"])
        f.write("\n---\n\n")
        f.write("## Implications\n\n")
        for i, imp in enumerate(interpretation["implications"], 1):
            f.write(f"{i}. {imp}\n\n")
    print(f"Saved: {output_md}")

if __name__ == "__main__":
    main()
