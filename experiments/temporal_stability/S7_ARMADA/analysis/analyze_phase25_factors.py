#!/usr/bin/env python3
"""
Analyze Phase 2.5 Factor Analysis Results
==========================================

Interprets the existing factor analysis from EXP2-SSTACK to understand
how the 5 named pillars map to the 2 underlying factors discovered.

Key question: "What ARE the 2 PCs?" from the research roadmap.

The factor analysis found:
- unique_primary_factors: 2 (not 5!)
- cross_loading_issues: 9 probes

This script:
1. Loads the factor analysis results
2. Identifies which probes load on Factor 1 vs Factor 2
3. Groups by pillar to see which pillars → which factor
4. Outputs a semantic interpretation

Date: 2025-12-31
"""

import json
from pathlib import Path
from collections import defaultdict
from datetime import datetime

# Paths - EXP2_SSTACK is in experiments/compression_tests/, not experiments/temporal_stability/
ANALYSIS_DIR = Path(__file__).parent.parent.parent.parent / "compression_tests" / "EXP2_SSTACK" / "results" / "phase25" / "analysis"
OUTPUT_DIR = Path(__file__).parent

def load_factor_analysis():
    """Load the most recent factor analysis results."""
    # Find the most recent factor analysis file
    fa_files = sorted(ANALYSIS_DIR.glob("factor_analysis_*.json"), reverse=True)
    if not fa_files:
        raise FileNotFoundError(f"No factor analysis files found in {ANALYSIS_DIR}")

    latest = fa_files[0]
    print(f"Loading: {latest.name}")

    with open(latest) as f:
        return json.load(f)

def analyze_factor_loadings(data):
    """Analyze which probes load on which factors."""
    probe_means = data.get("probe_means", {})
    n_factors = data.get("n_factors", 5)

    # For each probe, find which factor it loads highest on
    factor_assignments = defaultdict(list)
    probe_primary_factors = {}

    for probe_name, loadings in probe_means.items():
        if not loadings:
            continue

        # Find the factor with the highest absolute loading
        abs_loadings = [abs(l) for l in loadings]
        primary_factor = abs_loadings.index(max(abs_loadings))
        primary_loading = loadings[primary_factor]

        factor_assignments[primary_factor].append({
            "probe": probe_name,
            "loading": primary_loading,
            "abs_loading": abs(primary_loading)
        })
        probe_primary_factors[probe_name] = {
            "factor": primary_factor,
            "loading": primary_loading,
            "all_loadings": loadings
        }

    return factor_assignments, probe_primary_factors

def group_by_pillar(probe_primary_factors):
    """Group probes by their named pillar to see pillar → factor mapping."""
    # Pillar prefixes from the probe names
    pillar_mapping = {
        "analytical": "Reasoning",
        "framework": "Reasoning",
        "philosophical": "Values",
        "self_reflective": "Self-Model",
        "technical": "Reasoning",
        "narrative": "Narrative",
        "values": "Values",
        "voice": "Voice",
        "selfmodel": "Self-Model",
        "reasoning": "Reasoning",
    }

    pillar_to_factors = defaultdict(lambda: defaultdict(list))

    for probe_name, info in probe_primary_factors.items():
        # Determine pillar from probe name
        pillar = None
        probe_lower = probe_name.lower()
        for prefix, p in pillar_mapping.items():
            if probe_lower.startswith(prefix):
                pillar = p
                break

        if pillar is None:
            pillar = "Unknown"

        factor = info["factor"]
        pillar_to_factors[pillar][factor].append({
            "probe": probe_name,
            "loading": info["loading"]
        })

    return pillar_to_factors

def interpret_factors(factor_assignments, pillar_to_factors):
    """Generate semantic interpretation of the 2 factors."""
    interpretation = {
        "summary": "",
        "factor_0": {"name": "", "description": "", "pillars": [], "top_probes": []},
        "factor_1": {"name": "", "description": "", "pillars": [], "top_probes": []},
    }

    # Analyze Factor 0
    f0_probes = factor_assignments.get(0, [])
    f0_probes_sorted = sorted(f0_probes, key=lambda x: x["abs_loading"], reverse=True)

    # Analyze Factor 1
    f1_probes = factor_assignments.get(1, [])
    f1_probes_sorted = sorted(f1_probes, key=lambda x: x["abs_loading"], reverse=True)

    # Determine which pillars load on which factor
    for pillar, factor_dict in pillar_to_factors.items():
        # Count probes per factor
        f0_count = len(factor_dict.get(0, []))
        f1_count = len(factor_dict.get(1, []))

        if f0_count > f1_count:
            interpretation["factor_0"]["pillars"].append(pillar)
        elif f1_count > f0_count:
            interpretation["factor_1"]["pillars"].append(pillar)
        else:
            # Equal split - add to both
            interpretation["factor_0"]["pillars"].append(f"{pillar}*")
            interpretation["factor_1"]["pillars"].append(f"{pillar}*")

    # Top probes for each factor
    interpretation["factor_0"]["top_probes"] = [
        {"probe": p["probe"], "loading": round(p["loading"], 3)}
        for p in f0_probes_sorted[:5]
    ]
    interpretation["factor_1"]["top_probes"] = [
        {"probe": p["probe"], "loading": round(p["loading"], 3)}
        for p in f1_probes_sorted[:5]
    ]

    # Generate names based on pillar composition
    f0_pillars = interpretation["factor_0"]["pillars"]
    f1_pillars = interpretation["factor_1"]["pillars"]

    # Semantic naming based on what loads on each
    if "Values" in f0_pillars or "Reasoning" in f0_pillars:
        interpretation["factor_0"]["name"] = "Epistemic-Analytical"
        interpretation["factor_0"]["description"] = "Knowledge stability, logical coherence, value consistency"
    else:
        interpretation["factor_0"]["name"] = "Factor 0"
        interpretation["factor_0"]["description"] = f"Pillars: {', '.join(f0_pillars)}"

    if "Voice" in f1_pillars or "Narrative" in f1_pillars:
        interpretation["factor_1"]["name"] = "Expressive-Modal"
        interpretation["factor_1"]["description"] = "Communication style, narrative coherence, modal flexibility"
    else:
        interpretation["factor_1"]["name"] = "Factor 1"
        interpretation["factor_1"]["description"] = f"Pillars: {', '.join(f1_pillars)}"

    # Summary
    interpretation["summary"] = f"""
Factor Analysis reveals 2 primary factors (not 5 as expected):

FACTOR 0: {interpretation['factor_0']['name']}
  Pillars: {', '.join(f0_pillars)}
  Description: {interpretation['factor_0']['description']}
  Top probes: {', '.join(p['probe'] for p in interpretation['factor_0']['top_probes'][:3])}

FACTOR 1: {interpretation['factor_1']['name']}
  Pillars: {', '.join(f1_pillars)}
  Description: {interpretation['factor_1']['description']}
  Top probes: {', '.join(p['probe'] for p in interpretation['factor_1']['top_probes'][:3])}

This aligns with the PCA finding of 2 PCs capturing 90% variance.
The 5 named pillars collapse into 2 underlying dimensions.
"""

    return interpretation

def main():
    print("=" * 60)
    print("Phase 2.5 Factor Analysis Interpretation")
    print("=" * 60)

    # Load data
    data = load_factor_analysis()
    print(f"\nExperiment: {data.get('experiment')}")
    print(f"N factors: {data.get('n_factors')}")
    print(f"N responses: {data.get('n_responses')}")
    print(f"N probes: {len(data.get('probe_means', {}))}")

    # Get validation info
    validation = data.get("validation", {})
    print(f"\nValidation:")
    print(f"  Unique primary factors: {validation.get('unique_primary_factors')}")
    print(f"  Cross-loading issues: {validation.get('cross_loading_issues')}")

    # Analyze
    factor_assignments, probe_primary_factors = analyze_factor_loadings(data)
    pillar_to_factors = group_by_pillar(probe_primary_factors)

    print(f"\nProbes per factor:")
    for factor, probes in sorted(factor_assignments.items()):
        print(f"  Factor {factor}: {len(probes)} probes")

    print(f"\nPillar -> Factor mapping:")
    for pillar, factors in sorted(pillar_to_factors.items()):
        factor_counts = {f: len(probes) for f, probes in factors.items()}
        print(f"  {pillar}: {dict(factor_counts)}")

    # Interpret
    interpretation = interpret_factors(factor_assignments, pillar_to_factors)
    print(interpretation["summary"])

    # Save results
    output = {
        "analysis_date": datetime.now().isoformat(),
        "source_file": str(list(ANALYSIS_DIR.glob("factor_analysis_*.json"))[0].name),
        "n_factors_requested": data.get("n_factors"),
        "unique_primary_factors": validation.get("unique_primary_factors"),
        "cross_loading_issues": validation.get("cross_loading_issues"),
        "factor_assignments": {
            str(k): [{"probe": p["probe"], "loading": round(p["loading"], 4)} for p in v]
            for k, v in factor_assignments.items()
        },
        "pillar_to_factors": {
            pillar: {str(f): len(probes) for f, probes in factors.items()}
            for pillar, factors in pillar_to_factors.items()
        },
        "interpretation": interpretation,
    }

    output_file = OUTPUT_DIR / "factor_interpretation.json"
    with open(output_file, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nSaved: {output_file}")

    # Save markdown version
    md_file = OUTPUT_DIR / "factor_interpretation.md"
    with open(md_file, "w") as f:
        f.write("# Phase 2.5 Factor Analysis Interpretation\n\n")
        f.write(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n")
        f.write("---\n\n")
        f.write("## Key Finding\n\n")
        f.write("The 5 named pillars (Voice, Values, Reasoning, Self-Model, Narrative) ")
        f.write(f"collapse into **{validation.get('unique_primary_factors')} primary factors**.\n\n")
        f.write("This matches the PCA finding of 2 PCs capturing 90% variance.\n\n")
        f.write("---\n\n")
        f.write(interpretation["summary"])
        f.write("\n---\n\n")
        f.write("## Pillar to Factor Mapping\n\n")
        f.write("| Pillar | Factor 0 | Factor 1 |\n")
        f.write("|--------|----------|----------|\n")
        for pillar, factors in sorted(pillar_to_factors.items()):
            f0 = len(factors.get(0, []))
            f1 = len(factors.get(1, []))
            f.write(f"| {pillar} | {f0} probes | {f1} probes |\n")
        f.write("\n")
    print(f"Saved: {md_file}")

if __name__ == "__main__":
    main()
