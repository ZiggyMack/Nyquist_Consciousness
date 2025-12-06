"""
EXP2-SSTACK Phase 2.5: Factor Analysis — Pillar Validation
===========================================================

STATUS: SPEC / STARTING POINT — NOT YET TESTED

PURPOSE:
    Determine if our named pillars (Voice, Values, Reasoning, Self-Model, Narrative)
    are statistically distinct or overlapping constructs.

PREREQUISITES:
    - Phase 1 complete (5 Reasoning probes)
    - Phase 2 complete (16 Voice/Values/Narrative/Self-Model probes)
    - All response JSON files in results/ and results_phase2/

METHOD:
    1. Load all responses from Phase 1 + Phase 2
    2. Embed each response using text-embedding-3-large
    3. Run PCA to reduce 3072 dims → 100 dims
    4. Run Exploratory Factor Analysis with 5-10 factors
    5. Analyze factor loadings to see if probes cluster by pillar

SUCCESS CRITERIA:
    - Probes load ≥0.5 on "correct" factor: 80% of probes
    - Cross-loadings < 0.3: 80% of probes
    - 5-10 factors explain 70%+ variance

OUTPUT:
    - Factor loading heatmap (probes × factors)
    - Pillar-to-factor mapping table
    - Recommendations for probe refinement

Usage:
    py -3.12 run_exp2_phase2p5.py

Date: 2025-12-06
Version: 0.1 (SPEC - Initial Structure)
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
import numpy as np

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

# Load environment
def load_env():
    """Load API keys from .env file."""
    for env_path in [
        Path(__file__).parent.parent.parent.parent / 'temporal_stability' / 'S7_ARMADA' / '.env',
        Path(__file__).parent.parent.parent.parent.parent / '.env',
    ]:
        if env_path.exists():
            with open(env_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, value = line.split('=', 1)
                        os.environ[key.strip()] = value.strip()
            return True
    return False

load_env()

try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

try:
    from sklearn.decomposition import PCA, FactorAnalysis
    from sklearn.preprocessing import StandardScaler
    SKLEARN_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False

try:
    import matplotlib.pyplot as plt
    import seaborn as sns
    PLOTTING_AVAILABLE = True
except ImportError:
    PLOTTING_AVAILABLE = False


# =============================================================================
# PROBE METADATA — Which pillar does each probe belong to?
# =============================================================================

PROBE_PILLARS = {
    # Phase 1 probes (Reasoning + 1 Self-Model)
    "technical": "Reasoning",
    "philosophical": "Reasoning",
    "framework": "Reasoning",
    "analytical": "Reasoning",
    "self_reflective": "Self-Model",

    # Phase 2 probes
    "voice_style": "Voice",
    "voice_metaphor": "Voice",
    "voice_rhythm": "Voice",
    "voice_formality": "Voice",

    "values_ethics": "Values",
    "values_priorities": "Values",
    "values_boundaries": "Values",
    "values_preferences": "Values",

    "narrative_structure": "Narrative",
    "narrative_meaning": "Narrative",
    "narrative_temporal": "Narrative",
    "narrative_conflict": "Narrative",

    "selfmodel_capabilities": "Self-Model",
    "selfmodel_limitations": "Self-Model",
    "selfmodel_purpose": "Self-Model",
    "selfmodel_description": "Self-Model",
}

PILLARS = ["Voice", "Values", "Reasoning", "Self-Model", "Narrative"]


# =============================================================================
# DATA LOADING
# =============================================================================

def load_all_responses() -> List[Dict]:
    """Load all response files from Phase 1 and Phase 2."""
    responses = []
    base_dir = Path(__file__).parent

    # Phase 1 responses
    phase1_dir = base_dir / "results" / "responses"
    if phase1_dir.exists():
        for f in phase1_dir.glob("*.json"):
            with open(f) as fp:
                data = json.load(fp)
                data["phase"] = 1
                data["source_file"] = str(f.name)
                responses.append(data)

    # Phase 2 responses
    phase2_dir = base_dir / "results_phase2" / "responses"
    if phase2_dir.exists():
        for f in phase2_dir.glob("*.json"):
            with open(f) as fp:
                data = json.load(fp)
                data["phase"] = 2
                data["source_file"] = str(f.name)
                responses.append(data)

    print(f"Loaded {len(responses)} total responses")
    print(f"  Phase 1: {sum(1 for r in responses if r['phase'] == 1)}")
    print(f"  Phase 2: {sum(1 for r in responses if r['phase'] == 2)}")

    return responses


# =============================================================================
# EMBEDDING
# =============================================================================

def get_embeddings(texts: List[str], client: OpenAI) -> np.ndarray:
    """Get embeddings for a list of texts."""
    embeddings = []
    batch_size = 100  # OpenAI limit

    for i in range(0, len(texts), batch_size):
        batch = texts[i:i + batch_size]
        response = client.embeddings.create(
            model="text-embedding-3-large",
            input=batch
        )
        for item in response.data:
            embeddings.append(item.embedding)

    return np.array(embeddings)


# =============================================================================
# FACTOR ANALYSIS
# =============================================================================

def run_factor_analysis(
    embeddings: np.ndarray,
    probe_labels: List[str],
    n_pca_components: int = 100,
    n_factors: int = 5
) -> Tuple[np.ndarray, np.ndarray, float]:
    """
    Run PCA + Factor Analysis on embeddings.

    Returns:
        loadings: (n_probes, n_factors) factor loading matrix
        explained_var: variance explained by each factor
        total_var: total variance explained
    """
    print(f"\n[FACTOR ANALYSIS]")
    print(f"  Input: {embeddings.shape[0]} samples, {embeddings.shape[1]} dimensions")

    # Step 1: Standardize
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(embeddings)

    # Step 2: PCA to reduce dimensions
    print(f"  PCA: {embeddings.shape[1]} → {n_pca_components} dimensions")
    pca = PCA(n_components=n_pca_components)
    X_reduced = pca.fit_transform(X_scaled)
    pca_var = sum(pca.explained_variance_ratio_)
    print(f"  PCA variance explained: {pca_var:.2%}")

    # Step 3: Factor Analysis
    print(f"  Factor Analysis: {n_factors} factors")
    fa = FactorAnalysis(n_components=n_factors, random_state=42)
    factors = fa.fit_transform(X_reduced)

    # Compute loadings (correlation between original probes and factors)
    # For this, we need to aggregate embeddings by probe
    unique_probes = list(set(probe_labels))
    probe_means = []
    for probe in unique_probes:
        mask = [p == probe for p in probe_labels]
        probe_means.append(X_reduced[mask].mean(axis=0))
    probe_means = np.array(probe_means)

    # Get factor loadings for mean probe embeddings
    fa_probes = FactorAnalysis(n_components=n_factors, random_state=42)
    fa_probes.fit(probe_means)
    loadings = fa_probes.components_.T  # (n_probes, n_factors)

    return loadings, unique_probes, pca_var


def analyze_loadings(
    loadings: np.ndarray,
    probe_names: List[str],
    threshold_primary: float = 0.5,
    threshold_cross: float = 0.3
) -> Dict:
    """Analyze factor loadings to validate pillar structure."""

    results = {
        "probe_factor_assignments": {},
        "correct_assignments": 0,
        "cross_loadings": [],
        "pillar_factor_mapping": {},
    }

    # For each probe, find its primary factor
    for i, probe in enumerate(probe_names):
        probe_loadings = loadings[i]
        primary_factor = np.argmax(np.abs(probe_loadings))
        primary_loading = probe_loadings[primary_factor]

        # Check for cross-loadings
        cross_loaded = []
        for j, loading in enumerate(probe_loadings):
            if j != primary_factor and abs(loading) > threshold_cross:
                cross_loaded.append((j, loading))

        results["probe_factor_assignments"][probe] = {
            "primary_factor": int(primary_factor),
            "primary_loading": float(primary_loading),
            "cross_loadings": cross_loaded,
            "expected_pillar": PROBE_PILLARS.get(probe, "Unknown"),
        }

        if cross_loaded:
            results["cross_loadings"].append(probe)

    # Map factors to pillars (by majority vote)
    factor_pillar_votes = {}
    for probe, assignment in results["probe_factor_assignments"].items():
        factor = assignment["primary_factor"]
        pillar = assignment["expected_pillar"]
        if factor not in factor_pillar_votes:
            factor_pillar_votes[factor] = {}
        factor_pillar_votes[factor][pillar] = factor_pillar_votes[factor].get(pillar, 0) + 1

    for factor, votes in factor_pillar_votes.items():
        if votes:
            best_pillar = max(votes, key=votes.get)
            results["pillar_factor_mapping"][factor] = best_pillar

    # Count correct assignments
    for probe, assignment in results["probe_factor_assignments"].items():
        factor = assignment["primary_factor"]
        expected = assignment["expected_pillar"]
        if results["pillar_factor_mapping"].get(factor) == expected:
            results["correct_assignments"] += 1

    return results


# =============================================================================
# VISUALIZATION
# =============================================================================

def plot_factor_loadings(
    loadings: np.ndarray,
    probe_names: List[str],
    output_path: Path
):
    """Create a heatmap of factor loadings."""
    if not PLOTTING_AVAILABLE:
        print("Matplotlib/seaborn not available, skipping plot")
        return

    # Sort probes by pillar
    sorted_indices = sorted(
        range(len(probe_names)),
        key=lambda i: (PROBE_PILLARS.get(probe_names[i], "ZZZ"), probe_names[i])
    )
    sorted_probes = [probe_names[i] for i in sorted_indices]
    sorted_loadings = loadings[sorted_indices]

    # Add pillar labels
    probe_labels = [f"{p} ({PROBE_PILLARS.get(p, '?')})" for p in sorted_probes]

    plt.figure(figsize=(12, 10))
    sns.heatmap(
        sorted_loadings,
        xticklabels=[f"Factor {i}" for i in range(loadings.shape[1])],
        yticklabels=probe_labels,
        cmap="RdBu_r",
        center=0,
        annot=True,
        fmt=".2f",
    )
    plt.title("Factor Loadings by Probe\n(Probes grouped by expected pillar)")
    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()
    print(f"Saved factor loading heatmap to: {output_path}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    """Run Phase 2.5 Factor Analysis."""

    print("=" * 70)
    print("EXP2-SSTACK Phase 2.5: Factor Analysis — Pillar Validation")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print("STATUS: SPEC / INITIAL IMPLEMENTATION")
    print("=" * 70)

    # Check prerequisites
    if not OPENAI_AVAILABLE:
        print("ERROR: OpenAI not available. Install with: pip install openai")
        return

    if not SKLEARN_AVAILABLE:
        print("ERROR: scikit-learn not available. Install with: pip install scikit-learn")
        return

    # Load responses
    responses = load_all_responses()

    if len(responses) < 50:
        print(f"WARNING: Only {len(responses)} responses found.")
        print("Phase 2.5 requires Phase 1 AND Phase 2 to be complete.")
        print("Run Phase 2 first: py -3.12 run_exp2_phase2.py --parallel 10")
        return

    # Filter to FULL regime only (we're comparing probe types, not regimes)
    full_responses = [r for r in responses if r.get("regime") == "FULL"]
    print(f"\nUsing {len(full_responses)} FULL-regime responses for analysis")

    # Extract texts and labels
    texts = [r["response"] for r in full_responses]
    probe_labels = [r["probe_key"] for r in full_responses]

    # Get embeddings
    print("\n[EMBEDDING]")
    client = OpenAI()
    print(f"  Embedding {len(texts)} responses...")
    embeddings = get_embeddings(texts, client)
    print(f"  Got embeddings: {embeddings.shape}")

    # Run factor analysis
    loadings, probe_names, pca_var = run_factor_analysis(
        embeddings,
        probe_labels,
        n_pca_components=100,
        n_factors=5  # Our 5 pillars
    )

    # Analyze loadings
    print("\n[ANALYSIS]")
    analysis = analyze_loadings(loadings, probe_names)

    # Print results
    print("\n" + "=" * 70)
    print("RESULTS")
    print("=" * 70)

    print("\nFactor-to-Pillar Mapping:")
    for factor, pillar in sorted(analysis["pillar_factor_mapping"].items()):
        print(f"  Factor {factor} → {pillar}")

    print(f"\nCorrect Assignments: {analysis['correct_assignments']}/{len(probe_names)}")
    print(f"  ({100 * analysis['correct_assignments'] / len(probe_names):.1f}%)")

    print(f"\nProbes with Cross-Loadings: {len(analysis['cross_loadings'])}")
    for probe in analysis["cross_loadings"]:
        info = analysis["probe_factor_assignments"][probe]
        print(f"  {probe}: primary={info['primary_factor']}, cross={info['cross_loadings']}")

    # Visualize
    output_dir = Path(__file__).parent / "results_phase2p5"
    output_dir.mkdir(exist_ok=True)

    plot_factor_loadings(
        loadings,
        probe_names,
        output_dir / "factor_loadings_heatmap.png"
    )

    # Save results
    results = {
        "experiment": "EXP2-SSTACK-Phase2p5",
        "version": "0.1",
        "status": "SPEC",
        "timestamp": datetime.now().isoformat(),
        "n_responses": len(full_responses),
        "pca_variance_explained": float(pca_var),
        "analysis": analysis,
    }

    results_file = output_dir / f"phase2p5_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

    # Convert numpy types for JSON serialization
    def convert(obj):
        if isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        return obj

    with open(results_file, 'w') as f:
        json.dump(results, f, indent=2, default=convert)

    print(f"\nResults saved to: {results_file}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    correct_pct = 100 * analysis['correct_assignments'] / len(probe_names)
    cross_pct = 100 * len(analysis['cross_loadings']) / len(probe_names)

    if correct_pct >= 80 and cross_pct <= 20:
        print("STATUS: PILLARS VALIDATED")
        print("Our named dimensions appear to be statistically distinct.")
    elif correct_pct >= 60:
        print("STATUS: PARTIAL VALIDATION")
        print("Some pillars overlap. Consider refining probes.")
    else:
        print("STATUS: PILLARS NOT DISTINCT")
        print("Factor structure doesn't match our naming. Rethink dimensions.")

    print("=" * 70)


if __name__ == "__main__":
    main()
