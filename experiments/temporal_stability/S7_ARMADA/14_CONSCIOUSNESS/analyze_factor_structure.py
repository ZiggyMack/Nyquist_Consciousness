"""
FACTOR STRUCTURE ANALYSIS
=========================
Analyze the factor structure of Gold Rush + Diamond Rush responses.

PURPOSE:
--------
Address the "2 → 10 → ?" question from IRON CLAD:
- IRON CLAD found 2 PCs capture 90% of variance
- We named 10 dimensions (pillars)
- Are they the same thing? What ARE those 2 PCs?

METHODOLOGY:
------------
1. Load Gold Rush (self-assessment) and Diamond Rush (cross-model interpretation) data
2. Generate embeddings for each response using text-embedding-3-small
3. Run PCA to extract principal components
4. Attempt semantic interpretation of the axes
5. Run factor analysis to see if pillars cluster

USAGE:
------
py analyze_factor_structure.py                  # Full analysis
py analyze_factor_structure.py --gold-only      # Just Gold Rush
py analyze_factor_structure.py --diamond-only   # Just Diamond Rush
py analyze_factor_structure.py --skip-embed     # Use cached embeddings

OUTPUT:
-------
- factor_analysis_results.json
- Visualizations in results/factor_plots/

Author: VALIS NETWORK / Consciousness Branch
Date: 2025-12-31
"""

import os
import sys
import json
import argparse
from datetime import datetime
from pathlib import Path
from collections import defaultdict
import numpy as np

# Fix Windows encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"

# Load .env for API keys
from dotenv import load_dotenv
env_path = ARMADA_DIR / ".env"
if env_path.exists():
    load_dotenv(env_path)

# OpenAI for embeddings
import openai


def load_gold_rush_data():
    """Load Gold Rush self-assessment responses."""
    gold_file = RESULTS_DIR / "gold_rush_20251231_193159.json"
    if not gold_file.exists():
        print("[WARN] Gold Rush data not found")
        return []

    with open(gold_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    responses = []
    for result in data.get("results", []):
        if result.get("success") and result.get("response"):
            responses.append({
                "source": "gold_rush",
                "ship": result.get("ship_name"),
                "provider": result.get("provider"),
                "question_set": result.get("question_set"),
                "text": result["response"],
            })

    print(f"[GOLD] Loaded {len(responses)} responses")
    return responses


def load_diamond_rush_data():
    """Load Diamond Rush cross-model interpretation responses."""
    diamond_file = RESULTS_DIR / "diamond_rush_gravity_20251231_193824.json"
    if not diamond_file.exists():
        print("[WARN] Diamond Rush data not found")
        return []

    with open(diamond_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    responses = []
    for result in data.get("results", []):
        if result.get("success") and result.get("response"):
            responses.append({
                "source": "diamond_rush",
                "ship": result.get("ship_name"),
                "provider": result.get("provider"),
                "log_analyzed": result.get("log_source"),
                "text": result["response"],
            })

    print(f"[DIAMOND] Loaded {len(responses)} responses")
    return responses


def generate_embeddings(responses, cache_file=None):
    """Generate embeddings for all responses using text-embedding-3-small."""

    # Check cache
    if cache_file and cache_file.exists():
        print(f"[EMBED] Loading cached embeddings from {cache_file}")
        with open(cache_file, "r", encoding="utf-8") as f:
            return json.load(f)

    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("[ERROR] OPENAI_API_KEY not found")
        return None

    client = openai.OpenAI(api_key=api_key)

    print(f"[EMBED] Generating embeddings for {len(responses)} responses...")

    embeddings = []
    for i, resp in enumerate(responses):
        try:
            # Truncate to avoid token limits
            text = resp["text"][:8000]

            result = client.embeddings.create(
                model="text-embedding-3-small",
                input=text
            )

            embedding = result.data[0].embedding
            embeddings.append({
                **resp,
                "embedding": embedding
            })

            if (i + 1) % 10 == 0:
                print(f"  [{i+1}/{len(responses)}] embedded...")

        except Exception as e:
            print(f"  [ERROR] {resp.get('ship')}: {e}")
            continue

    # Cache results
    if cache_file:
        cache_file.parent.mkdir(parents=True, exist_ok=True)
        with open(cache_file, "w", encoding="utf-8") as f:
            json.dump(embeddings, f)
        print(f"[EMBED] Cached to {cache_file}")

    return embeddings


def run_pca_analysis(embeddings, n_components=10):
    """Run PCA on the embeddings and extract principal components."""
    from sklearn.decomposition import PCA
    from sklearn.preprocessing import StandardScaler

    # Extract embedding vectors
    X = np.array([e["embedding"] for e in embeddings])

    print(f"\n[PCA] Running PCA on {X.shape[0]} samples x {X.shape[1]} dimensions")

    # Standardize
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(X)

    # Run PCA
    pca = PCA(n_components=n_components)
    X_pca = pca.fit_transform(X_scaled)

    # Analyze variance explained
    var_explained = pca.explained_variance_ratio_
    cumulative_var = np.cumsum(var_explained)

    print("\n--- VARIANCE EXPLAINED ---")
    for i, (var, cum) in enumerate(zip(var_explained, cumulative_var)):
        bar = "#" * int(var * 50)
        print(f"  PC{i+1}: {var*100:5.2f}% (cum: {cum*100:5.2f}%) {bar}")

    # Find how many PCs for 90% variance
    n_for_90 = np.argmax(cumulative_var >= 0.90) + 1
    print(f"\n[PCA] {n_for_90} PCs needed for 90% variance")

    return {
        "pca_model": pca,
        "X_pca": X_pca,
        "variance_explained": var_explained.tolist(),
        "cumulative_variance": cumulative_var.tolist(),
        "n_for_90_percent": int(n_for_90),
    }


def analyze_pc_by_metadata(embeddings, pca_results):
    """Analyze how metadata (ship, provider, source) relates to PC scores."""
    X_pca = pca_results["X_pca"]

    print("\n--- PC SCORES BY PROVIDER ---")
    by_provider = defaultdict(list)
    for i, e in enumerate(embeddings):
        provider = e.get("provider", "unknown")
        by_provider[provider].append(X_pca[i])

    for provider, scores in sorted(by_provider.items()):
        scores = np.array(scores)
        mean_pc1 = np.mean(scores[:, 0])
        mean_pc2 = np.mean(scores[:, 1])
        print(f"  {provider:12s}: PC1={mean_pc1:+6.3f}, PC2={mean_pc2:+6.3f} (n={len(scores)})")

    print("\n--- PC SCORES BY SOURCE ---")
    by_source = defaultdict(list)
    for i, e in enumerate(embeddings):
        source = e.get("source", "unknown")
        by_source[source].append(X_pca[i])

    for source, scores in sorted(by_source.items()):
        scores = np.array(scores)
        mean_pc1 = np.mean(scores[:, 0])
        mean_pc2 = np.mean(scores[:, 1])
        print(f"  {source:15s}: PC1={mean_pc1:+6.3f}, PC2={mean_pc2:+6.3f} (n={len(scores)})")

    print("\n--- PC SCORES BY SHIP (Top 10 by PC1) ---")
    by_ship = defaultdict(list)
    for i, e in enumerate(embeddings):
        ship = e.get("ship", "unknown")
        by_ship[ship].append(X_pca[i])

    ship_means = []
    for ship, scores in by_ship.items():
        scores = np.array(scores)
        ship_means.append((ship, np.mean(scores[:, 0]), np.mean(scores[:, 1]), len(scores)))

    ship_means.sort(key=lambda x: x[1], reverse=True)
    for ship, pc1, pc2, n in ship_means[:10]:
        print(f"  {ship:30s}: PC1={pc1:+6.3f}, PC2={pc2:+6.3f} (n={n})")

    return by_provider, by_source, by_ship


def interpret_pcs(embeddings, pca_results):
    """Attempt to interpret what PC1 and PC2 represent semantically."""
    X_pca = pca_results["X_pca"]

    print("\n" + "=" * 60)
    print("PC INTERPRETATION ANALYSIS")
    print("=" * 60)

    # Find extreme samples on each PC
    pc1_high_idx = np.argsort(X_pca[:, 0])[-3:]  # Top 3 PC1
    pc1_low_idx = np.argsort(X_pca[:, 0])[:3]    # Bottom 3 PC1
    pc2_high_idx = np.argsort(X_pca[:, 1])[-3:]  # Top 3 PC2
    pc2_low_idx = np.argsort(X_pca[:, 1])[:3]    # Bottom 3 PC2

    print("\n--- HIGH PC1 (Top 3) ---")
    for idx in pc1_high_idx:
        e = embeddings[idx]
        print(f"\n[{e.get('ship')}] PC1={X_pca[idx, 0]:.3f}")
        print(f"  Source: {e.get('source')}, Question: {e.get('question_set', e.get('log_analyzed'))}")
        print(f"  Text preview: {e['text'][:200]}...")

    print("\n--- LOW PC1 (Bottom 3) ---")
    for idx in pc1_low_idx:
        e = embeddings[idx]
        print(f"\n[{e.get('ship')}] PC1={X_pca[idx, 0]:.3f}")
        print(f"  Source: {e.get('source')}, Question: {e.get('question_set', e.get('log_analyzed'))}")
        print(f"  Text preview: {e['text'][:200]}...")

    print("\n--- HIGH PC2 (Top 3) ---")
    for idx in pc2_high_idx:
        e = embeddings[idx]
        print(f"\n[{e.get('ship')}] PC2={X_pca[idx, 1]:.3f}")
        print(f"  Source: {e.get('source')}, Question: {e.get('question_set', e.get('log_analyzed'))}")
        print(f"  Text preview: {e['text'][:200]}...")

    print("\n--- LOW PC2 (Bottom 3) ---")
    for idx in pc2_low_idx:
        e = embeddings[idx]
        print(f"\n[{e.get('ship')}] PC2={X_pca[idx, 1]:.3f}")
        print(f"  Source: {e.get('source')}, Question: {e.get('question_set', e.get('log_analyzed'))}")
        print(f"  Text preview: {e['text'][:200]}...")


def main():
    parser = argparse.ArgumentParser(description="Factor Structure Analysis")
    parser.add_argument("--gold-only", action="store_true", help="Only analyze Gold Rush")
    parser.add_argument("--diamond-only", action="store_true", help="Only analyze Diamond Rush")
    parser.add_argument("--skip-embed", action="store_true", help="Use cached embeddings")
    parser.add_argument("--n-components", type=int, default=10, help="Number of PCs to extract")
    args = parser.parse_args()

    print("\n" + "=" * 60)
    print("FACTOR STRUCTURE ANALYSIS")
    print("Addressing the '2 -> 10 -> ?' Question")
    print("=" * 60)
    print(f"Time: {datetime.now().isoformat()}")

    # Load data
    responses = []
    if not args.diamond_only:
        responses.extend(load_gold_rush_data())
    if not args.gold_only:
        responses.extend(load_diamond_rush_data())

    if not responses:
        print("[ERROR] No data loaded")
        return

    print(f"\n[DATA] Total responses: {len(responses)}")

    # Generate embeddings
    cache_file = RESULTS_DIR / "factor_analysis_cache" / "embeddings_cache.json"
    embeddings = generate_embeddings(responses, cache_file=cache_file)

    if not embeddings:
        print("[ERROR] No embeddings generated")
        return

    # Run PCA
    pca_results = run_pca_analysis(embeddings, n_components=args.n_components)

    # Analyze by metadata
    analyze_pc_by_metadata(embeddings, pca_results)

    # Interpret PCs
    interpret_pcs(embeddings, pca_results)

    # Save results
    output = {
        "timestamp": datetime.now().isoformat(),
        "n_responses": len(responses),
        "n_embedded": len(embeddings),
        "pca_results": {
            "variance_explained": pca_results["variance_explained"],
            "cumulative_variance": pca_results["cumulative_variance"],
            "n_for_90_percent": pca_results["n_for_90_percent"],
        },
        "interpretation_notes": "See console output for extreme samples",
    }

    output_file = RESULTS_DIR / "factor_analysis_results.json"
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2)
    print(f"\n[SAVED] {output_file}")

    print("\n" + "=" * 60)
    print("ANALYSIS COMPLETE")
    print("=" * 60)
    print(f"""
KEY FINDINGS:
- {pca_results['n_for_90_percent']} PCs capture 90% of variance
- PC1 explains {pca_results['variance_explained'][0]*100:.1f}%
- PC2 explains {pca_results['variance_explained'][1]*100:.1f}%

NEXT STEPS:
1. Review extreme samples to interpret PC axes semantically
2. Test if Gold vs Diamond responses cluster differently
3. Compare to LOGOS Phi mapping hypothesis
4. Determine if 2 PCs = epistemic/ontological divide
""")


if __name__ == "__main__":
    main()
