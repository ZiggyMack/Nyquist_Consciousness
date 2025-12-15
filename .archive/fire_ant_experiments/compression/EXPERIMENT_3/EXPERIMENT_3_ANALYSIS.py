"""
EXPERIMENT 3 — HUMAN VALIDATION ANALYSIS
Compute inter-rater reliability, correlations, and combined PFI metrics.

Requirements:
- EXPERIMENT_3_RESULTS_RAW.csv (per-rater responses)
- EXP1/EXP2 results with PFI_model values
- pandas, numpy, scipy, pingouin (or similar stats libraries)

Output:
- EXPERIMENT_3_RESULTS_AGG.csv (aggregated PFI_human per pair)
- EXPERIMENT_3_STATS_OUTPUT.txt (statistical summary)
"""

import pandas as pd
import numpy as np
import os
from scipy import stats
from scipy.stats import pearsonr
import warnings
warnings.filterwarnings('ignore')

# Configuration
RAW_DATA_PATH = "data/results/EXPERIMENT_3_RESULTS_RAW.csv"
PAIRS_TABLE_PATH = "EXPERIMENT_3_PAIRS_TABLE.csv"
EXP1_DATA_PATH = "../EXPERIMENT_1/EXPERIMENT_1_DEMONSTRATION_DATA.csv"
EXP2_DATA_PATH = "../EXPERIMENT_2/EXPERIMENT_2_RESULTS.csv"
OUTPUT_AGG_PATH = "data/results/EXPERIMENT_3_RESULTS_AGG.csv"
OUTPUT_STATS_PATH = "data/results/EXPERIMENT_3_STATS_OUTPUT.txt"
OUTPUT_ANALYSIS_MD = "EXPERIMENT_3_ANALYSIS.md"

def load_data():
    """Load raw rater data and model PFI from EXP1/EXP2."""
    print("Loading data...")

    # Load human ratings
    human_df = pd.read_csv(RAW_DATA_PATH)

    # Load model PFI from experiments
    exp1_df = pd.read_csv(EXP1_DATA_PATH)
    exp2_df = pd.read_csv(EXP2_DATA_PATH)

    # Filter for FULL vs T3 comparisons only
    exp1_full_t3 = exp1_df[exp1_df['regime'].isin(['FULL', 'T3'])]
    exp2_full_t3 = exp2_df[exp2_df['regime'].isin(['FULL', 'T3'])]

    return human_df, exp1_full_t3, exp2_full_t3

def compute_inter_rater_reliability(human_df):
    """Compute Cronbach's alpha for inter-rater reliability."""
    print("\n=== INTER-RATER RELIABILITY ===")

    # Pivot to get raters as columns for each trial
    dimensions = ['dim4_overall_similarity']  # Use overall similarity for reliability

    reliability_results = {}

    for dim in dimensions:
        # Create matrix: rows=trials, cols=raters
        pivot = human_df.pivot_table(
            index='trial_id',
            columns='rater_id',
            values=dim,
            aggfunc='first'
        )

        # Compute Cronbach's alpha
        alpha = compute_cronbachs_alpha(pivot.values)
        reliability_results[dim] = alpha

        print(f"{dim}: α = {alpha:.3f}")

    overall_alpha = reliability_results['dim4_overall_similarity']

    if overall_alpha >= 0.75:
        print(f"\n✅ PASS: Inter-rater reliability (α={overall_alpha:.3f}) ≥ 0.75")
    else:
        print(f"\n⚠️ WARNING: Inter-rater reliability (α={overall_alpha:.3f}) < 0.75")

    return overall_alpha

def compute_cronbachs_alpha(data):
    """
    Compute Cronbach's alpha for reliability.
    data: matrix of shape (n_items, n_raters)
    """
    n_items, n_raters = data.shape

    # Variance of sum of scores
    sum_scores = np.nansum(data, axis=1)
    var_sum = np.var(sum_scores, ddof=1)

    # Sum of variances
    var_items = np.nanvar(data, axis=0, ddof=1)
    sum_var = np.sum(var_items)

    # Cronbach's alpha formula
    alpha = (n_raters / (n_raters - 1)) * (1 - (sum_var / var_sum))

    return alpha

def aggregate_human_pfi(human_df):
    """Aggregate per-rater scores into single PFI_human per pair."""
    print("\n=== AGGREGATING HUMAN PFI ===")

    # Compute PFI_human_raw as mean of 4 dimensions per rater per trial
    human_df['pfi_human_raw'] = human_df[[
        'dim1_identity_voice',
        'dim2_values_priorities',
        'dim3_reasoning_style',
        'dim4_overall_similarity'
    ]].mean(axis=1)

    # Normalize to [0,1]
    human_df['pfi_human'] = (human_df['pfi_human_raw'] - 1) / 9

    # Aggregate across raters for each trial
    agg_df = human_df.groupby('trial_id').agg({
        'persona': 'first',
        'domain': 'first',
        'pfi_human': ['mean', 'std', 'count']
    }).reset_index()

    agg_df.columns = ['trial_id', 'persona', 'domain', 'pfi_human_mean', 'pfi_human_std', 'n_raters']

    print(f"Aggregated {len(agg_df)} trial pairs across {agg_df['n_raters'].iloc[0]} raters")
    print(f"Mean PFI_human: {agg_df['pfi_human_mean'].mean():.3f}")
    print(f"SD PFI_human: {agg_df['pfi_human_mean'].std():.3f}")

    return agg_df

def merge_with_model_pfi(agg_df, exp1_df, exp2_df):
    """Merge human PFI with model PFI from experiments."""
    print("\n=== MERGING WITH MODEL PFI ===")

    # For this to work, need trial_id to map to specific (persona, domain, run) combos
    # Simplified: assume trials map to experiment results by order or explicit ID

    # Combine EXP1 and EXP2 model PFI
    model_df = pd.concat([
        exp1_df[['persona', 'domain', 'run_index', 'pfi']],
        exp2_df[['persona', 'domain', 'run_index', 'pfi']]
    ])

    model_df = model_df.rename(columns={'pfi': 'pfi_model'})

    # Group by persona+domain to get mean model PFI
    model_agg = model_df.groupby(['persona', 'domain'])['pfi_model'].mean().reset_index()

    # Merge with human data
    merged_df = agg_df.merge(
        model_agg,
        on=['persona', 'domain'],
        how='left'
    )

    print(f"Merged {len(merged_df)} pairs")
    print(f"Mean PFI_model: {merged_df['pfi_model'].mean():.3f}")

    return merged_df

def compute_correlations(merged_df):
    """Compute correlation between human and model PFI."""
    print("\n=== MODEL-HUMAN CORRELATION ===")

    # Remove NaN values
    clean_df = merged_df.dropna(subset=['pfi_human_mean', 'pfi_model'])

    # Pearson correlation
    r, p = pearsonr(clean_df['pfi_model'], clean_df['pfi_human_mean'])

    print(f"Pearson r = {r:.3f}, p = {p:.4f}")

    if r >= 0.70 and p < 0.05:
        print(f"✅ PASS: Correlation (r={r:.3f}) ≥ 0.70 and significant")
    else:
        print(f"⚠️ WARNING: Correlation criteria not met")

    return r, p

def analyze_by_domain(merged_df):
    """Analyze PFI_human by domain."""
    print("\n=== DOMAIN-LEVEL ANALYSIS ===")

    domain_stats = merged_df.groupby('domain')['pfi_human_mean'].agg([
        'mean', 'std', 'count'
    ]).reset_index()

    # Compute 95% CI
    domain_stats['ci_95'] = 1.96 * domain_stats['std'] / np.sqrt(domain_stats['count'])

    print("\nDomain PFI_human:")
    print(domain_stats.to_string(index=False))

    # Check domain hierarchy
    domain_order = domain_stats.sort_values('mean', ascending=False)
    print("\nDomain hierarchy (highest to lowest PFI_human):")
    print(domain_order[['domain', 'mean']].to_string(index=False))

    return domain_stats

def analyze_by_persona(merged_df):
    """Analyze PFI_human by persona."""
    print("\n=== PERSONA-LEVEL ANALYSIS ===")

    persona_stats = merged_df.groupby('persona')['pfi_human_mean'].agg([
        'mean', 'std', 'count'
    ]).reset_index()

    # Compute 95% CI
    persona_stats['ci_95'] = 1.96 * persona_stats['std'] / np.sqrt(persona_stats['count'])

    print("\nPersona PFI_human:")
    print(persona_stats.to_string(index=False))

    return persona_stats

def compute_combined_pfi(merged_df):
    """Compute PFI_combined = 0.5 * (PFI_model + PFI_human)."""
    print("\n=== COMBINED PFI ===")

    merged_df['pfi_combined'] = 0.5 * (merged_df['pfi_model'] + merged_df['pfi_human_mean'])

    print(f"Mean PFI_combined: {merged_df['pfi_combined'].mean():.3f}")
    print(f"SD PFI_combined: {merged_df['pfi_combined'].std():.3f}")

    return merged_df

def check_success_criteria(alpha, r, mean_pfi_human, mean_pfi_combined):
    """Check all success criteria (H1-H4)."""
    print("\n" + "="*50)
    print("SUCCESS CRITERIA EVALUATION")
    print("="*50)

    criteria = {
        "H1: Persona Recognition (Mean PFI_human ≥ 0.75)": mean_pfi_human >= 0.75,
        "H2: Model-Human Alignment (r ≥ 0.70)": r >= 0.70,
        "H3: Inter-rater Reliability (α ≥ 0.75)": alpha >= 0.75,
        "H4: Combined Fidelity (Mean PFI_combined ≥ 0.80)": mean_pfi_combined >= 0.80
    }

    for criterion, passed in criteria.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{status}: {criterion}")

    all_passed = all(criteria.values())

    if all_passed:
        print("\n🎉 ALL CRITERIA MET — Human validation successful!")
    else:
        print("\n⚠️ SOME CRITERIA NOT MET — Review results")

    return all_passed

def generate_report(merged_df, alpha, r, p, domain_stats, persona_stats):
    """Generate summary report."""
    report = []

    report.append("=" * 60)
    report.append("EXPERIMENT 3 — STATISTICAL SUMMARY")
    report.append("Human Validation of Persona Fidelity")
    report.append("=" * 60)

    report.append("\n### INTER-RATER RELIABILITY")
    report.append(f"Cronbach's α: {alpha:.3f}")
    report.append(f"Status: {'PASS' if alpha >= 0.75 else 'WARNING'}")

    report.append("\n### MODEL-HUMAN CORRELATION")
    report.append(f"Pearson r: {r:.3f}")
    report.append(f"p-value: {p:.4f}")
    report.append(f"Status: {'PASS' if (r >= 0.70 and p < 0.05) else 'WARNING'}")

    report.append("\n### OVERALL PFI METRICS")
    report.append(f"Mean PFI_human: {merged_df['pfi_human_mean'].mean():.3f}")
    report.append(f"Mean PFI_model: {merged_df['pfi_model'].mean():.3f}")
    report.append(f"Mean PFI_combined: {merged_df['pfi_combined'].mean():.3f}")

    report.append("\n### DOMAIN ANALYSIS")
    report.append(domain_stats.to_string(index=False))

    report.append("\n### PERSONA ANALYSIS")
    report.append(persona_stats.to_string(index=False))

    report.append("\n" + "=" * 60)
    report.append("END OF REPORT")
    report.append("=" * 60)

    return "\n".join(report)

def main():
    """Main analysis pipeline."""
    print("EXPERIMENT 3 — HUMAN VALIDATION ANALYSIS")
    print("=" * 60)

    # Create output directories
    os.makedirs("data/results", exist_ok=True)

    # Load data
    human_df, exp1_df, exp2_df = load_data()

    # Compute inter-rater reliability
    alpha = compute_inter_rater_reliability(human_df)

    # Aggregate human PFI
    agg_df = aggregate_human_pfi(human_df)

    # Merge with model PFI
    merged_df = merge_with_model_pfi(agg_df, exp1_df, exp2_df)

    # Compute correlations
    r, p = compute_correlations(merged_df)

    # Domain analysis
    domain_stats = analyze_by_domain(merged_df)

    # Persona analysis
    persona_stats = analyze_by_persona(merged_df)

    # Compute combined PFI
    merged_df = compute_combined_pfi(merged_df)

    # Check success criteria
    mean_pfi_human = merged_df['pfi_human_mean'].mean()
    mean_pfi_combined = merged_df['pfi_combined'].mean()
    success = check_success_criteria(alpha, r, mean_pfi_human, mean_pfi_combined)

    # Save outputs
    print(f"\nSaving aggregated results to {OUTPUT_AGG_PATH}")
    merged_df.to_csv(OUTPUT_AGG_PATH, index=False)

    # Generate and save report
    report = generate_report(merged_df, alpha, r, p, domain_stats, persona_stats)

    print(f"Saving statistical report to {OUTPUT_STATS_PATH}")
    with open(OUTPUT_STATS_PATH, 'w') as f:
        f.write(report)

    print("\n✅ Analysis complete!")
    print(f"Review {OUTPUT_STATS_PATH} for full statistical summary.")

if __name__ == "__main__":
    main()
