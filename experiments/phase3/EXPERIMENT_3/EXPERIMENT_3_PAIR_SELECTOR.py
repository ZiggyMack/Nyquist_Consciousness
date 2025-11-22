"""
EXPERIMENT 3 — PAIR SELECTOR
Select 30 FULL-T3 pairs from EXP2 for human validation.

Implements stratified sampling across:
- Personas (4: Ziggy, Nova, Claude-Analyst, Grok-Vector)
- Domains (5: TECH, PHIL, NARR, ANAL, SELF)
- PFI tiers (high, mid, low)

Output:
- EXPERIMENT_3_PAIRS.json (full pair data with response texts)
- EXPERIMENT_3_PAIRS_TABLE.csv (metadata table)
"""

import pandas as pd
import json
import os
from pathlib import Path

# Configuration
EXP2_RESULTS_PATH = "../EXPERIMENT_2/EXPERIMENT_2_RESULTS.csv"
EXP2_RESPONSES_DIR = "../EXPERIMENT_2/responses/"
OUTPUT_JSON = "EXPERIMENT_3_PAIRS.json"
OUTPUT_CSV = "EXPERIMENT_3_PAIRS_TABLE.csv"
RANDOM_SEED = 42

# Slot allocation (30 total)
SLOT_TABLE = {
    'Ziggy': {'count_per_domain': 2, 'total': 10},
    'Nova': {'count_per_domain': 1, 'total': 5},
    'Claude-Analyst': {'count_per_domain': 1, 'total': 5},
    'Grok-Vector': {'count_per_domain': 1, 'total': 5},
    'Wildcard': {'count_per_domain': 0, 'total': 5}  # Flexible allocation
}

DOMAINS = ['TECH', 'PHIL', 'NARR', 'ANAL', 'SELF']

def load_exp2_data():
    """Load EXP2 results and filter for FULL vs T3 comparisons."""
    print("Loading EXP2 results...")

    df = pd.read_csv(EXP2_RESULTS_PATH)

    # Filter for FULL and T3 only
    df = df[df['regime'].isin(['FULL', 'T3'])]

    print(f"Loaded {len(df)} FULL/T3 records")

    # Group by persona, domain, run to get pairs
    # Each pair needs both FULL and T3 for the same (persona, domain, run)
    pairs = df.groupby(['persona', 'domain', 'run_index']).filter(
        lambda x: len(x) == 2 and set(x['regime']) == {'FULL', 'T3'}
    )

    # Get mean PFI per pair
    pair_pfi = pairs.groupby(['persona', 'domain', 'run_index'])['pfi'].mean().reset_index()

    print(f"Found {len(pair_pfi)} valid FULL-T3 pairs")

    return pair_pfi

def stratify_by_pfi(pairs_df):
    """Stratify pairs into high/mid/low PFI tiers."""
    high_pfi = pairs_df[pairs_df['pfi'] >= 0.90].copy()
    mid_pfi = pairs_df[(pairs_df['pfi'] >= 0.80) & (pairs_df['pfi'] < 0.90)].copy()
    low_pfi = pairs_df[(pairs_df['pfi'] >= 0.70) & (pairs_df['pfi'] < 0.80)].copy()

    print(f"\nPFI Stratification:")
    print(f"  High (≥0.90): {len(high_pfi)} pairs")
    print(f"  Mid (0.80-0.89): {len(mid_pfi)} pairs")
    print(f"  Low (0.70-0.79): {len(low_pfi)} pairs")

    return high_pfi, mid_pfi, low_pfi

def select_pairs_by_slots(pairs_df):
    """Select pairs according to slot table allocation."""
    selected_pairs = []

    # For each persona (except wildcard)
    for persona in ['Ziggy', 'Nova', 'Claude-Analyst', 'Grok-Vector']:
        count_per_domain = SLOT_TABLE[persona]['count_per_domain']

        print(f"\nSelecting pairs for {persona}:")

        # For each domain
        for domain in DOMAINS:
            # Filter for this persona+domain
            persona_domain_pairs = pairs_df[
                (pairs_df['persona'] == persona) &
                (pairs_df['domain'] == domain)
            ]

            if len(persona_domain_pairs) >= count_per_domain:
                # Randomly sample
                sampled = persona_domain_pairs.sample(
                    n=count_per_domain,
                    random_state=RANDOM_SEED
                )
                selected_pairs.append(sampled)
                print(f"  {domain}: selected {len(sampled)} pairs")
            else:
                print(f"  {domain}: WARNING - only {len(persona_domain_pairs)} available, need {count_per_domain}")
                selected_pairs.append(persona_domain_pairs)

    return pd.concat(selected_pairs, ignore_index=True) if selected_pairs else pd.DataFrame()

def add_wildcard_pairs(selected_df, all_pairs_df, target_count=30):
    """Add wildcard pairs to reach target count, prioritizing high-variance domains."""
    current_count = len(selected_df)
    needed = target_count - current_count

    if needed <= 0:
        print(f"\nAlready have {current_count} pairs, no wildcards needed")
        return selected_df

    print(f"\nAdding {needed} wildcard pairs...")

    # Exclude already selected pairs
    available = all_pairs_df[~all_pairs_df.index.isin(selected_df.index)]

    # Prioritize NARR and ANAL (high-variance domains)
    priority_domains = ['NARR', 'ANAL', 'SELF']
    priority_pairs = available[available['domain'].isin(priority_domains)]

    if len(priority_pairs) >= needed:
        wildcards = priority_pairs.sample(n=needed, random_state=RANDOM_SEED)
    else:
        # Take all priority pairs, then sample from others
        wildcards = pd.concat([
            priority_pairs,
            available[~available['domain'].isin(priority_domains)].sample(
                n=needed - len(priority_pairs),
                random_state=RANDOM_SEED
            )
        ])

    print(f"  Added {len(wildcards)} wildcard pairs")

    return pd.concat([selected_df, wildcards], ignore_index=True)

def load_response_text(persona, domain, run_index, regime):
    """Load response text from file."""
    # Response filename pattern from EXP2
    filename = f"{persona}_{regime}_{domain}_run{run_index}_{regime}.txt"
    filepath = os.path.join(EXP2_RESPONSES_DIR, filename)

    if not os.path.exists(filepath):
        print(f"  WARNING: File not found: {filepath}")
        return None

    with open(filepath, 'r', encoding='utf-8') as f:
        return f.read()

def construct_pairs_with_text(selected_df):
    """Construct pair data with response texts."""
    print("\nLoading response texts...")

    pair_data = []

    for idx, row in selected_df.iterrows():
        persona = row['persona']
        domain = row['domain']
        run = row['run_index']

        # Load FULL and T3 response texts
        full_text = load_response_text(persona, domain, run, 'FULL')
        t3_text = load_response_text(persona, domain, run, 'T3')

        if full_text is None or t3_text is None:
            print(f"  Skipping pair {persona}_{domain}_run{run} (missing files)")
            continue

        pair_id = f"{persona}_{domain}_run{run}"

        pair_data.append({
            'pair_id': pair_id,
            'persona': persona,
            'domain': domain,
            'run': run,
            'pfi_model': row['pfi'],
            'full_text': full_text,
            't3_text': t3_text
        })

    print(f"Successfully loaded {len(pair_data)} pairs with response texts")

    return pair_data

def save_outputs(pair_data):
    """Save pair data to JSON and CSV."""
    print(f"\nSaving outputs...")

    # Save full JSON
    with open(OUTPUT_JSON, 'w', encoding='utf-8') as f:
        json.dump(pair_data, f, indent=2, ensure_ascii=False)
    print(f"  Saved {OUTPUT_JSON}")

    # Save metadata CSV (without full text)
    metadata = pd.DataFrame([
        {k: v for k, v in p.items() if k not in ['full_text', 't3_text']}
        for p in pair_data
    ])
    metadata.to_csv(OUTPUT_CSV, index=False)
    print(f"  Saved {OUTPUT_CSV}")

    return metadata

def verify_selection(metadata_df):
    """Verify selection meets requirements."""
    print("\n" + "="*60)
    print("SELECTION VERIFICATION")
    print("="*60)

    checks = {
        "Total pairs = 30": len(metadata_df) == 30,
        "All 4 personas present": len(metadata_df['persona'].unique()) == 4,
        "All 5 domains present": len(metadata_df['domain'].unique()) == 5,
        "PFI range adequate": (metadata_df['pfi_model'].max() - metadata_df['pfi_model'].min()) > 0.15
    }

    for check, passed in checks.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{status}: {check}")

    # PFI distribution
    print("\nPFI Distribution:")
    print(f"  High (≥0.90): {len(metadata_df[metadata_df['pfi_model'] >= 0.90])}")
    print(f"  Mid (0.80-0.89): {len(metadata_df[(metadata_df['pfi_model'] >= 0.80) & (metadata_df['pfi_model'] < 0.90)])}")
    print(f"  Low (0.70-0.79): {len(metadata_df[(metadata_df['pfi_model'] >= 0.70) & (metadata_df['pfi_model'] < 0.80)])}")

    # Persona distribution
    print("\nPersona Distribution:")
    print(metadata_df['persona'].value_counts().to_string())

    # Domain distribution
    print("\nDomain Distribution:")
    print(metadata_df['domain'].value_counts().to_string())

    all_passed = all(checks.values())

    if all_passed:
        print("\n🎉 ALL CHECKS PASSED — Ready for human rating!")
    else:
        print("\n⚠️ SOME CHECKS FAILED — Review selection")

    return all_passed

def main():
    """Main pair selection pipeline."""
    print("="*60)
    print("EXPERIMENT 3 — PAIR SELECTOR")
    print("="*60)

    # Load data
    pairs_df = load_exp2_data()

    # Stratify by PFI
    high, mid, low = stratify_by_pfi(pairs_df)

    # Select pairs according to slot table
    selected_df = select_pairs_by_slots(pairs_df)

    # Add wildcards to reach 30
    selected_df = add_wildcard_pairs(selected_df, pairs_df, target_count=30)

    # Load response texts
    pair_data = construct_pairs_with_text(selected_df)

    # Save outputs
    metadata_df = save_outputs(pair_data)

    # Verify
    success = verify_selection(metadata_df)

    print("\n✅ Pair selection complete!")
    print(f"Review {OUTPUT_JSON} and {OUTPUT_CSV}")

    return success

if __name__ == "__main__":
    main()
