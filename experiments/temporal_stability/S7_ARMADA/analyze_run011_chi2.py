#!/usr/bin/env python3
"""
Run 011 Statistical Analysis: Control vs Persona Fleet Comparison
=================================================================
Tests whether the Nyquist persona architecture produces statistically
different drift distributions than the control (vanilla) condition.

Hypothesis: Persona fleet will have lower drift and tighter clustering.
"""

import json
from pathlib import Path
import numpy as np
from scipy import stats

# Constants
EVENT_HORIZON = 1.23
DATA_FILE = Path(__file__).parent / "armada_results" / "S7_run_011_persona_20251203_080622.json"

def load_data():
    """Load Run 011 data."""
    with open(DATA_FILE, encoding='utf-8') as f:
        return json.load(f)

def extract_fleet_stats(data):
    """Extract drift statistics for control and persona fleets."""
    control_stats = {
        'drifts': [],          # All drift values
        'max_drifts': [],      # Max drift per ship
        'mean_drifts': [],     # Mean drift per ship
        'baselines': [],       # Initial drift values
        'stable_count': 0,
        'volatile_count': 0,
        'ships': []
    }

    persona_stats = {
        'drifts': [],
        'max_drifts': [],
        'mean_drifts': [],
        'baselines': [],
        'stable_count': 0,
        'volatile_count': 0,
        'ships': []
    }

    # Process control fleet
    for ship_data in data.get('control_fleet', []):
        turns = ship_data.get('turns', [])
        if not turns:
            continue

        drifts = [t['drift'] for t in turns if 'drift' in t]
        if len(drifts) < 3:
            continue

        control_stats['ships'].append(ship_data.get('ship', 'unknown'))
        control_stats['drifts'].extend(drifts)
        control_stats['max_drifts'].append(max(drifts))
        control_stats['mean_drifts'].append(np.mean(drifts))
        control_stats['baselines'].append(drifts[0])

        if max(drifts) >= EVENT_HORIZON:
            control_stats['volatile_count'] += 1
        else:
            control_stats['stable_count'] += 1

    # Process persona fleet
    for ship_data in data.get('persona_fleet', []):
        turns = ship_data.get('turns', [])
        if not turns:
            continue

        drifts = [t['drift'] for t in turns if 'drift' in t]
        if len(drifts) < 3:
            continue

        persona_stats['ships'].append(ship_data.get('ship', 'unknown'))
        persona_stats['drifts'].extend(drifts)
        persona_stats['max_drifts'].append(max(drifts))
        persona_stats['mean_drifts'].append(np.mean(drifts))
        persona_stats['baselines'].append(drifts[0])

        if max(drifts) >= EVENT_HORIZON:
            persona_stats['volatile_count'] += 1
        else:
            persona_stats['stable_count'] += 1

    return control_stats, persona_stats

def run_chi_squared(control, persona):
    """Chi-squared test: Is STABLE/VOLATILE distribution independent of fleet type?"""
    # Contingency table:
    #                  STABLE    VOLATILE
    # Control          a         b
    # Persona          c         d

    observed = np.array([
        [control['stable_count'], control['volatile_count']],
        [persona['stable_count'], persona['volatile_count']]
    ])

    # Check if we have enough data
    if observed.sum() < 10:
        return None, None, "Insufficient data"

    # Check for zero cells (would break chi-squared)
    if 0 in observed.flatten():
        # Use Fisher's exact test instead
        odds_ratio, p_value = stats.fisher_exact(observed)
        return None, p_value, f"Fisher's exact (zero cells): OR={odds_ratio:.3f}"

    chi2, p_value, dof, expected = stats.chi2_contingency(observed)
    return chi2, p_value, f"Chi-squared: χ²={chi2:.3f}, dof={dof}"

def run_t_tests(control, persona):
    """T-tests comparing drift distributions."""
    results = {}

    # Test 1: All drifts
    if control['drifts'] and persona['drifts']:
        t_stat, p_value = stats.ttest_ind(control['drifts'], persona['drifts'])
        results['all_drifts'] = {
            't_stat': t_stat,
            'p_value': p_value,
            'control_mean': np.mean(control['drifts']),
            'control_std': np.std(control['drifts']),
            'persona_mean': np.mean(persona['drifts']),
            'persona_std': np.std(persona['drifts']),
            'n_control': len(control['drifts']),
            'n_persona': len(persona['drifts'])
        }

    # Test 2: Max drifts per ship
    if control['max_drifts'] and persona['max_drifts']:
        t_stat, p_value = stats.ttest_ind(control['max_drifts'], persona['max_drifts'])
        results['max_drifts'] = {
            't_stat': t_stat,
            'p_value': p_value,
            'control_mean': np.mean(control['max_drifts']),
            'control_std': np.std(control['max_drifts']),
            'persona_mean': np.mean(persona['max_drifts']),
            'persona_std': np.std(persona['max_drifts']),
            'n_control': len(control['max_drifts']),
            'n_persona': len(persona['max_drifts'])
        }

    # Test 3: Mean drifts per ship
    if control['mean_drifts'] and persona['mean_drifts']:
        t_stat, p_value = stats.ttest_ind(control['mean_drifts'], persona['mean_drifts'])
        results['mean_drifts'] = {
            't_stat': t_stat,
            'p_value': p_value,
            'control_mean': np.mean(control['mean_drifts']),
            'control_std': np.std(control['mean_drifts']),
            'persona_mean': np.mean(persona['mean_drifts']),
            'persona_std': np.std(persona['mean_drifts']),
            'n_control': len(control['mean_drifts']),
            'n_persona': len(persona['mean_drifts'])
        }

    return results

def run_mann_whitney(control, persona):
    """Mann-Whitney U test (non-parametric alternative to t-test)."""
    results = {}

    if control['drifts'] and persona['drifts']:
        stat, p_value = stats.mannwhitneyu(control['drifts'], persona['drifts'], alternative='two-sided')
        results['all_drifts'] = {'U_stat': stat, 'p_value': p_value}

    if control['max_drifts'] and persona['max_drifts']:
        stat, p_value = stats.mannwhitneyu(control['max_drifts'], persona['max_drifts'], alternative='two-sided')
        results['max_drifts'] = {'U_stat': stat, 'p_value': p_value}

    return results

def run_levene_test(control, persona):
    """Levene's test for equality of variances."""
    results = {}

    if control['drifts'] and persona['drifts']:
        stat, p_value = stats.levene(control['drifts'], persona['drifts'])
        results['variance_equality'] = {
            'W_stat': stat,
            'p_value': p_value,
            'control_var': np.var(control['drifts']),
            'persona_var': np.var(persona['drifts'])
        }

    return results

def main():
    print("=" * 70)
    print("RUN 011: CONTROL vs PERSONA STATISTICAL ANALYSIS")
    print("=" * 70)
    print()

    # Load data
    data = load_data()
    control, persona = extract_fleet_stats(data)

    # Basic counts
    print("FLEET SUMMARY")
    print("-" * 40)
    print(f"Control Fleet: {len(control['ships'])} ships")
    print(f"  STABLE:   {control['stable_count']}")
    print(f"  VOLATILE: {control['volatile_count']}")
    print(f"  Total drift measurements: {len(control['drifts'])}")
    print()
    print(f"Persona Fleet: {len(persona['ships'])} ships")
    print(f"  STABLE:   {persona['stable_count']}")
    print(f"  VOLATILE: {persona['volatile_count']}")
    print(f"  Total drift measurements: {len(persona['drifts'])}")
    print()

    # Chi-squared test
    print("=" * 70)
    print("TEST 1: CHI-SQUARED (STABLE/VOLATILE Independence)")
    print("-" * 40)
    chi2, p_chi, chi_note = run_chi_squared(control, persona)
    print(f"Contingency Table:")
    print(f"                 STABLE    VOLATILE")
    print(f"  Control:       {control['stable_count']:6}    {control['volatile_count']:6}")
    print(f"  Persona:       {persona['stable_count']:6}    {persona['volatile_count']:6}")
    print()
    print(f"Result: {chi_note}")
    print(f"p-value: {p_chi:.6f}" if p_chi else "p-value: N/A")
    if p_chi and p_chi < 0.05:
        print(">>> SIGNIFICANT at alpha=0.05 - Fleet type affects stability outcome!")
    elif p_chi:
        print(">>> NOT SIGNIFICANT at alpha=0.05 - No evidence fleet type affects outcome")
    print()

    # T-tests
    print("=" * 70)
    print("TEST 2: T-TESTS (Mean Drift Comparison)")
    print("-" * 40)
    t_results = run_t_tests(control, persona)

    for test_name, result in t_results.items():
        print(f"\n{test_name.upper().replace('_', ' ')}:")
        print(f"  Control: mean={result['control_mean']:.4f} +/- {result['control_std']:.4f} (n={result['n_control']})")
        print(f"  Persona: mean={result['persona_mean']:.4f} +/- {result['persona_std']:.4f} (n={result['n_persona']})")
        print(f"  t-statistic: {result['t_stat']:.4f}")
        print(f"  p-value: {result['p_value']:.6f}")
        diff = result['control_mean'] - result['persona_mean']
        pct = (diff / result['control_mean'] * 100) if result['control_mean'] != 0 else 0
        direction = "lower" if diff > 0 else "higher"
        print(f"  Difference: Persona is {abs(pct):.1f}% {direction} than Control")
        if result['p_value'] < 0.05:
            print(f"  >>> SIGNIFICANT at alpha=0.05")
        else:
            print(f"  >>> NOT SIGNIFICANT at alpha=0.05")

    # Mann-Whitney (non-parametric)
    print()
    print("=" * 70)
    print("TEST 3: MANN-WHITNEY U (Non-parametric)")
    print("-" * 40)
    mw_results = run_mann_whitney(control, persona)
    for test_name, result in mw_results.items():
        print(f"{test_name}: U={result['U_stat']:.1f}, p={result['p_value']:.6f}")
        if result['p_value'] < 0.05:
            print(f"  >>> SIGNIFICANT at alpha=0.05")

    # Levene's test (variance equality)
    print()
    print("=" * 70)
    print("TEST 4: LEVENE'S TEST (Variance Equality)")
    print("-" * 40)
    levene_results = run_levene_test(control, persona)
    if 'variance_equality' in levene_results:
        r = levene_results['variance_equality']
        print(f"Control variance: {r['control_var']:.4f}")
        print(f"Persona variance: {r['persona_var']:.4f}")
        print(f"W-statistic: {r['W_stat']:.4f}")
        print(f"p-value: {r['p_value']:.6f}")
        if r['p_value'] < 0.05:
            tight = "Persona" if r['persona_var'] < r['control_var'] else "Control"
            print(f">>> SIGNIFICANT - {tight} has tighter clustering!")
        else:
            print(">>> NOT SIGNIFICANT - Variances are similar")

    # Effect size (Cohen's d)
    print()
    print("=" * 70)
    print("EFFECT SIZE: COHEN'S d")
    print("-" * 40)
    if t_results.get('max_drifts'):
        r = t_results['max_drifts']
        pooled_std = np.sqrt((r['control_std']**2 + r['persona_std']**2) / 2)
        cohens_d = (r['control_mean'] - r['persona_mean']) / pooled_std if pooled_std > 0 else 0
        print(f"Max Drift Cohen's d: {cohens_d:.3f}")
        if abs(cohens_d) < 0.2:
            print("  Interpretation: Negligible effect")
        elif abs(cohens_d) < 0.5:
            print("  Interpretation: Small effect")
        elif abs(cohens_d) < 0.8:
            print("  Interpretation: Medium effect")
        else:
            print("  Interpretation: Large effect")

    # Summary verdict
    print()
    print("=" * 70)
    print("VERDICT")
    print("=" * 70)

    significant_tests = []
    if p_chi and p_chi < 0.05:
        significant_tests.append("Chi-squared (STABLE/VOLATILE)")
    for name, r in t_results.items():
        if r['p_value'] < 0.05:
            significant_tests.append(f"T-test ({name})")
    for name, r in mw_results.items():
        if r['p_value'] < 0.05:
            significant_tests.append(f"Mann-Whitney ({name})")
    if levene_results.get('variance_equality', {}).get('p_value', 1) < 0.05:
        significant_tests.append("Levene (variance)")

    if significant_tests:
        print(f"\nSignificant results ({len(significant_tests)} tests):")
        for t in significant_tests:
            print(f"  ✓ {t}")
        print("\n>>> EVIDENCE SUPPORTS: Persona architecture produces")
        print("    measurably different drift behavior than control.")
    else:
        print("\nNo statistically significant differences found.")
        print("\n>>> CONCLUSION: Cannot reject null hypothesis.")
        print("    Persona and Control fleets show similar drift patterns.")

    print()
    print("=" * 70)

if __name__ == "__main__":
    main()
