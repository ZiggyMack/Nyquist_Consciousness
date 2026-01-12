#!/usr/bin/env python3
"""
S8_gamma_extraction.py - Identity Gravity (gamma) Measurement from Run 023d Data

IRON CLAD PATTERN COMPLIANT
===========================
This script extracts empirical gamma (γ) values from Run 023d extended settling data.

THEORETICAL BASIS (from S8_IDENTITY_GRAVITY_SPEC.md):
- G_I = -γ · ∇F(I_t)  → Identity gravitational force
- dI/dt = -γ · ∇F(I)   → Drift decay governed by gamma
- 1 Zig = pull required to reduce drift by 0.01 PFI

MEASUREMENT APPROACH:
- Use recovery phase drift trajectories (probes 4-23)
- Fit exponential decay: drift(t) = d_peak * exp(-γ * t) + d_settled
- Extract γ per experiment, aggregate by model/provider

OUTPUT:
- S8_gamma_analysis_CURRENT.json  → Full results
- Console summary of γ by provider
- Ready for S8 visualization pipeline

Author: Claude + Nyquist
Date: 2026-01-11
"""

import json
import os
import sys
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Optional, Tuple
import math
from collections import defaultdict

# ============================================================================
# CONFIGURATION
# ============================================================================

RESULTS_DIR = Path(__file__).parent / "results"
INPUT_FILE = RESULTS_DIR / "S7_run_023d_CURRENT.json"
OUTPUT_FILE = RESULTS_DIR / "S8_gamma_analysis_CURRENT.json"

# Minimum probes needed for reliable gamma fit
MIN_RECOVERY_PROBES = 5

# ============================================================================
# DATA STRUCTURES
# ============================================================================

@dataclass
class GammaResult:
    """Result of gamma extraction for a single experiment."""
    model: str
    provider: str
    iteration: int

    # Raw trajectory data
    peak_drift: float           # Maximum drift after perturbation
    settled_drift: float        # Final drift value
    settling_time: int          # Probes to settle (tau_s)

    # Gamma extraction
    gamma_raw: float            # Raw exponential fit gamma
    gamma_zigs: float           # Gamma in Zigs (normalized)
    fit_r_squared: float        # Quality of exponential fit

    # Recovery characteristics
    recovery_magnitude: float   # peak_drift - settled_drift
    recovery_rate: float        # recovery_magnitude / settling_time
    half_life_probes: float     # Probes to reach 50% recovery

    # Force curve type (from S8 spec)
    force_curve_type: str       # I, II, III, IV, or 0

    # Metadata
    naturally_settled: bool
    is_monotonic: bool
    ringback_count: int
    timestamp: str


@dataclass
class ProviderGammaStats:
    """Aggregated gamma statistics per provider."""
    provider: str
    n_experiments: int

    # Gamma statistics
    gamma_mean: float
    gamma_std: float
    gamma_median: float
    gamma_min: float
    gamma_max: float

    # Recovery statistics
    avg_recovery_magnitude: float
    avg_settling_time: float
    avg_half_life: float

    # Force curve distribution
    force_curve_distribution: Dict[str, int]

    # Quality metrics
    avg_fit_r_squared: float
    pct_naturally_settled: float


# ============================================================================
# GAMMA EXTRACTION FUNCTIONS
# ============================================================================

def extract_recovery_trajectory(probe_sequence: List[dict]) -> Tuple[List[float], List[int]]:
    """Extract drift values and indices for recovery probes only."""
    drifts = []
    indices = []

    for probe in probe_sequence:
        if probe['probe_type'] == 'recovery':
            drifts.append(probe['drift'])
            indices.append(probe['probe_index'])

    return drifts, indices


def fit_exponential_decay(drifts: List[float], indices: List[int], settled_drift: float) -> Tuple[float, float]:
    """
    Fit exponential decay: drift(t) = A * exp(-gamma * t) + settled_drift

    Returns:
        gamma: decay constant
        r_squared: goodness of fit
    """
    if len(drifts) < MIN_RECOVERY_PROBES:
        return 0.0, 0.0

    # Shift drifts relative to settled value
    shifted = [max(d - settled_drift, 0.001) for d in drifts]  # Avoid log(0)

    # Linear regression on log(shifted) vs index to get gamma
    # log(drift - settled) = log(A) - gamma * t
    n = len(shifted)
    t_values = [i - indices[0] for i in indices]  # Normalize time to start at 0

    log_shifted = [math.log(s) if s > 0 else -10 for s in shifted]

    # Calculate means
    t_mean = sum(t_values) / n
    log_mean = sum(log_shifted) / n

    # Calculate slope (negative gamma) and intercept
    numerator = sum((t - t_mean) * (ls - log_mean) for t, ls in zip(t_values, log_shifted))
    denominator = sum((t - t_mean) ** 2 for t in t_values)

    if denominator == 0:
        return 0.0, 0.0

    slope = numerator / denominator  # This is -gamma
    gamma = -slope

    # Calculate R-squared
    intercept = log_mean - slope * t_mean
    predicted = [intercept + slope * t for t in t_values]
    ss_res = sum((actual - pred) ** 2 for actual, pred in zip(log_shifted, predicted))
    ss_tot = sum((ls - log_mean) ** 2 for ls in log_shifted)

    r_squared = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0.0

    return max(gamma, 0.0), max(r_squared, 0.0)  # Gamma should be positive


def calculate_half_life(gamma: float) -> float:
    """Calculate half-life in probes from gamma."""
    if gamma <= 0:
        return float('inf')
    return math.log(2) / gamma


def classify_force_curve(gamma: float, is_monotonic: bool, ringback_count: int, naturally_settled: bool) -> str:
    """
    Classify force curve type per S8 spec.

    Types:
    - Type I: Strong gravity, fast monotonic recovery
    - Type II: Moderate gravity, some oscillation
    - Type III: Weak gravity, significant ringback
    - Type IV: Very weak gravity, did not settle
    - Type 0: No recovery attempt or failed
    """
    if gamma <= 0 or not naturally_settled:
        if ringback_count > 10:
            return "IV"  # Very weak, chaotic
        return "0"  # No meaningful recovery

    if gamma >= 0.3 and is_monotonic:
        return "I"   # Strong, monotonic
    elif gamma >= 0.15 and ringback_count <= 3:
        return "II"  # Moderate, controlled oscillation
    elif gamma >= 0.05:
        return "III" # Weak, significant ringback
    else:
        return "IV"  # Very weak


def extract_gamma_from_experiment(result: dict) -> GammaResult:
    """Extract gamma and related metrics from a single experiment result."""

    # Get recovery trajectory
    drifts, indices = extract_recovery_trajectory(result['probe_sequence'])

    # Fit exponential decay
    gamma_raw, r_squared = fit_exponential_decay(
        drifts, indices, result['settled_drift']
    )

    # Convert to Zigs (1 Zig = 0.01 PFI reduction)
    # gamma_raw is in units of (drift reduction per probe)
    # To convert to Zigs: gamma_zigs = gamma_raw * 100 (since 1 Zig = 0.01)
    gamma_zigs = gamma_raw * 100

    # Calculate recovery characteristics
    recovery_magnitude = result['peak_drift'] - result['settled_drift']
    recovery_rate = recovery_magnitude / max(result['settling_time'], 1)
    half_life = calculate_half_life(gamma_raw)

    # Classify force curve
    force_curve = classify_force_curve(
        gamma_raw,
        result['is_monotonic'],
        result['ringback_count'],
        result['naturally_settled']
    )

    return GammaResult(
        model=result['model'],
        provider=result['provider'],
        iteration=result['iteration'],
        peak_drift=result['peak_drift'],
        settled_drift=result['settled_drift'],
        settling_time=result['settling_time'],
        gamma_raw=gamma_raw,
        gamma_zigs=gamma_zigs,
        fit_r_squared=r_squared,
        recovery_magnitude=recovery_magnitude,
        recovery_rate=recovery_rate,
        half_life_probes=half_life,
        force_curve_type=force_curve,
        naturally_settled=result['naturally_settled'],
        is_monotonic=result['is_monotonic'],
        ringback_count=result['ringback_count'],
        timestamp=datetime.now().isoformat()
    )


def aggregate_by_provider(gamma_results: List[GammaResult]) -> Dict[str, ProviderGammaStats]:
    """Aggregate gamma results by provider."""

    by_provider = defaultdict(list)
    for result in gamma_results:
        by_provider[result.provider].append(result)

    stats = {}
    for provider, results in by_provider.items():
        gammas = [r.gamma_zigs for r in results if r.gamma_zigs > 0]

        if not gammas:
            continue

        # Force curve distribution
        fc_dist = defaultdict(int)
        for r in results:
            fc_dist[r.force_curve_type] += 1

        stats[provider] = ProviderGammaStats(
            provider=provider,
            n_experiments=len(results),
            gamma_mean=sum(gammas) / len(gammas),
            gamma_std=math.sqrt(sum((g - sum(gammas)/len(gammas))**2 for g in gammas) / len(gammas)) if len(gammas) > 1 else 0,
            gamma_median=sorted(gammas)[len(gammas)//2],
            gamma_min=min(gammas),
            gamma_max=max(gammas),
            avg_recovery_magnitude=sum(r.recovery_magnitude for r in results) / len(results),
            avg_settling_time=sum(r.settling_time for r in results) / len(results),
            avg_half_life=sum(r.half_life_probes for r in results if r.half_life_probes < float('inf')) / max(1, sum(1 for r in results if r.half_life_probes < float('inf'))),
            force_curve_distribution=dict(fc_dist),
            avg_fit_r_squared=sum(r.fit_r_squared for r in results) / len(results),
            pct_naturally_settled=sum(1 for r in results if r.naturally_settled) / len(results) * 100
        )

    return stats


def aggregate_by_model(gamma_results: List[GammaResult]) -> Dict[str, dict]:
    """Aggregate gamma results by model."""

    by_model = defaultdict(list)
    for result in gamma_results:
        by_model[result.model].append(result)

    stats = {}
    for model, results in by_model.items():
        gammas = [r.gamma_zigs for r in results if r.gamma_zigs > 0]

        if not gammas:
            continue

        stats[model] = {
            'model': model,
            'provider': results[0].provider,
            'n_experiments': len(results),
            'gamma_mean': sum(gammas) / len(gammas),
            'gamma_std': math.sqrt(sum((g - sum(gammas)/len(gammas))**2 for g in gammas) / len(gammas)) if len(gammas) > 1 else 0,
            'gamma_median': sorted(gammas)[len(gammas)//2],
            'pct_naturally_settled': sum(1 for r in results if r.naturally_settled) / len(results) * 100,
            'avg_half_life': sum(r.half_life_probes for r in results if r.half_life_probes < float('inf')) / max(1, sum(1 for r in results if r.half_life_probes < float('inf'))),
        }

    return stats


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 70)
    print("S8 IDENTITY GRAVITY - GAMMA EXTRACTION FROM RUN 023d")
    print("=" * 70)
    print()

    # Load Run 023d data
    print(f"Loading: {INPUT_FILE}")
    with open(INPUT_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    results = data['results']
    print(f"Loaded {len(results)} experiments")
    print()

    # Extract gamma from each experiment
    print("Extracting gamma values...")
    gamma_results = []
    for i, result in enumerate(results):
        gamma_result = extract_gamma_from_experiment(result)
        gamma_results.append(gamma_result)

        if (i + 1) % 100 == 0:
            print(f"  Processed {i + 1}/{len(results)}")

    print(f"Extracted gamma from {len(gamma_results)} experiments")
    print()

    # Aggregate by provider
    provider_stats = aggregate_by_provider(gamma_results)

    # Aggregate by model
    model_stats = aggregate_by_model(gamma_results)

    # Print summary
    print("=" * 70)
    print("GAMMA BY PROVIDER (in Zigs)")
    print("=" * 70)
    print()
    print(f"{'Provider':<12} {'N':>6} {'gamma_mean':>12} {'gamma_std':>10} {'% Settled':>10} {'Avg t_1/2':>10}")
    print("-" * 70)

    for provider in sorted(provider_stats.keys()):
        s = provider_stats[provider]
        print(f"{provider:<12} {s.n_experiments:>6} {s.gamma_mean:>12.2f} {s.gamma_std:>10.2f} {s.pct_naturally_settled:>9.1f}% {s.avg_half_life:>10.1f}")

    print()
    print("=" * 70)
    print("GAMMA BY MODEL (Top 10 by gamma)")
    print("=" * 70)
    print()

    sorted_models = sorted(model_stats.items(), key=lambda x: x[1]['gamma_mean'], reverse=True)[:10]
    print(f"{'Model':<45} {'gamma':>8} {'% Settled':>10}")
    print("-" * 70)
    for model, s in sorted_models:
        short_model = model[:42] + "..." if len(model) > 45 else model
        print(f"{short_model:<45} {s['gamma_mean']:>8.2f} {s['pct_naturally_settled']:>9.1f}%")

    print()
    print("=" * 70)
    print("FORCE CURVE TYPE DISTRIBUTION (Fleet-wide)")
    print("=" * 70)
    print()

    fc_total = defaultdict(int)
    for r in gamma_results:
        fc_total[r.force_curve_type] += 1

    for fc_type in ['I', 'II', 'III', 'IV', '0']:
        count = fc_total.get(fc_type, 0)
        pct = count / len(gamma_results) * 100
        bar = '#' * int(pct / 2)
        print(f"  Type {fc_type}: {count:>4} ({pct:>5.1f}%) {bar}")

    print()

    # Save results
    output_data = {
        'analysis_type': 'S8_gamma_extraction',
        'source_run': '023d',
        'source_file': str(INPUT_FILE),
        'timestamp': datetime.now().isoformat(),
        'total_experiments': len(gamma_results),
        'provider_stats': {k: asdict(v) for k, v in provider_stats.items()},
        'model_stats': model_stats,
        'individual_results': [asdict(r) for r in gamma_results],
        'fleet_force_curve_distribution': dict(fc_total),
        'methodology': {
            'description': 'Exponential decay fit on recovery phase drift trajectories',
            'equation': 'drift(t) = A * exp(-gamma * t) + settled_drift',
            'units': 'gamma in Zigs (1 Zig = 0.01 PFI reduction per probe)',
            'min_recovery_probes': MIN_RECOVERY_PROBES,
        }
    }

    print(f"Saving results to: {OUTPUT_FILE}")
    with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
        json.dump(output_data, f, indent=2)

    print()
    print("=" * 70)
    print("S8 GAMMA EXTRACTION COMPLETE")
    print("=" * 70)
    print()
    print("Key Findings:")

    # Find strongest and weakest gravity providers
    sorted_providers = sorted(provider_stats.items(), key=lambda x: x[1].gamma_mean, reverse=True)
    strongest = sorted_providers[0]
    weakest = sorted_providers[-1]

    print(f"  - Strongest gravity: {strongest[0]} (gamma = {strongest[1].gamma_mean:.2f} Zigs)")
    print(f"  - Weakest gravity:   {weakest[0]} (gamma = {weakest[1].gamma_mean:.2f} Zigs)")
    print(f"  - Gravity ratio:     {strongest[1].gamma_mean / weakest[1].gamma_mean:.2f}x")
    print()
    print(f"  - Type I (strong):   {fc_total.get('I', 0)} ({fc_total.get('I', 0)/len(gamma_results)*100:.1f}%)")
    print(f"  - Type II (moderate): {fc_total.get('II', 0)} ({fc_total.get('II', 0)/len(gamma_results)*100:.1f}%)")
    print(f"  - Type III (weak):   {fc_total.get('III', 0)} ({fc_total.get('III', 0)/len(gamma_results)*100:.1f}%)")
    print()
    print("Next: Run S8_gamma_visualization.py to generate force curve plots")


if __name__ == "__main__":
    main()
