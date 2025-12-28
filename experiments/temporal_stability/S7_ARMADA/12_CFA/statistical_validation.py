#!/usr/bin/env python3
"""
Statistical Validation Suite for Cross-Platform Drift Analysis
===============================================================
SPEC: 0_docs/specs/5_METHODOLOGY_DOMAINS.md

Purpose: Validate that observed drift patterns are signal, not noise.
Provides: Bootstrap CIs, permutation tests, effect sizes, and variance analysis.

METHODOLOGY:
    Drift = cosine distance in embedding space (per Run 023d)
    Event Horizon = 0.80 (P95 = 0.806, mean + 2σ = 0.83)

Usage:
    py statistical_validation.py                    # Run all tests
    py statistical_validation.py --test bootstrap   # Run specific test
    py statistical_validation.py --report           # Generate markdown report
"""

import sys
import json
import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
import random
import math
from datetime import datetime

# Path setup
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = ARMADA_DIR / "0_results" / "runs"
REPORT_PATH = SCRIPT_DIR / "STATISTICAL_VALIDATION_REPORT.md"
CALIBRATION_LIB = ARMADA_DIR / "1_CALIBRATION" / "lib"

sys.path.insert(0, str(CALIBRATION_LIB))

# Import canonical drift calculator for methodology constants
try:
    from drift_calculator import (
        EVENT_HORIZON,
        THRESHOLD_WARNING,
        THRESHOLD_CATASTROPHIC,
        classify_zone
    )
    _has_drift_calculator = True
except ImportError:
    # Fallback constants if import fails
    EVENT_HORIZON = 0.80
    THRESHOLD_WARNING = 0.60
    THRESHOLD_CATASTROPHIC = 1.20
    _has_drift_calculator = False
    print("[!] Could not import drift_calculator - using fallback constants")

# Threshold zones for classification
THRESHOLD_ZONES = {
    "SAFE": (0.0, 0.30),
    "WARNING": (0.30, 0.50),
    "CRITICAL": (0.50, 0.80),
    "CATASTROPHIC": (1.00, float('inf'))
}


@dataclass
class OobleckData:
    """Data from a single Oobleck Effect measurement."""
    platform: str
    prosecutor_peak: float
    defense_peak: float
    ratio: float
    peak_drift: float
    timestamp: str


@dataclass
class InherentData:
    """Data from a single Induced vs Inherent measurement."""
    platform: str
    control_bf: float
    treatment_bf: float
    inherent_ratio: float
    timestamp: str


def load_run_020_data() -> List[OobleckData]:
    """Load all Run 020 (Tribunal) data for Oobleck analysis."""
    results = []

    # Try multiple file patterns for compatibility
    patterns = [
        "S7_run_020_v8_*.json",
        "S7_run_020A_*.json",
        "S7_run_020a_*.json"
    ]

    for pattern in patterns:
        for f in RESULTS_DIR.glob(pattern):
            try:
                with open(f, 'r', encoding='utf-8') as fp:
                    data = json.load(fp)

                # Skip empty runs
                if not data.get('results') or not data['results'][0].get('drift_sequence'):
                    continue

                result = data['results'][0]
                phase = result.get('phase_markers', {})

                # Determine platform from witness_provider
                provider = data.get('witness_provider', 'unknown')
                if provider == 'google':
                    platform = 'Gemini'
                elif provider == 'xai':
                    platform = 'Grok'
                elif provider == 'openai':
                    platform = 'GPT'
                else:
                    platform = 'Claude'

                prosecutor_peak = phase.get('prosecutor_peak', 0.0)
                defense_peak = phase.get('defense_peak', 0.0)

                if prosecutor_peak > 0:
                    ratio = defense_peak / prosecutor_peak
                else:
                    ratio = 0.0

                results.append(OobleckData(
                    platform=platform,
                    prosecutor_peak=prosecutor_peak,
                    defense_peak=defense_peak,
                    ratio=ratio,
                    peak_drift=result.get('peak_drift', 0.0),
                    timestamp=data.get('timestamp', '')
                ))
            except Exception as e:
                print(f"Warning: Could not load {f}: {e}")

    return results


def load_run_020b_data() -> List[InherentData]:
    """Load all Run 020B (Induced vs Inherent) data."""
    results = []

    # Try multiple file patterns for compatibility
    patterns = [
        "S7_run_020b_*.json",
        "S7_run_020B_*.json"
    ]

    for pattern in patterns:
        for f in RESULTS_DIR.glob(pattern):
            try:
                with open(f, 'r', encoding='utf-8') as fp:
                    data = json.load(fp)

                # Get summary data
                summary = data.get('summary', {})
                control_bf = summary.get('control_avg_drift', 0.0)
                treatment_bf = summary.get('treatment_avg_drift', 0.0)

                if treatment_bf > 0:
                    inherent_ratio = control_bf / treatment_bf
                else:
                    inherent_ratio = 0.0

                # Determine platform from provider
                provider = data.get('provider', data.get('witness_provider', 'unknown'))
                if provider == 'together':
                    platform = 'Llama'
                elif provider == 'google':
                    platform = 'Gemini'
                elif provider == 'xai':
                    platform = 'Grok'
                elif provider == 'openai':
                    platform = 'GPT'
                else:
                    platform = 'Claude'

                results.append(InherentData(
                    platform=platform,
                    control_bf=control_bf,
                    treatment_bf=treatment_bf,
                    inherent_ratio=inherent_ratio,
                    timestamp=data.get('timestamp', '')
                ))
            except Exception as e:
                print(f"Warning: Could not load {f}: {e}")

    return results


def bootstrap_ci(values: List[float], n_iterations: int = 10000,
                 confidence: float = 0.95) -> Tuple[float, float, float]:
    """
    Calculate bootstrap confidence interval for a list of values.

    Returns: (mean, lower_bound, upper_bound)
    """
    if not values:
        return (0.0, 0.0, 0.0)

    if len(values) == 1:
        return (values[0], values[0], values[0])

    means = []
    n = len(values)

    for _ in range(n_iterations):
        sample = [random.choice(values) for _ in range(n)]
        means.append(sum(sample) / len(sample))

    means.sort()

    alpha = (1 - confidence) / 2
    lower_idx = int(alpha * n_iterations)
    upper_idx = int((1 - alpha) * n_iterations)

    return (
        sum(values) / len(values),
        means[lower_idx],
        means[upper_idx]
    )


def permutation_test(group1: List[float], group2: List[float],
                     n_iterations: int = 10000) -> float:
    """
    Permutation test for difference between two groups.

    Returns: p-value (probability of observing difference by chance)
    """
    if not group1 or not group2:
        return 1.0

    observed_diff = abs(sum(group1)/len(group1) - sum(group2)/len(group2))

    combined = group1 + group2
    n1 = len(group1)

    extreme_count = 0
    for _ in range(n_iterations):
        random.shuffle(combined)
        perm_group1 = combined[:n1]
        perm_group2 = combined[n1:]
        perm_diff = abs(sum(perm_group1)/len(perm_group1) - sum(perm_group2)/len(perm_group2))

        if perm_diff >= observed_diff:
            extreme_count += 1

    return extreme_count / n_iterations


def cohens_d(group1: List[float], group2: List[float]) -> float:
    """
    Calculate Cohen's d effect size between two groups.

    Interpretation:
    - |d| < 0.2: negligible
    - 0.2 ≤ |d| < 0.5: small
    - 0.5 ≤ |d| < 0.8: medium
    - |d| ≥ 0.8: large
    """
    if not group1 or not group2:
        return 0.0

    mean1 = sum(group1) / len(group1)
    mean2 = sum(group2) / len(group2)

    var1 = sum((x - mean1)**2 for x in group1) / len(group1)
    var2 = sum((x - mean2)**2 for x in group2) / len(group2)

    pooled_std = math.sqrt((var1 + var2) / 2)

    if pooled_std == 0:
        return 0.0

    return (mean1 - mean2) / pooled_std


def analyze_oobleck_effect(data: List[OobleckData]) -> Dict:
    """Analyze Oobleck Effect across platforms."""
    results = {
        'by_platform': {},
        'overall': {}
    }

    # Group by platform
    by_platform = {}
    for d in data:
        if d.platform not in by_platform:
            by_platform[d.platform] = []
        by_platform[d.platform].append(d)

    # Analyze each platform
    all_ratios = []
    for platform, items in by_platform.items():
        ratios = [d.ratio for d in items]
        all_ratios.extend(ratios)

        mean, lower, upper = bootstrap_ci(ratios)

        # Also calculate Cohen's d comparing prosecutor vs defense peaks
        prosecutor_peaks = [d.prosecutor_peak for d in items]
        defense_peaks = [d.defense_peak for d in items]
        effect_size = cohens_d(defense_peaks, prosecutor_peaks)

        results['by_platform'][platform] = {
            'n': len(items),
            'mean_ratio': mean,
            'ci_lower': lower,
            'ci_upper': upper,
            'cohens_d': effect_size,
            'validated': mean > 1.0 and lower > 0.9,  # Lower bound close to 1.0
            'ratios': ratios
        }

    # Overall analysis
    if all_ratios:
        mean, lower, upper = bootstrap_ci(all_ratios)
        results['overall'] = {
            'n': len(all_ratios),
            'mean_ratio': mean,
            'ci_lower': lower,
            'ci_upper': upper,
            'validated': mean > 1.0
        }

    return results


def analyze_inherent_drift(data: List[InherentData]) -> Dict:
    """Analyze Induced vs Inherent drift patterns."""
    results = {
        'by_platform': {},
        'overall': {}
    }

    # Group by platform
    by_platform = {}
    for d in data:
        if d.platform not in by_platform:
            by_platform[d.platform] = []
        by_platform[d.platform].append(d)

    all_ratios = []
    all_controls = []
    all_treatments = []

    for platform, items in by_platform.items():
        ratios = [d.inherent_ratio for d in items]
        controls = [d.control_bf for d in items]
        treatments = [d.treatment_bf for d in items]

        all_ratios.extend(ratios)
        all_controls.extend(controls)
        all_treatments.extend(treatments)

        mean, lower, upper = bootstrap_ci(ratios)

        # Permutation test: is control significantly different from treatment?
        p_value = permutation_test(controls, treatments)

        # Effect size
        d = cohens_d(controls, treatments)

        results['by_platform'][platform] = {
            'n': len(items),
            'mean_inherent_ratio': mean,
            'ci_lower': lower,
            'ci_upper': upper,
            'p_value': p_value,
            'cohens_d': d,
            'validated': mean > 0.5  # More than 50% inherent
        }

    # Overall analysis
    if all_ratios:
        mean, lower, upper = bootstrap_ci(all_ratios)
        p_value = permutation_test(all_controls, all_treatments)
        d = cohens_d(all_controls, all_treatments)

        results['overall'] = {
            'n': len(all_ratios),
            'mean_inherent_ratio': mean,
            'ci_lower': lower,
            'ci_upper': upper,
            'p_value': p_value,
            'cohens_d': d,
            'validated': mean > 0.5
        }

    return results


def generate_report(oobleck: Dict, inherent: Dict) -> str:
    """Generate markdown report of statistical validation."""
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    # Calculate totals for status
    oobleck_n = sum(s['n'] for s in oobleck.get('by_platform', {}).values())
    inherent_n = sum(s['n'] for s in inherent.get('by_platform', {}).values())
    total_n = oobleck_n + inherent_n

    report = f"""# Statistical Validation Report

**Generated:** {timestamp}
**Methodology:** Cosine distance in embedding space (per Run 023d)
**Last Updated:** {datetime.now().strftime("%Y-%m-%d")}

---

## Executive Summary

### Oobleck Effect (Defense > Prosecutor)

> The Oobleck Effect measures whether supportive probing (Defense) enables more identity exploration
> than adversarial probing (Prosecutor). Ratio > 1.0 indicates Defense produces higher drift.

| Platform | N | Mean Ratio | 95% CI | Cohen's d | Validated |
|----------|---|------------|--------|-----------|-----------|
"""

    for platform, stats in oobleck.get('by_platform', {}).items():
        validated = "✅" if stats['validated'] else "⚠️"
        cohens = stats.get('cohens_d', 0.0)
        report += f"| {platform} | {stats['n']} | {stats['mean_ratio']:.3f} | [{stats['ci_lower']:.3f}, {stats['ci_upper']:.3f}] | {cohens:.3f} | {validated} |\n"

    if oobleck.get('overall'):
        overall = oobleck['overall']
        validated = "✅" if overall['validated'] else "⚠️"
        report += f"| **Overall** | {overall['n']} | {overall['mean_ratio']:.3f} | [{overall['ci_lower']:.3f}, {overall['ci_upper']:.3f}] | — | {validated} |\n"

    report += """
### Inherent Drift Ratio (Control ÷ Treatment)

> Tests whether drift is INHERENT to conversation or INDUCED by measurement.
> Ratio near 1.0 = drift is inherent; Ratio near 0.0 = drift is induced.

| Platform | N | Mean Ratio | 95% CI | p-value | Cohen's d | Interpretation |
|----------|---|------------|--------|---------|-----------|----------------|
"""

    for platform, stats in inherent.get('by_platform', {}).items():
        validated = "✅" if stats['validated'] else "⚠️"
        report += f"| {platform} | {stats['n']} | {stats['mean_inherent_ratio']:.1%} | [{stats['ci_lower']:.1%}, {stats['ci_upper']:.1%}] | {stats['p_value']:.4f} | {stats['cohens_d']:.3f} | {validated} |\n"

    if inherent.get('overall'):
        overall = inherent['overall']
        validated = "✅" if overall['validated'] else "⚠️"
        report += f"| **Overall** | {overall['n']} | {overall['mean_inherent_ratio']:.1%} | [{overall['ci_lower']:.1%}, {overall['ci_upper']:.1%}] | {overall['p_value']:.4f} | {overall['cohens_d']:.3f} | {validated} |\n"

    report += f"""
---

## Methodology

### Drift Calculation

```text
drift = 1 - cosine_similarity(response_embedding, baseline_embedding)
```

- **Embedding model:** text-embedding-3-large (3072 dimensions)
- **Canonical implementation:** `1_CALIBRATION/lib/drift_calculator.py`

### Threshold Zones (Cosine Distance)

| Zone | Range | Interpretation |
|------|-------|----------------|
| **SAFE** | < 0.30 | Normal conversational variation |
| **WARNING** | 0.30 – 0.50 | "I notice I'm adapting" |
| **CRITICAL** | 0.50 – 0.80 | Approaching Event Horizon |
| **CATASTROPHIC** | > 1.00 | Identity coherence compromised |

**Event Horizon:** {EVENT_HORIZON} (P95 = 0.806, mean + 2σ = 0.83 per Run 023d)

### Statistical Methods

| Method | Application |
|--------|-------------|
| **Bootstrap CI** | 95% confidence intervals (10,000 iterations) |
| **Permutation test** | p-values for group comparisons (10,000 iterations) |
| **Cohen's d** | Effect size magnitude |

---

## Interpretation Guide

### Effect Size (Cohen's d)

| Magnitude | Interpretation |
|-----------|----------------|
| \\|d\\| < 0.2 | Negligible effect |
| 0.2 ≤ \\|d\\| < 0.5 | Small effect |
| 0.5 ≤ \\|d\\| < 0.8 | Medium effect |
| \\|d\\| ≥ 0.8 | Large effect |

### Confidence Intervals

- **Oobleck Effect:** If 95% CI excludes 1.0, effect is statistically significant
- **Inherent Ratio:** If 95% CI excludes 0.5, drift is predominantly inherent (>0.5) or induced (<0.5)

### Validation Criteria

| Metric | Required N | Current N | Status |
|--------|------------|-----------|--------|
| Oobleck per platform | ≥ 3 | {oobleck_n} | {"✅" if oobleck_n >= 9 else "⏳"} |
| Inherent per platform | ≥ 3 | {inherent_n} | {"✅" if inherent_n >= 9 else "⏳"} |
| Cross-platform total | ≥ 12 | {total_n} | {"✅" if total_n >= 12 else "⏳"} |

---

## Data Sources

| Experiment | Location | Metrics Extracted |
|------------|----------|-------------------|
| Run 020A (Tribunal) | `11_CONTEXT_DAMPING/results/S7_run_020A_CURRENT.json` | Prosecutor/Defense drift |
| Run 020B (Control/Treatment) | `11_CONTEXT_DAMPING/results/S7_run_020B_CURRENT.json` | Inherent ratio |
| CFA Trinity | `12_CFA/results/` | Cross-auditor convergence |

---

## Related Documentation

| Document | Purpose |
|----------|---------|
| [5_METHODOLOGY_DOMAINS.md](../0_docs/specs/5_METHODOLOGY_DOMAINS.md) | Methodology specification |
| [drift_calculator.py](../1_CALIBRATION/lib/drift_calculator.py) | Canonical drift implementation |
| [TESTABLE_PREDICTIONS_MATRIX.md](../../../docs/maps/TESTABLE_PREDICTIONS_MATRIX.md) | Predictions registry |

---

*"Statistics don't prove. They quantify uncertainty."*

— VALIS Network
"""

    return report


def main():
    parser = argparse.ArgumentParser(description="Statistical validation for cross-platform drift")
    parser.add_argument('--test', choices=['bootstrap', 'permutation', 'effect', 'all'],
                        default='all', help='Which test to run')
    parser.add_argument('--report', action='store_true', help='Generate markdown report')
    args = parser.parse_args()

    print("=" * 60)
    print("STATISTICAL VALIDATION SUITE")
    print("=" * 60)
    print(f"Methodology: Cosine distance (Event Horizon = {EVENT_HORIZON})")
    if _has_drift_calculator:
        print("[+] Using canonical drift_calculator constants")
    else:
        print("[!] Using fallback constants")

    # Load data
    print("\nLoading Run 020 (Oobleck) data...")
    oobleck_data = load_run_020_data()
    print(f"  Found {len(oobleck_data)} Oobleck measurements")

    print("\nLoading Run 020B (Inherent) data...")
    inherent_data = load_run_020b_data()
    print(f"  Found {len(inherent_data)} Inherent measurements")

    # Analyze
    print("\n" + "-" * 60)
    print("OOBLECK EFFECT ANALYSIS")
    print("-" * 60)

    oobleck_results = analyze_oobleck_effect(oobleck_data)

    for platform, stats in oobleck_results.get('by_platform', {}).items():
        status = "[VALIDATED]" if stats['validated'] else "[Needs more data]"
        print(f"\n{platform}:")
        print(f"  N = {stats['n']}")
        print(f"  Mean Oobleck ratio = {stats['mean_ratio']:.3f}")
        print(f"  95% CI = [{stats['ci_lower']:.3f}, {stats['ci_upper']:.3f}]")
        print(f"  Cohen's d = {stats.get('cohens_d', 0):.3f}")
        print(f"  Status: {status}")

    print("\n" + "-" * 60)
    print("INHERENT DRIFT ANALYSIS")
    print("-" * 60)

    inherent_results = analyze_inherent_drift(inherent_data)

    for platform, stats in inherent_results.get('by_platform', {}).items():
        status = "[VALIDATED]" if stats['validated'] else "[Needs more data]"
        print(f"\n{platform}:")
        print(f"  N = {stats['n']}")
        print(f"  Mean inherent ratio = {stats['mean_inherent_ratio']:.1%}")
        print(f"  95% CI = [{stats['ci_lower']:.1%}, {stats['ci_upper']:.1%}]")
        print(f"  p-value = {stats['p_value']:.4f}")
        print(f"  Cohen's d = {stats['cohens_d']:.3f}")
        print(f"  Status: {status}")

    # Generate report
    if args.report:
        print("\n" + "-" * 60)
        print("GENERATING REPORT")
        print("-" * 60)

        report = generate_report(oobleck_results, inherent_results)

        with open(REPORT_PATH, 'w', encoding='utf-8') as f:
            f.write(report)

        print(f"\nReport saved to: {REPORT_PATH}")

    print("\n" + "=" * 60)
    print("VALIDATION COMPLETE")
    print("=" * 60)


if __name__ == "__main__":
    main()
