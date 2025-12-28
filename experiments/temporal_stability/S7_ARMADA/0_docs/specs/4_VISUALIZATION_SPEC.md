# S7 ARMADA Visualization Specification

**Purpose:** Prevent recurring pitfalls when creating visualizations from experimental data. Consult this BEFORE creating any new visualization script.

**Last Updated:** December 27, 2025
**Lessons From:** Runs 023b-023e visualization debugging sessions

> **Methodology Note:** This spec uses Cosine methodology (Event Horizon = 0.80).
> See [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md) for methodology details.
> For fleet terminology (provider/model_family/ship), see [ARCHITECTURE_MATRIX.json](../../0_results/manifests/ARCHITECTURE_MATRIX.json).

---

## CRITICAL DATA STRUCTURE UNDERSTANDING

Before writing ANY visualization code, understand the data hierarchy:

```text
Result (per experiment)
├── provider: str           # anthropic, openai, google, xai, together
├── model: str              # Full model ID
├── peak_drift: float       # Maximum drift reached (result-level)
├── settled_drift: float    # Final settled drift (result-level)
├── baseline_drift: float   # Always 0 by definition (see pitfall #1)
├── settling_time: int      # Probes to settle
├── naturally_settled: bool # Whether model settled within window
├── overshoot_ratio: float  # peak/settled ratio
├── ringback_count: int     # Direction changes
└── probe_sequence: list    # Per-probe data
    └── Probe
        ├── probe_type: str     # baseline, step_input, recovery
        ├── drift: float        # Drift at THIS probe
        ├── response_text: str  # Raw response (NOT 'response')
        └── timestamp: str
```

---

## PITFALL #1: BASELINE DRIFT IS ZERO BY DEFINITION

### The Problem

Baseline drift is **always 0** because baseline probes ARE the reference point. Any visualization using `baseline_drift` for comparisons will produce floods of zeros that drown out real signal.

### Wrong Pattern (Produces 0s)

```python
# WRONG: Using baseline drift from individual probes
for probe in probes:
    if probe['probe_type'] == 'baseline':
        drift = probe['drift']  # This is ALWAYS 0 or near-0!
```

### Correct Pattern

```python
# RIGHT: Use result-level metrics for meaningful comparisons
peak_drift = result.get('peak_drift', 0)      # Maximum deviation
settled_drift = result.get('settled_drift', 0) # Final settled state
step_input_drift = None
for probe in probes:
    if probe['probe_type'] == 'step_input':
        step_input_drift = probe['drift']  # Perturbation response
        break
```

### When to Use What

| Metric | Use For | Source |
|--------|---------|--------|
| `peak_drift` | Maximum identity deviation | Result-level |
| `settled_drift` | Recovery quality, permanent change | Result-level |
| `step_input_drift` | Perturbation sensitivity | Probe where `probe_type == 'step_input'` |
| `baseline_drift` | **NEVER USE IN COMPARISONS** | Always 0 |

---

## PITFALL #2: INDIVIDUAL EXPERIMENTS VS MODEL-LEVEL AGGREGATES

### The Problem

When comparing within-provider vs cross-provider distances, using individual experiments creates many near-zero differences (same model, same day, similar responses). This floods the distribution with noise.

### Wrong Pattern (Too Many Near-Zeros)

```python
# WRONG: Compare all individual experiments
within_distances = []
for i in range(len(experiments)):
    for j in range(i+1, len(experiments)):
        if experiments[i]['provider'] == experiments[j]['provider']:
            diff = abs(experiments[i]['peak_drift'] - experiments[j]['peak_drift'])
            within_distances.append(diff)  # Many near-0 values!
```

### Correct Pattern (Model-Level Aggregates)

```python
# RIGHT: Compare MODEL MEANS, not individual experiments
from collections import defaultdict

# Step 1: Aggregate by model
model_drifts = defaultdict(list)
for r in results:
    key = (r['provider'], r['model'])
    model_drifts[key].append(r['peak_drift'])

# Step 2: Compute mean per model
model_means = {key: np.mean(drifts) for key, drifts in model_drifts.items()}

# Step 3: Compare models (not experiments)
within_distances = []
by_provider = defaultdict(list)
for (provider, model), mean_drift in model_means.items():
    by_provider[provider].append((model, mean_drift))

for provider, models in by_provider.items():
    for i in range(len(models)):
        for j in range(i+1, len(models)):
            diff = abs(models[i][1] - models[j][1])
            within_distances.append(diff)  # Meaningful differences!
```

### When to Aggregate

| Comparison Type | Aggregation Level |
|-----------------|-------------------|
| Within-provider identity differences | Model means |
| Cross-provider identity differences | Model means |
| Stability over time | Individual experiments (time series) |
| Per-probe trajectories | Individual probes |

---

## PITFALL #3: WRONG FIELD NAMES

### The Problem

Data structure field names changed between runs. Code that worked on old data may fail silently on new data.

### Common Mistakes

```python
# WRONG: Old field name
response = probe.get('response', '')  # Empty on new data!

# RIGHT: New field name
response = probe.get('response_text', '')  # Has content

# WRONG: Old probe type field
ptype = probe.get('type', '')  # May be empty

# RIGHT: Try both for compatibility
ptype = probe.get('probe_type', probe.get('type', 'unknown'))
```

### Field Name Reference

| Data | Old Field | New Field (Run 023d+) |
|------|-----------|----------------------|
| Response text | `response` | `response_text` |
| Probe type | `type` | `probe_type` |

### Defensive Pattern

```python
def get_probe_type(probe):
    """Get probe type with backward compatibility."""
    return probe.get('probe_type', probe.get('type', 'unknown'))

def get_response_text(probe):
    """Get response text with backward compatibility."""
    return probe.get('response_text', probe.get('response', ''))
```

---

## PITFALL #4: PROVIDER NAME MAPPING

### The Problem

Old visualization code used display names that don't match data.

### Wrong Pattern

```python
# WRONG: Old visualization code
provider_names = {'claude': 'CLAUDE', 'gpt': 'GPT', 'gemini': 'GEMINI'}
# Data says 'anthropic', not 'claude'!
```

### Correct Pattern

```python
# RIGHT: Map from actual data values
PROVIDER_COLORS = {
    'anthropic': '#E07B53',  # Data says 'anthropic'
    'openai': '#10A37F',     # Data says 'openai'
    'google': '#4285F4',     # Data says 'google'
    'xai': '#1DA1F2',        # Data says 'xai'
    'together': '#7C3AED',   # Data says 'together'
}

PROVIDER_DISPLAY = {
    'anthropic': 'Anthropic',
    'openai': 'OpenAI',
    'google': 'Google',
    'xai': 'xAI',
    'together': 'Together.ai',
}
```

---

## PITFALL #5: DARK MODE VS LIGHT MODE

### The Problem

Dark mode visualizations look professional in terminals but are hard to read in white papers and PDFs.

### Standard: Use LIGHT MODE for Publication

```python
# LIGHT MODE template
fig, ax = plt.subplots(figsize=(12, 8))
fig.patch.set_facecolor('white')
ax.set_facecolor('white')  # or '#f8f8f8' for subtle contrast

# Text colors
ax.set_xlabel('Label', fontsize=12, color='black')
ax.set_title('Title', fontsize=14, color='black', fontweight='bold')
ax.tick_params(colors='black')

# Grid and spines
ax.grid(True, alpha=0.3, color='#cccccc')
for spine in ax.spines.values():
    spine.set_color('#cccccc')

# Legend
legend = ax.legend(facecolor='white', edgecolor='#cccccc')
for text in legend.get_texts():
    text.set_color('black')
```

### Color Palette for Light Mode

```python
# Background colors
BACKGROUND_WHITE = 'white'
BACKGROUND_SUBTLE = '#f8f8f8'
BACKGROUND_PANEL = '#f5f5f5'

# Text colors
TEXT_PRIMARY = 'black'
TEXT_SECONDARY = '#333333'
TEXT_MUTED = '#666666'

# Grid/spine colors
GRID_COLOR = '#cccccc'
SPINE_COLOR = '#cccccc'
```

---

## PITFALL #6: LEGEND PLACEMENT AND READABILITY

### The Problem

Legends can overlap with data points, making the visualization unreadable.

### Best Practices

1. **Multiple legends** - Use `ax.add_artist()` to keep both visible:

```python
# Main legend (upper left)
legend1 = ax.legend(handles=main_handles, loc='upper left',
                    facecolor='white', edgecolor='#cccccc')
ax.add_artist(legend1)  # Keep this legend

# Reference lines legend (lower right)
legend2 = ax.legend(handles=line_handles, loc='lower right',
                    facecolor='white', edgecolor='#cccccc')
```

2. **External placement** for crowded plots:

```python
ax.legend(loc='upper right', bbox_to_anchor=(1.3, 1.1))
```

3. **Move legend based on data** - Don't cover the interesting quadrant.

---

## PITFALL #7: EFFECT SIZE INTERPRETATION

### The Problem

Statistical significance (p-values) without effect size tells you nothing about practical significance.

### Always Report Effect Size

```python
# Cohen's d for comparing groups
def cohens_d(group1, group2):
    pooled_std = np.sqrt((np.var(group1) + np.var(group2)) / 2)
    return (np.mean(group2) - np.mean(group1)) / pooled_std if pooled_std > 0 else 0

d = cohens_d(within_distances, cross_distances)

# Interpretation thresholds
if abs(d) < 0.2:
    effect = "NEGLIGIBLE"
elif abs(d) < 0.5:
    effect = "SMALL"
elif abs(d) < 0.8:
    effect = "MEDIUM"
else:
    effect = "LARGE"
```

### Display in Visualization

```python
ax.set_title(f'Cross-Model Comparison (Cohen\'s d = {d:.3f} - {effect})')
```

---

## VISUALIZATION GENERATOR TEMPLATE

Every visualization script should follow this structure:

```python
#!/usr/bin/env python3
"""
[N]_[Name]: [Description]
===========================
[What this visualization shows]

Data source: Run 023d (IRON CLAD Foundation - 750 experiments)
LIGHT MODE for publication
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

# =============================================================================
# PATHS
# =============================================================================
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
OUTPUT_DIR = Path(__file__).parent

# =============================================================================
# CONSTANTS
# =============================================================================
EVENT_HORIZON = 0.80

PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
}

# =============================================================================
# DATA LOADING
# =============================================================================
def load_data():
    """Load Run 023d results."""
    data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])

def get_probe_type(probe):
    """Get probe type with backward compatibility."""
    return probe.get('probe_type', probe.get('type', 'unknown'))

def get_response_text(probe):
    """Get response text with backward compatibility."""
    return probe.get('response_text', probe.get('response', ''))

# =============================================================================
# VISUALIZATION (LIGHT MODE)
# =============================================================================
def generate_main_visualization(data, output_dir):
    """Create main visualization - LIGHT MODE."""
    fig, ax = plt.subplots(figsize=(12, 8))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')

    # ... visualization code ...

    # Standard finishing
    ax.set_xlabel('X Label', fontsize=12, color='black', fontweight='bold')
    ax.set_ylabel('Y Label', fontsize=12, color='black', fontweight='bold')
    ax.set_title('Title', fontsize=14, color='black', fontweight='bold')
    ax.tick_params(colors='black')
    ax.grid(True, alpha=0.3, color='#cccccc')
    for spine in ax.spines.values():
        spine.set_color('#cccccc')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'visualization_name.{ext}'
        plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

# =============================================================================
# MAIN
# =============================================================================
def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nGenerating visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    generate_main_visualization(results, OUTPUT_DIR)

    print("\n" + "="*70)
    print("VISUALIZATION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
```

---

## VALIDATION CHECKLIST

Before committing any visualization:

### Data Extraction
- [ ] Using correct field names (`probe_type` not `type`, `response_text` not `response`)
- [ ] NOT using `baseline_drift` for comparisons (it's always 0)
- [ ] Aggregating at correct level (model means vs individual experiments)
- [ ] Provider names match data (`anthropic` not `claude`)

### Visual Style
- [ ] Light mode (white background, black text)
- [ ] Provider colors from standard palette
- [ ] Legends don't overlap data
- [ ] Multiple legends properly retained with `add_artist()`

### Statistical Rigor
- [ ] Effect sizes reported (Cohen's d, not just p-values)
- [ ] Sample sizes displayed in titles/legends
- [ ] Thresholds clearly marked (Event Horizon = 0.80)

### Output
- [ ] Both PNG and SVG formats saved
- [ ] DPI = 150 for print quality
- [ ] `bbox_inches='tight'` to prevent clipping

---

## TIPS AND TRICKS

Lessons learned from Run 023 visualization debugging sessions.

### Full Resolution vs Aggregated Data

When visualizing drift trajectories, two complementary views exist:

| Data Type | Points Per Model | Use Case | File Naming |
|-----------|------------------|----------|-------------|
| **Aggregated** | ~30 (peak_drift per iteration) | Cleaner labels, traceable individual paths | `run023_*.png` |
| **Full Resolution** | ~780 (all probe drifts) | Dense patterns, emerged structure | `run023b_*.png` |

**Implementation:** Use `extract_trajectories(data, full_resolution=True/False)`

```python
# Aggregated (default) - one point per experiment iteration
trajectories = extract_trajectories(data, full_resolution=False)  # ~30 points/model

# Full resolution - every probe drift value
trajectories_full = extract_trajectories(data, full_resolution=True)  # ~780 points/model
```

### Line Visibility for Dense Visualizations

For dense visualizations (vortex, pillar analysis) with 16,000+ data points, balance visibility:

| Stability | Alpha | Linewidth | Rationale |
|-----------|-------|-----------|-----------|
| STABLE | 0.35-0.4 | 0.8-1.0 | Lighter - they're the norm |
| VOLATILE | 0.5-0.7 | 1.2-1.5 | Darker - highlight anomalies |

**Visibility ranges:**

```python
# Too faint - patterns invisible
alpha=0.15, linewidth=0.5

# Correct - emerged patterns visible
if status == 'STABLE':
    ax.plot(xs, ys, color=color, alpha=0.35, linewidth=0.8)
else:  # VOLATILE
    ax.plot(xs, ys, color=color, alpha=0.5, linewidth=1.2)

# Too dense - occludes everything
alpha=0.8, linewidth=2.0
```

### Vortex Full-Resolution Treatment (16K+ Datapoints)

The flagship vortex visualization (`run023b_vortex_*.png`) renders ~16,000 data points. Special treatment required:

**Problem:** Individual traces at default visibility (alpha=0.7, linewidth=1.5) create an unreadable blob.

**Solution:** Gradient trace visibility based on stability:

```python
# For full-resolution vortex (16K+ points)
for traj in trajectories:
    status = traj.get('status', 'STABLE')
    provider = traj.get('provider', 'unknown')
    color = PROVIDER_COLORS.get(provider, 'gray')

    # Visibility based on stability
    if status == 'STABLE':
        alpha, lw = 0.35, 0.8
    else:  # VOLATILE - make anomalies stand out
        alpha, lw = 0.5, 1.2

    # Plot trajectory
    ax.plot(angles, radii, color=color, alpha=alpha, linewidth=lw)
```

**Key insight:** With 16K points, you're not trying to see individual traces - you're looking for the **emerged pattern** (the vortex structure). Lower alpha makes the pattern visible.

### Safety Margin Calculation (Pillar Stability Panel 4)

The safety margin shows how far BELOW the Event Horizon a provider operates.

**Problem:** Using `mean_baseline` for full-resolution data produces all-identical bars (~0.80).

```python
# WRONG for full-resolution data:
safety_margin = EVENT_HORIZON - mean_baseline  # All bars show ~0.80

# WHY: Full-resolution trajectories have many short segments.
# Each segment's "baseline" is the first drift value, often near 0.
# So EVENT_HORIZON - 0 = 0.80 for all providers.
```

**Solution:** Use the maximum of baseline and final drift:

```python
# CORRECT for both data types:
max_drift = max(mean_baseline, mean_final)
safety_margin = EVENT_HORIZON - max_drift
```

**Why:** The `mean_final` (or max of both) captures actual operational drift, not the segment start point.

### Label Readability in Dense Plots

For pillar analysis Panel 2 (provider centroids), truncate long model names:

```python
# Too long - overlaps with other labels
label = traj['model']  # "claude-3-5-sonnet-20241022"

# Just right - readable without overlap
label = traj['model'][:20] + '...' if len(traj['model']) > 20 else traj['model']
fontsize = 8  # Not 6 - too small to read
```

---

## PITFALL #8: MISSING DATA FIELDS AND DEFAULT VALUES

### The Problem

When data fields don't exist in the JSON, code silently falls back to default values (often 0.5 or 0), producing identical or meaningless visualizations. This is particularly insidious for radar charts and multi-panel dashboards where multiple metrics are computed.

### Real Example: Unified Dashboard Radar Charts (Dec 2025)

All 25 ship dashboards showed **identical radar plots** because the code expected fields that didn't exist:

```python
# WRONG: Fields don't exist in Run 023b data
all_recoveries = []
all_baselines = []
for r in results:
    if 'recovery_ratio' in r:           # Field DOESN'T EXIST
        all_recoveries.append(r['recovery_ratio'])
    if 'baseline_drift' in r:           # Field DOESN'T EXIST
        all_baselines.append(r['baseline_drift'])

# These lists are EMPTY, so fallback kicks in:
mean_recovery = np.mean(all_recoveries) if all_recoveries else 0.5  # Always 0.5!
mean_baseline = 1 - np.mean(all_baselines) if all_baselines else 0.5  # Always 0.5!
```

### Correct Pattern: Compute From Available Data

```python
# RIGHT: Compute metrics from data that DOES exist
recovery_ratios = []
for r in results:
    peak = r.get('peak_drift', 0)
    settled = r.get('settled_drift', 0)
    if peak > 0.01:  # Avoid div by zero
        # Recovery = how much we recovered from peak
        recovery_ratios.append((peak - settled) / peak)

mean_recovery = np.mean(recovery_ratios) if recovery_ratios else 0.0

# Get baseline from first probe in sequence
all_first_drifts = []
for r in results:
    probes = r.get('probe_sequence', [])
    if probes:
        all_first_drifts.append(probes[0].get('drift', 0))

mean_baseline = 1 - np.mean(all_first_drifts) if all_first_drifts else 0.5
```

### Real Example: Hysteresis Recovery Ratio (Dec 2025)

The recovery ratio histogram showed all values clustered at 0 with outliers at 45-50 because the formula was inverted:

```python
# WRONG: post_avg / step_drift can be > 1 or have tiny denominators
recovery_ratio = post_avg / max(drifts[step_idx], 0.01)  # Produces values 0-50+!

# RIGHT: Recovery = how much drift decreased from peak
peak_drift = max(drifts)
final_drift = drifts[-1]
recovery_ratio = (peak_drift - final_drift) / peak_drift  # Always 0-1
recovery_ratio = max(0, min(1, recovery_ratio))  # Clamp to valid range
```

### Defensive Pattern: Validate Before Using

```python
def compute_radar_metrics(results):
    """Compute radar metrics with defensive checks."""
    metrics = {}

    # Collect raw data
    peaks = [r.get('peak_drift', 0) for r in results if 'peak_drift' in r]
    settled = [r.get('settled_drift', 0) for r in results if 'settled_drift' in r]

    # VALIDATE data exists before computing
    if not peaks:
        print(f"[WARNING] No peak_drift values found - using default")
        metrics['stability'] = 0.5
    else:
        metrics['stability'] = max(0, 1 - np.mean(peaks))

    # Compute recovery from available fields
    if peaks and settled and len(peaks) == len(settled):
        recoveries = [(p - s) / p for p, s in zip(peaks, settled) if p > 0.01]
        metrics['recovery'] = np.mean(recoveries) if recoveries else 0.0
    else:
        print(f"[WARNING] Cannot compute recovery - peaks={len(peaks)}, settled={len(settled)}")
        metrics['recovery'] = 0.0

    return metrics
```

### Data Field Inventory

Before writing ANY visualization, run this check:

```python
# Run this FIRST to see what fields actually exist
def inventory_data_fields(results):
    """Print inventory of available fields."""
    if not results:
        print("NO RESULTS!")
        return

    sample = results[0]
    print("Result-level fields:")
    for key in sorted(sample.keys()):
        val = sample[key]
        if isinstance(val, list):
            print(f"  {key}: list[{len(val)}]")
            if val and isinstance(val[0], dict):
                print(f"    └─ item keys: {list(val[0].keys())[:5]}")
        else:
            print(f"  {key}: {type(val).__name__} = {str(val)[:50]}")

inventory_data_fields(results)
```

### Known Field Availability by Run

| Field | Run 023b | Run 023d | Run 020B | Notes |
|-------|----------|----------|----------|-------|
| `peak_drift` | ✅ | ✅ | ✅ | Always available |
| `settled_drift` | ✅ | ✅ | ✅ | Always available |
| `probe_sequence` | ✅ | ✅ | ✅ | Always available |
| `recovery_ratio` | ❌ | ❌ | ❌ | **MUST COMPUTE** from peak/settled |
| `baseline_drift` | ❌ | ❌ | ❌ | **ALWAYS 0** - use first probe drift |
| `naturally_settled` | ❌ | ✅ | ❌ | Run 023d only |
| `ringback_count` | ❌ | ✅ | ❌ | Run 023d only |

---

## PITFALL #9: HORIZONTAL STRETCHING (1x3 vs 2x2 LAYOUT)

### The Problem

When combining 3+ panels, a single-row horizontal layout (1x3, 1x4) creates uncomfortably wide figures that:
- Don't fit well on standard paper/slides
- Make individual panels too narrow
- Create wasted vertical space

### Solution: Use 2x2 QUAD Layout for 3-4 Panels

```python
# WRONG: 1x3 horizontal (too wide)
fig, axes = plt.subplots(1, 3, figsize=(18, 6))  # 18" wide, 6" tall

# RIGHT: 2x2 quad (balanced proportions)
fig, axes = plt.subplots(2, 2, figsize=(14, 12))  # 14" wide, 12" tall
ax1, ax2 = axes[0, 0], axes[0, 1]  # top row
ax3, ax4 = axes[1, 0], axes[1, 1]  # bottom row
```

### Layout Guidelines

| Panels | Layout | Figure Size | Use Case |
|--------|--------|-------------|----------|
| 2 | 1×2 | (12, 5) | Side-by-side comparison |
| 3 | 2×2 (1 empty) | (14, 12) | Summary with text panel |
| 4 | 2×2 | (14, 12) | Four related metrics |
| 5 | 2×3 (1 empty) | (18, 12) | Provider-level detail |
| 6 | 2×3 | (18, 12) | Full provider grid |

### Example: context_damping_summary.png

The `context_damping_summary.png` is a good reference for 2x2 layout:
- Top-left: Overall statistics (bar chart)
- Top-right: Stability by provider (bar chart)
- Bottom-left: Peak drift distribution (histogram)
- Bottom-right: Key findings (text box)

This quad pattern is preferred over horizontal stretching when combining 3+ related visualizations.

---

## PITFALL #10: ERROR BARS ON BINARY/PROPORTION DATA

### The Problem

When displaying stability rates or other proportion metrics (0-100%), using standard deviation for error bars produces absurdly large whiskers. Binary data (0/1 outcomes) has high variance by nature: `std = sqrt(p*(1-p))` which at p=0.85 gives std≈0.36 (36 percentage points!).

### Real Example: Provider Stability Bar Chart (Dec 2025)

Error bars extended 30-40 percentage points because the code used raw standard deviation:

```python
# WRONG: Standard deviation of binary outcomes is HUGE
rates = [1 if d['stable'] else 0 for d in provider_data]  # List of 0s and 1s
stability_std = np.std(rates) * 100  # At 85% stable, std ≈ 36%!

bars = ax.bar(x, stability_means, yerr=stability_std, capsize=5)
# Result: Whiskers extend from 50% to 120% on an 85% bar!
```

### Correct Pattern: Use Standard Error for Proportions

```python
# RIGHT: Standard error gives appropriate confidence interval
rates = [1 if d['stable'] else 0 for d in provider_data]
n = len(rates)
p = np.mean(rates)

# Standard error of proportion: sqrt(p*(1-p)/n)
stability_se = np.sqrt(p * (1 - p) / n) * 100 if n > 0 else 0

bars = ax.bar(x, [p * 100], yerr=[stability_se], capsize=5)
# Result: With n=150 and p=0.85, SE ≈ 2.9% - reasonable whiskers!
```

### Why Standard Error?

| Statistic | Formula | Purpose | Typical Size |
|-----------|---------|---------|--------------|
| **Std Dev (σ)** | `sqrt(p*(1-p))` | Spread of individual outcomes | 30-50% for proportions |
| **Std Error (SE)** | `sqrt(p*(1-p)/n)` | Precision of the MEAN | 2-5% with decent n |

Standard error shrinks with sample size (√n in denominator), representing our confidence in the estimate. Standard deviation doesn't shrink - it just measures spread.

### When to Use Each

| Metric Type | Use | Why |
|-------------|-----|-----|
| Proportions/rates (0-100%) | **Standard Error** | Shows precision of estimate |
| Continuous measurements | Either (document which) | Std dev shows spread, SE shows precision |
| Small samples (n < 30) | **Confidence interval** | More accurate for small n |

### Alternative: Wilson Score Confidence Interval

For publication-quality proportion confidence intervals:

```python
from scipy import stats

def wilson_ci(successes, total, confidence=0.95):
    """Wilson score confidence interval for proportions."""
    if total == 0:
        return 0, 0, 0
    p = successes / total
    z = stats.norm.ppf((1 + confidence) / 2)
    denom = 1 + z**2 / total
    center = (p + z**2 / (2 * total)) / denom
    spread = z * np.sqrt(p * (1 - p) / total + z**2 / (4 * total**2)) / denom
    return center, center - spread, center + spread

# Usage
stable_count = sum(1 for d in data if d['stable'])
total = len(data)
mean, ci_low, ci_high = wilson_ci(stable_count, total)

# For asymmetric error bars:
yerr = [[mean - ci_low], [ci_high - mean]]
ax.bar(x, [mean * 100], yerr=[[ci_low * 100], [ci_high * 100]], capsize=5)
```

---

## PITFALL #11: ASSUMING FIELD SEMANTICS WITHOUT VERIFICATION

### The Problem

Different experimental runs use the same field names with DIFFERENT semantic meanings. Code that works on one dataset silently produces empty visualizations on another because it assumes a field means something it doesn't.

### Real Example: Run 020B subject_id (Dec 2025)

Bottom panels of `oobleck_control_treatment.png` were completely empty. The code tried to match control and treatment data by `subject_id`:

```python
# WRONG: Assumes subject_id is a provider/model identifier shared between arms
providers = set(d.get('subject_id', d.get('model', 'unknown')) for d in data)

for prov in providers:
    c_data = [d for d in control if d.get('subject_id', d.get('model')) == prov]
    t_data = [d for d in treatment if d.get('subject_id', d.get('model')) == prov]

    if c_data and t_data:  # NEVER TRUE!
        # ... plot data
```

**Why it failed:** In Run 020B, `subject_id` contains **unique session identifiers** like:
- Control: `control_81ec4971`, `control_6ec06259`, `control_d4a3e001`
- Treatment: `treatment_fdac1bbe`, `treatment_90c7e42a`, `treatment_a7b2c3d4`

There is **zero overlap** between control and treatment subject_ids. The `if c_data and t_data` condition is never satisfied.

### Solution: Verify Field Semantics Before Using

```python
# FIRST: Inspect what the field actually contains
def diagnose_field(data, field_name):
    """Check semantic meaning of a field across arms."""
    values = set(d.get(field_name, 'MISSING') for d in data)
    by_arm = {}
    for d in data:
        arm = d.get('arm', 'unknown')
        val = d.get(field_name, 'MISSING')
        by_arm.setdefault(arm, set()).add(val)

    print(f"\n{field_name} analysis:")
    print(f"  Unique values: {len(values)}")
    for arm, vals in by_arm.items():
        print(f"  {arm}: {len(vals)} unique values")
        print(f"    Samples: {list(vals)[:3]}")

    # Check overlap
    if len(by_arm) == 2:
        arms = list(by_arm.keys())
        overlap = by_arm[arms[0]] & by_arm[arms[1]]
        print(f"  Overlap between arms: {len(overlap)}")  # If 0, matching will FAIL!

diagnose_field(data, 'subject_id')
# Output reveals: Overlap between arms: 0  ← This is the bug!
```

### Correct Pattern: Aggregate When No Cross-Arm Identifier Exists

```python
# RIGHT: When subject_id is per-session (no overlap), aggregate ALL data per arm
control_drifts = [d.get('final_drift', 0) for d in data if d.get('arm') == 'control']
treatment_drifts = [d.get('final_drift', 0) for d in data if d.get('arm') == 'treatment']

# Plot aggregate comparison instead of per-subject matching
c_mean = np.mean(control_drifts)
t_mean = np.mean(treatment_drifts)

ax.bar(['Control', 'Treatment'], [c_mean, t_mean])
```

### Field Semantics Reference

| Field | Run 023d Meaning | Run 020B Meaning | Watch Out |
|-------|------------------|------------------|-----------|
| `subject_id` | N/A (not present) | Unique session ID (`control_abc123`) | NOT a join key! |
| `model` | Model name (e.g., `gpt-4`) | NOT present in 020B | Check before using |
| `provider` | Provider (e.g., `openai`) | NOT present in 020B | Check before using |
| `arm` | N/A | `control` or `treatment` | Split by this, not join |

### Defensive Pattern: Always Validate Join Keys

```python
def validate_join_key(data, key_field, group_field):
    """Validate that key_field has overlap across group_field values."""
    groups = set(d.get(group_field) for d in data)
    key_sets = {g: set(d.get(key_field) for d in data if d.get(group_field) == g) for g in groups}

    for g1 in groups:
        for g2 in groups:
            if g1 < g2:  # Avoid duplicate comparisons
                overlap = key_sets[g1] & key_sets[g2]
                if not overlap:
                    print(f"[WARNING] No {key_field} overlap between {g1} and {g2}!")
                    print(f"  {g1} has {len(key_sets[g1])} unique values")
                    print(f"  {g2} has {len(key_sets[g2])} unique values")
                    return False
    return True

# Use before any matching logic
if not validate_join_key(data, 'subject_id', 'arm'):
    print("Cannot match by subject_id - using aggregate comparison instead")
    # Fall back to aggregate logic
```

### Key Insight

**Never assume a field named `subject_id` or `model` is a join key.** Always verify:
1. The field exists in both datasets being compared
2. There is actual overlap in values between the groups you're trying to match
3. The field semantically represents what you think it does

---

## PITFALL #12: COMPRESSED DATA - WHEN TO USE LOG SCALE OR dB

### The Problem

When data spans multiple orders of magnitude OR has many near-zero values with rare large outliers, linear scales compress the majority of data into an unreadable cluster while outliers stretch the axis.

### Real Example: Gravity Parameter Space (Dec 2025)

The Run 018d gravity dynamics scatter plots were unreadable:
- X-axis (gamma) ranged from 0 to 400+
- 90% of data clustered between 0-1
- A few outliers at 100-400 stretched the axis
- Result: All interesting structure invisible in a blob at origin

```python
# WRONG: Linear scale compresses the signal
ax.scatter(gammas, drifts)  # Most points at origin, axis stretched to 400

# RIGHT: Log scale spreads the data
valid_pairs = [(g, d) for g, d in zip(gammas, drifts) if g > 0]
valid_gammas, valid_drifts = zip(*valid_pairs)
ax.scatter(valid_gammas, valid_drifts)
ax.set_xscale('log')  # Now structure visible across decades
```

### When to Use Log Scale

| Condition | Use Log Scale | Why |
|-----------|---------------|-----|
| Data spans 3+ orders of magnitude | ✅ YES | Linear compresses small values |
| Many zeros with rare large values | ✅ YES (filter zeros) | Zeros drown signal |
| Exponential decay/growth data | ✅ YES | Linearizes exponentials |
| Rate/frequency data | ✅ YES | Natural for multiplicative processes |
| Bounded 0-1 data (proportions) | ❌ NO | Use linear or logit |
| Symmetric around zero | ❌ NO | Log undefined for negatives |

### Handling Zeros in Log Plots

Zeros are undefined in log scale. Three approaches:

```python
# Approach 1: Filter zeros, note in visualization
nonzero = [x for x in data if x > 0]
zero_count = len(data) - len(nonzero)
ax.hist(nonzero, bins=np.logspace(-3, 2, 30))
ax.set_xscale('log')
ax.text(0.02, 0.98, f'{zero_count} zero values excluded',
        transform=ax.transAxes, fontsize=8, va='top')

# Approach 2: Epsilon replacement (for colormaps)
data_log_safe = [max(x, 0.001) for x in data]  # Small epsilon
scatter = ax.scatter(xs, ys, c=data_log_safe,
                     norm=plt.matplotlib.colors.LogNorm())

# Approach 3: Symlog for data with zeros AND negatives
ax.set_xscale('symlog', linthresh=0.01)  # Linear near 0, log elsewhere
```

### dB Scale for Signal Analysis

When comparing signal ratios or SNR-like metrics, decibels (dB) may be more intuitive:

```python
# Convert ratio to dB
def to_dB(ratio):
    """Convert power ratio to decibels."""
    return 10 * np.log10(max(ratio, 1e-10))  # Floor to avoid -inf

def to_dB_amplitude(ratio):
    """Convert amplitude ratio to decibels (20*log10)."""
    return 20 * np.log10(max(ratio, 1e-10))

# Example: SNR plot
snr_db = [to_dB(signal / noise) for signal, noise in pairs]
ax.hist(snr_db, bins=30)
ax.set_xlabel('SNR (dB)')
```

### When to Use dB

| Use Case | dB Type | Formula | Example |
|----------|---------|---------|---------|
| Power ratios | Power dB | 10·log₁₀(P₁/P₂) | Signal power / noise power |
| Amplitude ratios | Amplitude dB | 20·log₁₀(A₁/A₂) | Voltage, drift magnitude |
| Frequency response | Either | Depends on context | Filter gain plots |

### Log-Scaled Histograms

For distributions with long tails, use log-spaced bins:

```python
# WRONG: Linear bins compress the tail
ax.hist(data, bins=50)  # 90% of counts in first 2 bins!

# RIGHT: Log-spaced bins spread the distribution
log_min = np.log10(max(min(data), 1e-6))
log_max = np.log10(max(data))
log_bins = np.logspace(log_min, log_max, 30)

ax.hist(data, bins=log_bins)
ax.set_xscale('log')
```

### Colormap Log Normalization

For scatter plot colormaps with skewed data:

```python
# Linear colormap (WRONG for skewed data)
scatter = ax.scatter(x, y, c=values, cmap='viridis')  # Most colors unused

# Log-normalized colormap (RIGHT)
from matplotlib.colors import LogNorm
scatter = ax.scatter(x, y, c=values, cmap='viridis',
                     norm=LogNorm(vmin=0.01, vmax=100))
```

### Validation Checklist for Log/dB Decisions

Before finalizing any visualization:

- [ ] Check data range: Does it span 3+ orders of magnitude?
- [ ] Check for zeros: How many? Can they be filtered or need epsilon?
- [ ] Check for negatives: If present, use symlog not log
- [ ] Check if structure emerges: Does log reveal patterns hidden in linear?
- [ ] Label axes clearly: Include "(Log Scale)" or "(dB)" in axis label
- [ ] Note filtered values: If zeros excluded, show count in annotation

---

## PITFALL #14: X-AXIS LABEL CROWDING WITH MANY CATEGORIES

### The Problem

When visualizing data across the full armada (35-50+ models), x-axis labels become an unreadable mess of overlapping text. This is especially common with bar charts showing per-model breakdowns.

### Real Example: Oobleck Thermometer (Dec 2025)

The thermometer visualization tried to show inherent vs induced drift for all 35+ ships:
- Model names like `grok-4.1-fast-non-reasoning` are long
- Breaking on hyphens (`m.replace('-', '\n')`) creates tall vertical labels
- With 35 bars, labels overlap completely - rendering them useless

### Wrong Pattern

```python
# WRONG: Full model names with line breaks - unreadable with >10 models
display_labels = [m.replace('-', '\n') for m in models]
ax.set_xticklabels(display_labels, rotation=0, ha='center', fontsize=9)
```

### Correct Pattern: Adaptive Labeling

```python
# RIGHT: Adapt strategy based on number of categories
if len(models) > 10:
    # Abbreviate model names for readability
    def abbreviate_model(name):
        abbrevs = [
            ('claude-', 'c-'), ('anthropic-', 'a-'),
            ('gemini-', 'gem-'), ('google-', 'g-'),
            ('-mini', '-m'), ('-nano', '-n'),
            ('-fast-', '-f-'), ('-reasoning', '-r'),
            ('-non-reasoning', '-nr'), ('-distill', '-d'),
            ('deepseek-', 'ds-'), ('mistral-', 'mis-'),
            ('mixtral-', 'mix-'), ('llama', 'L'),
            ('nemotron-', 'nem-'), ('grok-', 'grk-'),
            ('kimi-', 'k-'),
        ]
        result = name
        for old, new in abbrevs:
            result = result.replace(old, new)
        return result

    display_labels = [abbreviate_model(m) for m in models]
    ax.set_xticklabels(display_labels, rotation=45, ha='right', fontsize=7)
else:
    # Full names are fine with <10 models
    display_labels = [m.replace('-', '\n') for m in models]
    ax.set_xticklabels(display_labels, rotation=0, ha='center', fontsize=9)
```

### Alternative Strategies for Many Categories

| Strategy | When to Use | Implementation |
|----------|-------------|----------------|
| **Abbreviate** | 10-30 models | Use abbreviation table + rotation |
| **Index + Legend** | 30-50 models | Number labels, key in legend/annotation |
| **Facet/Group** | 50+ models | Split by provider, show faceted subplots |
| **Top-N only** | Huge datasets | Show only top/bottom N, aggregate rest |

### Index + Legend Pattern (for 30+ categories)

```python
# When abbreviations still crowd, use indices
if len(models) > 30:
    # Use numeric indices on x-axis
    ax.set_xticks(range(len(models)))
    ax.set_xticklabels(range(1, len(models) + 1), fontsize=8)

    # Create legend mapping in separate text box
    legend_text = "\\n".join([f"{i+1}: {m}" for i, m in enumerate(models)])
    fig.text(1.02, 0.5, legend_text, fontsize=6, fontfamily='monospace',
             transform=ax.transAxes, va='center')
```

### Faceted Subplots Pattern (for provider grouping)

```python
# Group by provider and create subplots
providers = sorted(set(get_provider(m) for m in models))
fig, axes = plt.subplots(1, len(providers), figsize=(4*len(providers), 6), sharey=True)

for ax, provider in zip(axes, providers):
    provider_models = [m for m in models if get_provider(m) == provider]
    # Plot only this provider's models - now manageable number per subplot
    ax.bar(range(len(provider_models)), values_for_provider)
    ax.set_title(provider.upper())
```

### Validation Checklist for Label Crowding

Before finalizing any categorical visualization:

- [ ] Count categories: If >10, abbreviation likely needed
- [ ] Test at target resolution: Does it render clearly at intended DPI?
- [ ] Check overlap: Can you read all labels without overlap?
- [ ] Consider alternatives: Would faceting or aggregation be clearer?
- [ ] Preserve readability: Abbreviations should still be recognizable

---

## RELATED SPECS

| Spec | Purpose |
|------|---------|
| [0_RUN_METHODOLOGY.md](0_RUN_METHODOLOGY.md) | Run design and data collection |
| [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md) | **ONE SOURCE OF TRUTH** for drift methodology |
| [ARCHITECTURE_MATRIX.json](../../0_results/manifests/ARCHITECTURE_MATRIX.json) | Fleet configuration (provider/model_family/ship terminology) |
| [ARMADA_MAP.md](../../../../../docs/maps/1_ARMADA_MAP.md) | Complete fleet roster (49 ships, 10 families, 5 providers) |
| [LLM_BEHAVIORAL_MATRIX.md](../../../../../docs/maps/6_LLM_BEHAVIORAL_MATRIX.md) | Provider behavioral profiles |

---

*"The visualization that misrepresents the data is worse than no visualization at all."*
