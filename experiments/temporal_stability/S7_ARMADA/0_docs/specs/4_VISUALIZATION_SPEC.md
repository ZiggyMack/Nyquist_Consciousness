# S7 ARMADA Visualization Specification

**Purpose:** Prevent recurring pitfalls when creating visualizations from experimental data. Consult this BEFORE creating any new visualization script.

**Last Updated:** December 22, 2025
**Lessons From:** Runs 023b-023e visualization debugging sessions

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

## RELATED SPECS

| Spec | Purpose |
|------|---------|
| [0_RUN_METHODOLOGY.md](0_RUN_METHODOLOGY.md) | Run design and data collection |
| [../../../docs/maps/LLM_BEHAVIORAL_MATRIX.md](../../../docs/maps/LLM_BEHAVIORAL_MATRIX.md) | Provider behavioral profiles |

---

*"The visualization that misrepresents the data is worse than no visualization at all."*
