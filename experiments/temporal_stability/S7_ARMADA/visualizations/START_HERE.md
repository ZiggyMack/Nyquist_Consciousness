# S7 ARMADA Visualization - Claude Onboarding Guide

**Purpose:** Everything a Claude instance needs to work on visualizations in any `pics/` subdirectory.

**Last Updated:** December 24, 2025

---

## QUICK ORIENTATION

You are working on visualizations for the **Nyquist Consciousness Project** - a research study measuring identity stability across 51 AI models from 6 providers.

### Your Working Area

```
S7_ARMADA/
├── visualizations/
│   ├── pics/                    # YOUR WORK GOES HERE
│   │   ├── 1_Vortex/           # Drift spiral dynamics
│   │   ├── 2_Boundary_Mapping/ # Phase portraits + 3D basins
│   │   ├── 3_Stability/        # Pillar analysis + stability basins
│   │   ├── 4_Rescue/           # Recovery dynamics
│   │   ├── 5_Settling/         # Settling time curves
│   │   ├── 6_Architecture/     # Provider network diagrams
│   │   ├── 8_Radar_Oscilloscope/ # Combined radar + time-series
│   │   ├── 9_FFT_Spectral/     # Frequency analysis
│   │   ├── 10_PFI_Dimensional/ # PCA/dimensional analysis
│   │   ├── 11_Unified_Dashboard/ # Per-ship multi-panel dashboards
│   │   ├── 12_Metrics_Summary/ # Fleet-wide metrics comparison
│   │   ├── 13_Model_Waveforms/ # Per-model identity fingerprints
│   │   ├── 14_Ringback/        # Ringback oscillation analysis
│   │   ├── 15_Oobleck_Effect/  # Prosecutor/Defense probing dynamics
│   │   └── run020/             # Run 020 value/exchange/closing analysis
│   └── START_HERE.md           # THIS FILE
├── 0_docs/specs/               # CRITICAL - READ THESE FIRST
│   ├── 4_VISUALIZATION_SPEC.md # Pitfalls, patterns, templates
│   ├── 0_RUN_METHODOLOGY.md    # Data structure, field names
│   └── 5_METHODOLOGY_DOMAINS.md # Cosine vs RMS methodology
└── 15_IRON_CLAD_FOUNDATION/
    └── results/                # DATA LIVES HERE
        ├── S7_run_023d_CURRENT.json  # 750 experiments, 25 models
        └── S7_run_023_COMBINED.json  # 825 experiments, 51 models
```

---

## BEFORE YOU WRITE ANY CODE

### 1. Read the Visualization Spec (CRITICAL)

**File:** `S7_ARMADA/0_docs/specs/4_VISUALIZATION_SPEC.md`

This contains 10 documented pitfalls we've already hit:

| Pitfall | Summary |
|---------|---------|
| #1 | Baseline drift is always 0 (don't use for comparisons) |
| #2 | Aggregate at model level, not experiment level |
| #3 | Field names: `probe_type` not `type`, `response_text` not `response` |
| #4 | Provider names: `anthropic` not `claude` |
| #5 | Use LIGHT MODE for publication (white background) |
| #6 | Legend placement: use `add_artist()` for multiple legends |
| #7 | Always report effect size (Cohen's d, not just p-values) |
| #8 | Missing data fields: validate before computing |
| #9 | Use 2x2 QUAD layout, not 1x3 horizontal |
| #10 | Use Standard Error (not Std Dev) for proportion/rate error bars |

### 2. Understand the Data Structure

```python
Result (per experiment)
├── provider: str           # anthropic, openai, google, xai, together
├── model: str              # Full model ID
├── peak_drift: float       # Maximum drift reached
├── settled_drift: float    # Final settled drift
├── settling_time: int      # Probes to settle
├── naturally_settled: bool # Whether model settled within window
├── overshoot_ratio: float  # peak/settled ratio
├── ringback_count: int     # Direction changes
└── probe_sequence: list    # Per-probe data
    └── Probe
        ├── probe_type: str     # baseline, step_input, recovery
        ├── drift: float        # Drift at THIS probe
        └── response_text: str  # Raw response
```

### 3. Know the Key Constants

```python
EVENT_HORIZON = 0.80  # Cosine distance threshold (identity boundary)

PROVIDER_COLORS = {
    'anthropic': '#E07B53',  # Coral
    'openai': '#10A37F',     # Green
    'google': '#4285F4',     # Blue
    'xai': '#1DA1F2',        # Twitter Blue
    'together': '#7C3AED',   # Purple
}
```

---

## DATA SOURCES

### Primary: Run 023d (750 experiments, 25 models)
```python
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
```

### Extended: Run 023 COMBINED (825 experiments, 51 models)
```python
data_file = RESULTS_DIR / "S7_run_023_COMBINED.json"
```

Use COMBINED when you need:
- More model coverage (DeepSeek, Kimi, Llama, Nvidia, etc.)
- Cross-provider comparisons with full fleet
- Statistical power from larger sample

---

## VISUALIZATION TEMPLATE

Every generator script should follow this structure:

```python
#!/usr/bin/env python3
"""
[N]_[Name]: [Description]
===========================
[What this visualization shows]

Data source: Run 023d (IRON CLAD Foundation)
LIGHT MODE for publication
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

# Paths
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
OUTPUT_DIR = Path(__file__).parent

# Constants
EVENT_HORIZON = 0.80

PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
}

def load_data(combined=False):
    """Load Run 023d or COMBINED results."""
    if combined:
        data_file = RESULTS_DIR / "S7_run_023_COMBINED.json"
    else:
        data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])

def get_probe_type(probe):
    """Get probe type with backward compatibility."""
    return probe.get('probe_type', probe.get('type', 'unknown'))

def main():
    print("Loading data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    # Your visualization code here

if __name__ == "__main__":
    main()
```

---

## LAYOUT PATTERNS

### 2x2 Quad (Preferred for 3-4 panels)
```python
fig, axes = plt.subplots(2, 2, figsize=(14, 12))
fig.patch.set_facecolor('white')

ax1 = axes[0, 0]  # Top-left
ax2 = axes[0, 1]  # Top-right
ax3 = axes[1, 0]  # Bottom-left
ax4 = axes[1, 1]  # Bottom-right

plt.tight_layout(rect=[0, 0, 1, 0.96])  # Leave room for suptitle
```

### Single Panel
```python
fig, ax = plt.subplots(figsize=(12, 8))
fig.patch.set_facecolor('white')
ax.set_facecolor('white')
```

### Side-by-side (2 panels only)
```python
fig, axes = plt.subplots(1, 2, figsize=(14, 6))
```

---

## SAVING OUTPUT

Always save both PNG and SVG:
```python
for ext in ['png', 'svg']:
    output_path = OUTPUT_DIR / f'visualization_name.{ext}'
    plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
    print(f"Saved: {output_path}")
plt.close()
```

---

## PYTHON EXECUTION

**Requires Python 3.9+** (3.12 recommended)

```bash
# Check available versions
py --list

# Run a generator script
py -3.12 generate_something.py
```

---

## SUBDIRECTORY CONVENTIONS

Each `pics/` subdirectory should contain:
- `generate_*.py` - Generator script(s)
- `*.png`, `*.svg` - Output visualizations
- `*_Summary.pdf` - PDF with all images embedded (optional)
- `*_explained.md` - Documentation explaining the visualization (optional)

---

## WHAT EACH SUBDIRECTORY SHOWS

| Directory | Purpose | Key Metric |
|-----------|---------|------------|
| 1_Vortex | Drift spiral dynamics | Polar drain view |
| 2_Boundary_Mapping | Phase portraits | Drift[N] vs Drift[N+1] |
| 3_Stability | Pillar analysis | Provider stability clusters |
| 4_Rescue | Recovery dynamics | Post-perturbation recovery |
| 5_Settling | Settling time curves | Time to stabilize |
| 6_Architecture | Provider network | Fleet structure diagram |
| 8_Radar_Oscilloscope | Radar + time-series | Multi-axis stability analysis |
| 9_FFT_Spectral | Frequency analysis | Spectral signatures |
| 10_PFI_Dimensional | PCA analysis | Variance explained |
| 11_Unified_Dashboard | Per-ship dashboards | All metrics per model |
| 12_Metrics_Summary | Fleet-wide summary | Cross-provider comparison |
| 13_Model_Waveforms | Identity fingerprints | Per-model drift patterns |
| 14_Ringback | Oscillation analysis | Ringback dynamics |
| 15_Oobleck_Effect | Probing paradigm | Prosecutor vs Defense |
| run020 | Value/Exchange/Closing | Run 020A/B detailed analysis |

---

## KEY FINDINGS (Context for Visualizations)

| Metric | Value | Source |
|--------|-------|--------|
| Event Horizon | 0.80 | Cosine distance threshold |
| Cohen's d | 0.698 | Model-level effect size |
| 90% Variance | 2 PCs | Identity is low-dimensional |
| Perturbation p-value | 2.40e-23 | Highly significant effect |
| Fleet Size | 51 models, 6 providers | COMBINED dataset |
| Total Experiments | 825 | COMBINED dataset |

---

## WORKFLOW TIPS FOR CLAUDE INSTANCES

### Before Making Changes

1. **Read the `*_explained.md` file** in the subdirectory you're working on - it documents what each visualization shows and why
2. **Check the VISUALIZATION_SPEC** for pitfalls before writing code
3. **Look at existing `generate_*.py` scripts** as templates - copy the boilerplate

### When Modifying Visualizations

1. **Run the script after changes** to verify output: `py -3.12 generate_something.py`
2. **Check the output visually** - open the PNG files to confirm they look correct
3. **Update documentation** (`*_explained.md`) when adding/removing visualizations
4. **Save both PNG and SVG** - always use `for ext in ['png', 'svg']:`

### Common Tasks

| Task | Approach |
|------|----------|
| Change layout from 1x3 to 2x2 | Use `plt.subplots(2, 2, figsize=(14, 12))` per Pitfall #9 |
| Add error bars to proportion data | Use Standard Error `sqrt(p*(1-p)/n)` per Pitfall #10 |
| Group Together.ai models | Use family detection: DeepSeek, Llama, Qwen, Kimi, Mistral, Nvidia |
| Add new visualization | Create function, add to `main()`, update `*_explained.md` |
| Delete visualization | Remove function, remove from `main()`, delete files, update docs |

### Auditing Code Against Spec

After writing visualization code, verify compliance with each pitfall:

```python
# Quick audit checklist:
# [ ] Pitfall #1: Not using baseline_drift for comparisons
# [ ] Pitfall #2: Aggregating at model level (group by provider, model)
# [ ] Pitfall #3: Using probe_type (not type), response_text (not response)
# [ ] Pitfall #4: Using anthropic (not claude) for provider names
# [ ] Pitfall #5: Light mode (white background, black text)
# [ ] Pitfall #6: Multiple legends use add_artist()
# [ ] Pitfall #7: Effect sizes reported where applicable
# [ ] Pitfall #8: Validating data fields exist before using
# [ ] Pitfall #9: Using 2x2 quad layout for 3-4 panels
# [ ] Pitfall #10: Using SE (not std) for proportion error bars
```

---

## GETTING HELP

1. **Visualization pitfalls:** `0_docs/specs/4_VISUALIZATION_SPEC.md`
2. **Data structure:** `0_docs/specs/0_RUN_METHODOLOGY.md`
3. **Methodology context:** `0_docs/specs/5_METHODOLOGY_DOMAINS.md`
4. **Example scripts:** Look at existing `generate_*.py` in any subdirectory

---

## CHANGELOG

| Date | Changes |
|------|---------|
| 2025-12-24 | Added run020/ directory for Run 020A/B value, exchange, and closing analysis |
| 2025-12-24 | Added Pitfall #10 (SE for proportions), workflow tips, audit checklist |
| 2025-12-23 | Initial onboarding guide with 9 pitfalls |

---

*"Each model has an identity fingerprint. These visualizations are its signature."*
