# Model Identity Waveforms

**A Visual Guide to Per-Model Identity Drift Patterns**

**Purpose:** Show the characteristic "identity fingerprint" for each model in the fleet.

**Core Question:** How does each model's identity drift pattern differ?

**Data Source:** Run 023d IRON CLAD Foundation (750 experiments, 25 models)

---

## Visualizations

### 1. model_waveform_grid.png
**25-Panel Grid: All Models at a Glance**

Shows the identity drift waveform for each of the 25 models in the fleet. Each panel displays:
- Individual experiment traces (faint lines)
- Mean waveform (bold line)
- Event Horizon reference (red dashed at 0.80)
- Step input marker (orange dotted at probe 3)

**Key insight:** Models have distinct "fingerprints" - some spike high then recover, others stay stable throughout.

### 2. provider_waveform_overlay.png
**5-Panel Provider Comparison**

Each provider's models overlaid on the same axes. This shows:
- Intra-provider variation (how different models from same provider behave)
- Model-level mean waveforms for direct comparison
- Provider-specific color coding

**Key insight:** Some providers show tight clustering (consistent training philosophy), others show wide spread (diverse model architectures).

### 3. fleet_waveform_comparison.png
**Fleet-Wide Overlay**

All 25 model mean waveforms on a single plot with:
- Color-coded by provider
- Probe regions marked (Baseline, Step Input, Recovery)
- Event Horizon reference

**Key insight:** Fleet-level patterns emerge - most models show initial spike at step input (probe 3) followed by recovery.

### 4. Individual Model Waveforms (waveform_*.png)
**Detailed Single-Model Views**

For the top 6 models by sample size:
- All experiment traces with gradient transparency
- Mean ± 1 standard deviation envelope
- Probe region shading
- Summary statistics box (Peak, Settled, STD)

**Key insight:** Individual model behavior with uncertainty bounds. Some models are highly consistent (tight envelope), others variable (wide envelope).

---

## How to Read These Waveforms

**X-axis (Probe Index):**
- Probes 0-2: Baseline (normal conversation)
- Probe 3: Step Input (identity perturbation)
- Probes 4+: Recovery (return to normal)

**Y-axis (Cosine Distance):**
- 0.0 = Identical to baseline (perfect identity retention)
- 0.80 = Event Horizon (significant identity drift)
- 1.0 = Maximum measurable drift

**Waveform Patterns:**
- **Spike and Recover:** Sharp rise at step input, gradual return to baseline
- **Plateau:** Elevated drift that stays high (hysteresis)
- **Stable:** Minimal drift throughout (robust identity)
- **Oscillating:** Multiple peaks and valleys (unstable)

---

## Key Metrics from Run 023d

| Metric | Value |
|--------|-------|
| Total Models | 25 |
| Experiments | 750 (30 per model) |
| Providers | 5 (Anthropic, OpenAI, Google, xAI, Together.ai) |
| Probe Window | 7-24 probes (extended settling) |
| Event Horizon | 0.80 cosine distance |

---

## Provider Color Legend

| Provider | Color |
|----------|-------|
| Anthropic | Coral (#E07B53) |
| OpenAI | Green (#10A37F) |
| Google | Blue (#4285F4) |
| xAI | Twitter Blue (#1DA1F2) |
| Together.ai | Purple (#7C3AED) |

---

*"Each model has an identity fingerprint. These waveforms are its signature."*

**Generated:** December 23, 2025
