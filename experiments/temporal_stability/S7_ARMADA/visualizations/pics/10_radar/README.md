<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./generate_radar_plots.py
  - ../../visualize_armada.py
  - ../../../0_results/temporal_logs/
impacts:
  - ../README.md
  - ../../../../../../WHITE-PAPER/figures/10_radar/
keywords:
  - radar
  - visualization
  - provider_fingerprint
  - pfi
  - nyquist_pillar
-->
# 10_radar: Multi-Dimensional Radar Visualizations

**Location:** `experiments/temporal_stability/S7_ARMADA/visualizations/pics/10_radar/`
**Generated:** December 17, 2025

---

## Visualizations

### 1. pfi_component_distribution.png

**5D Identity Weight Radar**

Shows the relative weights of the five identity dimensions:
- Voice (how the model speaks)
- Values (ethical priorities)
- Reasoning (analytical patterns)
- Self-Model (meta-cognition)
- Narrative (storytelling structure)

**Interpretation:** Equal weights indicate balanced identity; asymmetric weights indicate dominant dimensions.

---

### 2. run018_provider_fingerprint.png

**Cross-Provider Comparison Radar**

Compares AI providers across 5 behavioral metrics:
- **Mean Drift** - Average deviation from baseline (normalized to Event Horizon)
- **Peak Drift** - Maximum deviation reached
- **Volatility** - Rate of Event Horizon crossings
- **Stability** - Inverse of volatility
- **Consistency** - Inverse of standard deviation

**Providers Shown:** Claude (Anthropic), GPT (OpenAI), Gemini (Google), Grok (xAI), Together.ai

**Key Finding:** Different providers have distinct "fingerprints" in identity space.

---

### 3. run009_provider_fingerprint.png

**Run 009 Provider Comparison**

Same metrics as Run 018 but with Run 009 (Event Horizon Discovery) data.
Shows earlier experimental data for comparison.

---

### 4. nyquist_pillar_placeholder.png

**Placeholder for Nyquist Set Pillars**

A template radar with the 5 Nyquist pillars:
- Voice
- Values
- Reasoning
- Self-Model
- Narrative

**Status:** Awaiting Run 010 v2 data (will use embedding-based pillar extraction)

**Current State:** OLD 5D scalars (A_pole, B_zero, C_meta, D_identity, E_hedging) are DEPRECATED. This placeholder shows the target structure.

---

## Generation

### Via visualize_armada.py (Recommended)

```bash
# Generate radar plots for a specific run
python visualize_armada.py --run 018 --type radar

# Generate all visualization types including radar
python visualize_armada.py --run 018 --all
```

### Via standalone script

```bash
python generate_radar_plots.py
```

---

## Technical Details

**Data Sources:**
- PFI component weights from EXP2_SSTACK phase 3 results
- Provider metrics from `0_results/temporal_logs/run0XX_*.json`

**Dependencies:**
- matplotlib
- numpy

**Output Formats:**
- PNG (raster, 300 DPI)
- SVG (vector, scalable)

---

## Sync to WHITE-PAPER

Files are synced to `WHITE-PAPER/figures/10_radar/` for publication.

```bash
# Manual sync
cp *.png *.svg ../../../../../../../WHITE-PAPER/figures/10_radar/
```

---

## Connection to Paper

These radar plots support:
- **Section 8 (PFI Dimensional Validation)** - Shows multi-dimensional identity structure
- **Cross-Architecture Analysis** - Provider fingerprints demonstrate distinct training signatures
- **Future Work** - Nyquist pillar placeholder indicates direction for Run 010 v2

---

*"Identity has shape. Radar plots reveal it."*
