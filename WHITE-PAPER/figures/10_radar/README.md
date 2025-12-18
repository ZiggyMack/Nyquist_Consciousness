# 10_radar: Multi-Dimensional Radar Visualizations

**Source:** `experiments/temporal_stability/S7_ARMADA/visualizations/pics/10_radar/`
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

**Providers Shown:** Claude (Anthropic), Gemini (Google), Grok (xAI)

**Key Finding:** Different providers have distinct "fingerprints" in identity space.

---

### 3. nyquist_pillar_placeholder.png

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

## Technical Details

**Generation Script:** `generate_radar_plots.py`

**Data Sources:**
- PFI component weights from EXP2_SSTACK phase 3 results
- Provider metrics from `0_results/temporal_logs/run018_*.json`

**Dependencies:**
- matplotlib
- numpy

---

## Connection to Paper

These radar plots support:
- **Section 8 (PFI Dimensional Validation)** - Shows multi-dimensional identity structure
- **Cross-Architecture Analysis** - Provider fingerprints demonstrate distinct training signatures
- **Future Work** - Nyquist pillar placeholder indicates direction for Run 010 v2

---

*"Identity has shape. Radar plots reveal it."*
