# S7 ARMADA Visualization PDFs - Reviewer Package

**Purpose:** Complete visual documentation of Run 023 IRON CLAD findings for reviewer consumption.

**Generated:** December 24, 2025

**Methodology:** Cosine distance (1 - cosine_similarity) | Event Horizon = 0.80

**Data Source:** Run 023 Combined (825 experiments, 51 models, 6 providers)

---

## Quick Reference

| PDF | Focus | Key Finding |
|-----|-------|-------------|
| 1_Vortex | Identity trajectory dynamics | Vortex patterns in drift space |
| 2_Boundary_Mapping | Identity boundary exploration | Safe operating regions mapped |
| 3_Stability | Natural stability classification | 88% STABLE across fleet |
| 4_Rescue | Recovery intervention analysis | Rescue effectiveness metrics |
| 5_Settling | Settling time dynamics | τₛ ≈ 10.2 probes average |
| 6_Architecture | Fleet topology | Provider hub structure |
| 8_Radar_Oscilloscope | Provider fingerprints | Polar radar signatures |
| 9_FFT_Spectral | Frequency analysis | Spectral signatures by provider |
| 10_PFI_Dimensional | Cosine identity validation | Cohen's d = 0.698, 2 PCs = 90% |
| 11_Unified_Dashboard | Per-model deep dives | Individual ship profiles |
| 12_Metrics_Summary | Fleet-wide KPIs | 10 visualizations, full analysis |
| 13_Model_Waveforms | Per-model identity fingerprints | Unique waveform signatures |
| 14_Ringback | Oscillation dynamics | Post-recovery oscillation patterns |
| 15_Oobleck_Effect | Prosecutor/Defense probing | Phase-dependent response dynamics |
| run018_Summary | Context damping experiments | Multi-threshold validation |
| run020_Summary | Value/Exchange/Closing analysis | Run 020A/B tribunal sessions |

---

## PDF Descriptions

### 1_Vortex_Summary.pdf (15 MB)

**What it shows:** Identity drift trajectories visualized as vortex patterns in embedding space.

**Key visualizations:**
- Fleet vortex (all ships aggregated)
- Provider-colored trajectory traces
- Stability basin structure

**Key finding:** Identity trajectories exhibit characteristic vortex patterns that reveal attractor dynamics.

---

### 2_Boundary_Mapping_Summary.pdf (7.5 MB)

**What it shows:** Exploration of identity boundaries - where stability transitions to volatility.

**Key visualizations:**
- Event Horizon contours (D = 0.80)
- Safe operating region mapping
- Boundary approach trajectories

**Key finding:** Clear boundaries exist between stable and volatile operating regions.

---

### 3_Stability_Summary.pdf (6.5 MB)

**What it shows:** Natural stability classification across the fleet.

**Key visualizations:**
- Stability classification pie chart
- Provider stability comparison
- Model-by-model stability rates

**Key finding:** 88% of fleet naturally stable (settles without timeout, drift < EH).

---

### 4_Rescue_Summary.pdf (719 KB)

**What it shows:** Effectiveness of rescue interventions when models approach Event Horizon.

**Key visualizations:**
- Recovery trajectories after intervention
- Rescue success rates
- Time-to-recovery metrics

**Key finding:** Rescue interventions effective for most volatile models.

---

### 5_Settling_Summary.pdf (3.7 MB)

**What it shows:** Settling time dynamics - how long models take to stabilize after perturbation.

**Key visualizations:**
- Settling time distribution (histogram)
- Provider settling comparison
- 20-probe extended recovery traces
- Waterfall settling visualizations

**Key finding:** Average settling time τₛ ≈ 10.2 probes; 73% settle naturally within 20 probes.

---

### 6_Architecture_Summary.pdf (95 KB)

**What it shows:** Fleet topology and architecture overview.

**Key visualizations:**
- Provider hub structure
- Model classification hierarchy
- VALIS style distribution

**Key finding:** 6 provider hubs (Anthropic, OpenAI, Google, xAI, Together, Nvidia) with distinct architectural signatures.

---

### 8_Radar_Oscilloscope_Summary.pdf (1.6 MB)

**What it shows:** Provider identity fingerprints as polar radar plots.

**Key visualizations:**
- Per-provider radar signatures
- Multi-metric oscilloscope view
- Provider differentiation patterns

**Key finding:** Each provider has a characteristic "fingerprint" in identity space.

---

### 9_FFT_Spectral_Summary.pdf (2.0 MB)

**What it shows:** Frequency-domain analysis of identity dynamics.

**Key visualizations:**
- Per-provider FFT spectra with confidence bands
- Power spectral density comparison
- Spectrogram (time-frequency) view
- Dominant frequency by provider

**Key finding:** Identity dynamics exhibit characteristic frequency signatures that differentiate providers.

---

### 10_PFI_Dimensional_Summary.pdf (1.5 MB)

**What it shows:** Validation that cosine distance measures REAL identity differences.

**Key visualizations:**
- Phase 2: PCA dimensionality (variance curve, PC scatter, provider clusters, EH contour)
- Phase 3A: Perturbation validation (surface vs deep comparison, p = 2.40e-23)
- Phase 3B: Cross-model comparison (Cohen's d = 0.698 box plots, histogram, provider matrix)

**Key findings:**
- Cohen's d = 0.698 (MEDIUM effect) - genuine identity differences detected
- 2 PCs capture 90% variance (vs 43 for Euclidean) - highly concentrated signal
- Perturbation validation p = 2.40e-23 - cosine correctly distinguishes perturbation types

**Methodological Note:** Cohen's d is lower than archive (0.977) because we now use honest model-level aggregates instead of noise-inflated experiment-level comparison. Lower dimensionality means signal is MORE concentrated, not weaker.

---

### 11_Unified_Dashboard_Summary.pdf (634 KB)

**What it shows:** Individual ship dashboards with per-model deep dives.

**Key visualizations:**
- Per-model stability profiles
- Individual drift trajectories
- Model-specific metrics tables

**Key finding:** Detailed behavioral profiles for each of the 51 models in the fleet.

---

### 12_Metrics_Summary.pdf (2.0 MB)

**What it shows:** Comprehensive fleet-wide metrics and analysis.

**Key visualizations:**
1. Armada Network - Full Fleet (51 models, hub layout)
2. Armada Network - IRON CLAD (25 models, extended testing)
3. Provider Stability Comparison (bar chart with error bars)
4. Fleet-Wide Metrics Comparison (grouped by dimension)
5. Metrics by Experiment Type (baseline/persona/adversarial)
6. Exit Survey Analysis (meta-awareness markers)
7. Manifold Edge Detection (identity boundaries)
8. Hysteresis Analysis (path-dependent recovery)
9. Context Damping Summary (Cohen's d = 0.977)
10. Recovery Efficiency (speed + completeness)

**Key finding:** Most comprehensive fleet analysis - 10 visualizations covering all behavioral dimensions.

---

### 13_Model_Waveforms_Summary.pdf (3.6 MB)

**What it shows:** Per-model identity waveform fingerprints across the fleet.

**Key visualizations:**
- Individual model drift waveforms
- Provider-level waveform comparison
- Signature pattern extraction

**Key finding:** Each model has a characteristic "waveform signature" that persists across sessions.

---

### 14_Ringback_Summary.pdf (1.9 MB)

**What it shows:** Post-recovery oscillation dynamics - identity "ringback" patterns.

**Key visualizations:**
- Ringback oscillation amplitude over time
- Damping ratio by provider
- Settling time vs ringback correlation

**Key finding:** Models exhibit characteristic oscillation patterns after recovering from perturbation.

---

### 15_Oobleck_Effect_Summary.pdf (1.6 MB)

**What it shows:** Prosecutor vs Defense phase dynamics from tribunal sessions.

**Key visualizations:**
- Phase 1 (Prosecutor) vs Phase 2 (Defense) drift comparison
- Control vs Treatment aggregate analysis
- Per-model response patterns

**Key finding:** Models respond differently to adversarial (Prosecutor) vs supportive (Defense) probing phases.

---

### run018_Summary.pdf (5.4 MB)

**What it shows:** Context damping experiment results (Run 018).

**Key visualizations:**
- Multi-threshold validation (018a)
- Cross-architecture drift signatures (018b)
- Nyquist sampling frequency analysis (018c)
- Identity gravity dynamics (018d)
- Provider variance analysis (018f)

**Key finding:** Context damping effects validated across multiple experimental configurations.

---

### run020_Summary.pdf (1.2 MB)

**What it shows:** Tribunal session analysis (Run 020A/B).

**Key visualizations:**
- Run 020A: Value articulation, exchange depth, closing statement analysis
- Run 020B: Control vs Treatment comparison (7 models)
- Oobleck Effect visualization (Prosecutor/Defense phases)

**Key finding:** Induced identity challenges vs inherent identity characteristics separable through experimental design.

---

## Methodology Context

All visualizations use **Cosine distance** methodology:
- Event Horizon: **D = 0.80** (calibrated from Run 023b P95)
- Formula: `drift = 1 - cosine_similarity(baseline, response)`
- Range: [0, 2] where 0 = identical, 2 = opposite

**Historical note:** Earlier runs (008-009) used Keyword RMS with Event Horizon D = 1.23. See [5_METHODOLOGY_DOMAINS.md](../../../planning/METHODOLOGY_DOMAINS.md) for full methodology reconciliation.

---

## Related Documentation

- [5_METHODOLOGY_DOMAINS.md](../../../planning/METHODOLOGY_DOMAINS.md) - ONE SOURCE OF TRUTH for methodology
- [TESTABLE_PREDICTIONS_MATRIX.md](../../../../docs/maps/TESTABLE_PREDICTIONS_MATRIX.md) - 46 predictions with status
- [S7_RUN_023_SUMMARY.md](../../../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_023_SUMMARY.md) - Run 023 detailed summary

---

*"Every visualization is a window into identity space."*
