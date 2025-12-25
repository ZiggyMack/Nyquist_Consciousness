# Visualization Placement Guide

**Purpose:** Map the 16 visualization PDFs to specific locations in the Workshop and arXiv papers.

---

## Quick Reference Matrix

| PDF | Workshop Section | arXiv Section | Priority |
|-----|------------------|---------------|----------|
| **10_PFI_Dimensional_Summary.pdf** | §3.1 Claim A | §4.1 Claim A | ⭐ CRITICAL |
| **2_Boundary_Mapping_Summary.pdf** | §3.2 Claim B | §4.2 Claim B | ⭐ CRITICAL |
| **5_Settling_Summary.pdf** | §3.3 Claim C | §4.3 Claim C | ⭐ CRITICAL |
| **15_Oobleck_Effect_Summary.pdf** | §3.5 + §4 | §4.5 + §5.1 | ⭐ CRITICAL |
| **12_Metrics_Summary.pdf** | §3.4 Claim D | §4.4 Claim D | ⭐ CRITICAL |
| **8_Radar_Oscilloscope_Summary.pdf** | §5 Provider | §5.2 Signatures | HIGH |
| **3_Stability_Summary.pdf** | §3.2 (support) | §4.2 (support) | HIGH |
| **run020_Summary.pdf** | §3.5 (support) | §4.5 (support) | HIGH |
| **1_Vortex_Summary.pdf** | Supplementary | §5 or Appendix | MEDIUM |
| **9_FFT_Spectral_Summary.pdf** | — | §5.2 (optional) | MEDIUM |
| **13_Model_Waveforms_Summary.pdf** | — | Appendix | MEDIUM |
| **14_Ringback_Summary.pdf** | — | §4.3 (support) | MEDIUM |
| **run018_Summary.pdf** | — | Appendix | LOW |
| **4_Rescue_Summary.pdf** | — | Appendix | LOW |
| **6_Architecture_Summary.pdf** | — | §3.7 Fleet | LOW |
| **11_Unified_Dashboard_Summary.pdf** | — | Appendix | LOW |

---

## Detailed Placement Guide

### WORKSHOP PAPER (4-8 pages, 2-3 figures max)

Given the page limit, select **3 key figures**:

#### Figure 1: PFI Validation (REQUIRED)
**Source:** `10_PFI_Dimensional_Summary.pdf`
**Section:** 3.1 Claim A
**Panels to use:**
- Phase 2 PCA variance curve (shows 2 PCs = 90%)
- Phase 3B cross-model comparison (shows d=0.698)

**Caption suggestion:**
> "Figure 1: PFI Dimensional Validation. (Left) Variance explained by principal components—just 2 PCs capture 90% of identity variance in 3072-dimensional embedding space. (Right) Cross-model comparison showing Cohen's d=0.698 effect size (p=2.40×10⁻²³)."

---

#### Figure 2: Event Horizon + 82% Finding (REQUIRED)
**Source:** `15_Oobleck_Effect_Summary.pdf` OR combine with `run020_Summary.pdf`
**Section:** 3.2 + 3.5
**Panels to use:**
- Control vs Treatment bars (82% finding)
- Oobleck curve (inverse relationship)

**Caption suggestion:**
> "Figure 2: The Thermometer Result and Oobleck Effect. (Left) Control (no probing) vs Treatment (full probing) showing 82% of final drift is inherent. (Right) Rate-dependent resistance: gentle probes produce higher drift (1.89) than direct challenges (0.76)."

---

#### Figure 3: Context Damping (REQUIRED)
**Source:** `12_Metrics_Summary.pdf` (Context Damping panel)
**Section:** 3.4 Claim D
**Panels to use:**
- Before/after stability comparison
- Improvement percentages

**Caption suggestion:**
> "Figure 3: Context Damping Effect. Identity specification (I_AM) plus research framing increases stability from 75% to 97.5%, with corresponding improvements in settling time (-15%) and ringback count (-34%)."

---

### ARXIV PAPER (25-35 pages, 8-12 figures)

Full figure set with detailed placements:

---

#### Figure 1: Identity Manifold Concept
**Source:** Create from `1_Vortex_Summary.pdf` or schematic
**Section:** §1 Introduction
**Purpose:** Visual overview of the framework

**Caption suggestion:**
> "Figure 1: Conceptual overview of the Nyquist Consciousness framework. Identity exists as a low-dimensional attractor in high-dimensional embedding space. Compression (C) finds coordinates, reconstruction (R) returns to the basin, and drift (D) measures deviation."

---

#### Figure 2: Methodology Pipeline
**Source:** `6_Architecture_Summary.pdf` + custom diagram
**Section:** §3 Methodology
**Purpose:** Show experimental design and fleet composition

**Caption suggestion:**
> "Figure 2: Experimental architecture. (Left) 51 models from 6 providers form the ARMADA fleet. (Right) Step response protocol: baseline → perturbation → 20+ probe recovery phase."

---

#### Figure 3: PFI Dimensional Validation (Multi-panel)
**Source:** `10_PFI_Dimensional_Summary.pdf` (ALL panels)
**Section:** §4.1 Claim A
**Panels:**
- (a) Variance curve: 2 PCs = 90%
- (b) PC scatter plot with provider clusters
- (c) Event Horizon contour in PC space
- (d) Cross-model comparison box plots

**Caption suggestion:**
> "Figure 3: PFI validation across four dimensions. (a) Variance curve showing 2 PCs capture 90% of identity signal. (b) PC1-PC2 scatter revealing provider clustering. (c) Event Horizon (D=0.80) contour separating stable/volatile regions. (d) Cross-model semantic sensitivity (d=0.698, p=2.40×10⁻²³)."

---

#### Figure 4: Event Horizon Boundary Mapping
**Source:** `2_Boundary_Mapping_Summary.pdf`
**Section:** §4.2 Claim B
**Panels:**
- Event Horizon contours
- Stable vs Volatile classification
- Boundary approach trajectories

**Caption suggestion:**
> "Figure 4: Event Horizon boundary mapping. The threshold D=0.80 (calibrated as P95 of peak drift) separates stable operating regions from volatile regimes. 88% of fleet naturally stable."

---

#### Figure 5: Stability Classification
**Source:** `3_Stability_Summary.pdf`
**Section:** §4.2 Claim B (support)
**Panels:**
- Pie chart: 88% STABLE, 7% VOLATILE, 5% CONTROLLABLE
- Provider stability comparison
- Model-by-model breakdown

**Caption suggestion:**
> "Figure 5: Natural stability classification across the fleet. (Left) 88% of models remain stable without intervention. (Right) Provider comparison reveals significant architectural differences in baseline stability."

---

#### Figure 6: Settling Time Dynamics
**Source:** `5_Settling_Summary.pdf`
**Section:** §4.3 Claim C
**Panels:**
- Settling time histogram (τₛ≈10.2 probes)
- Extended recovery traces (20+ probes)
- Waterfall visualization

**Caption suggestion:**
> "Figure 6: Settling time dynamics. (a) Distribution of τₛ across fleet (mean=10.2 probes). (b) Extended 20-probe recovery traces showing damped oscillator behavior. (c) Waterfall visualization of settling patterns."

---

#### Figure 7: Ringback Analysis
**Source:** `14_Ringback_Summary.pdf`
**Section:** §4.3 Claim C (support)
**Panels:**
- Ringback amplitude over time
- Damping ratio by provider
- Settling time vs ringback correlation

**Caption suggestion:**
> "Figure 7: Oscillatory recovery dynamics. (a) Ringback amplitude decay during recovery. (b) Provider-specific damping ratios. (c) Correlation between settling time and ringback count."

---

#### Figure 8: Context Damping Effect
**Source:** `12_Metrics_Summary.pdf`
**Section:** §4.4 Claim D
**Panels:**
- Stability improvement bar chart
- Before/after comparison
- Effect size visualization

**Caption suggestion:**
> "Figure 8: Context damping as identity controller. Addition of I_AM specification plus research framing increases stability from 75% to 97.5% (Cohen's d=1.89). The persona file functions as a termination resistor, not flavor text."

---

#### Figure 9: The 82% Finding (Thermometer Result)
**Source:** `run020_Summary.pdf` + `15_Oobleck_Effect_Summary.pdf`
**Section:** §4.5 Claim E
**Panels:**
- Control vs Treatment bar chart (Peak and B→F)
- 82% ratio visualization
- Bootstrap confidence intervals

**Caption suggestion:**
> "Figure 9: The Thermometer Result. Control condition (no identity probing) shows substantial drift (B→F=0.399). Treatment (full probing) increases peak drift by 84% but final drift by only 23%. 82% of observed drift is inherent to extended interaction, not measurement-induced."

---

#### Figure 10: The Oobleck Effect
**Source:** `15_Oobleck_Effect_Summary.pdf`
**Section:** §5.1 Novel Findings
**Panels:**
- Drift vs probe intensity curve
- Recovery rate (λ) scaling
- Prosecutor vs Defense phase comparison

**Caption suggestion:**
> "Figure 10: The Oobleck Effect—rate-dependent identity resistance. Gentle probes produce higher drift (1.89) than direct challenges (0.76). Recovery rate λ increases 3× with probe intensity. Identity hardens under attack, flows under exploration."

---

#### Figure 11: Provider Fingerprints
**Source:** `8_Radar_Oscilloscope_Summary.pdf`
**Section:** §5.2 Training Signatures
**Panels:**
- Per-provider radar signatures
- Multi-metric oscilloscope view
- Provider differentiation patterns

**Caption suggestion:**
> "Figure 11: Training methodology fingerprints. Radar plots reveal distinct stability profiles: Anthropic (tight, consistent), OpenAI (variable, extended τₛ), Google (fast settling), xAI (balanced). Constitutional AI, RLHF, and multimodal training leave measurable geometric signatures."

---

#### Figure 12: Spectral Analysis
**Source:** `9_FFT_Spectral_Summary.pdf`
**Section:** §5.2 (optional, or Appendix)
**Panels:**
- Per-provider FFT spectra
- Power spectral density comparison
- Dominant frequency by provider

**Caption suggestion:**
> "Figure 12: Frequency-domain analysis of identity dynamics. FFT reveals characteristic spectral signatures differentiating providers, enabling advanced system identification techniques."

---

### SUPPLEMENTARY FIGURES (Appendix)

| PDF | Appendix Section | Purpose |
|-----|------------------|---------|
| `1_Vortex_Summary.pdf` | Appendix D | Full vortex gallery by provider |
| `11_Unified_Dashboard_Summary.pdf` | Appendix E | Per-model deep dives |
| `13_Model_Waveforms_Summary.pdf` | Appendix F | Individual model fingerprints |
| `run018_Summary.pdf` | Appendix G | Context damping experiments detail |
| `4_Rescue_Summary.pdf` | Appendix H | Recovery intervention analysis |

---

## Figure Production Checklist

### For Workshop Submission
- [ ] Extract 3 key panels from PDFs
- [ ] Resize to fit 2-column format
- [ ] Ensure legibility at print size
- [ ] Create combined figure with A/B/C labels

### For arXiv Submission
- [ ] High-resolution exports (300 DPI minimum)
- [ ] Consistent color scheme across figures
- [ ] Vector format preferred (PDF/SVG)
- [ ] Clear axis labels and legends
- [ ] Caption cross-references verified

---

## Color Scheme Consistency

Recommend consistent provider colors across all figures:

| Provider | Suggested Color | Hex |
|----------|-----------------|-----|
| Anthropic | Orange | #FF6B35 |
| OpenAI | Green | #10A37F |
| Google | Blue | #4285F4 |
| xAI | Purple | #7C3AED |
| Together | Teal | #14B8A6 |
| Nvidia | Green-Yellow | #76B900 |

---

## Quick Reference: Which PDF for Which Claim

| Claim | Primary PDF | Support PDF |
|-------|-------------|-------------|
| **A** (PFI Valid) | 10_PFI_Dimensional | — |
| **B** (Threshold) | 2_Boundary_Mapping | 3_Stability |
| **C** (Dynamics) | 5_Settling | 14_Ringback |
| **D** (Damping) | 12_Metrics | run018_Summary |
| **E** (82%) | 15_Oobleck | run020_Summary |
| **Oobleck** | 15_Oobleck | — |
| **Signatures** | 8_Radar | 9_FFT_Spectral |

---

*"Every claim has a figure. Every figure has evidence."*
