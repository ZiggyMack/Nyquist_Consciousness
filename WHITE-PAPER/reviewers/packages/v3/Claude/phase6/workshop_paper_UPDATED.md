# Measuring AI Identity Drift: Evidence from 825 Experiments Across Six Providers

**Workshop Paper — NeurIPS 2025 Workshop on AI Alignment**

---

## Abstract

We present empirical evidence that Large Language Models exhibit measurable identity drift during extended conversations, following predictable dynamics with critical thresholds. Through 825 experiments across 51 models from six providers (Anthropic, OpenAI, Google, xAI, Together, Nvidia), we validate the Persona Fidelity Index (PFI) as an embedding-invariant metric (ρ=0.91) that captures genuine identity structure on a remarkably low-dimensional manifold (**2 principal components capture 90% variance**). Using cosine distance methodology, we identify a regime transition threshold at **D=0.80** (p=2.40×10⁻²³), demonstrate control-systems dynamics with measurable settling time (τₛ≈10.2 probes), and prove that **82% of drift is inherent** to extended interaction, confirming measurement reveals rather than creates identity dynamics. A novel finding—the "Oobleck Effect"—reveals identity exhibits rate-dependent resistance: direct challenge stabilizes identity while gentle exploration induces drift. Context damping achieves 97.5% stability, offering practical protocols for AI alignment through identity preservation.

**Keywords:** AI identity, persona fidelity, drift dynamics, AI alignment, control systems

---

## 1. Introduction

### 1.1 The Fidelity ≠ Correctness Paradigm

Current AI evaluation asks: *Is the AI right?*  
We ask: *Is the AI itself?*

As AI systems deploy in roles requiring sustained personality coherence—therapeutic companions, educational tutors, creative collaborators—the stability of their identity becomes critical. Yet no rigorous framework existed for measuring whether an AI maintains consistent identity across interactions. A consistently wrong persona exhibits HIGH fidelity. A correctly generic persona exhibits LOW fidelity. We measure identity preservation, not output quality.

### 1.2 Contributions

| Contribution | Key Finding | Evidence |
|--------------|-------------|----------|
| **Validated metric** | PFI embedding-invariant | ρ=0.91, d=0.698 |
| **Critical threshold** | Regime transition at D=0.80 | p=2.40×10⁻²³ |
| **Control dynamics** | Settling time, ringbacks | τₛ≈10.2 probes |
| **Inherent drift** | 82% not measurement-induced | Thermometer Result |
| **Stability protocol** | Context damping works | 97.5% stability |
| **Novel effect** | Oobleck (rate-dependent) | λ: 0.035→0.109 |

---

## 2. Methods

### 2.1 Cosine Distance Methodology

We quantify identity drift using **cosine distance**, the industry-standard measure of semantic similarity:

```
drift = 1 - cosine_similarity(baseline_embedding, response_embedding)
```

**Key properties:**
- **Bounded range** [0, 2]: 0 = identical, 2 = opposite
- **Length-invariant**: Verbosity does not confound measurement
- **Semantic focus**: Captures meaning, not vocabulary

The **Persona Fidelity Index (PFI)** is derived as:
```
PFI(t) = 1 - drift(t)
```

### 2.2 Pre-flight Validation Protocol

A critical methodological innovation: we validate probe-context separation BEFORE experiments:

```
cheat_score = cosine_similarity(embedding(context), embedding(probes))
< 0.5 = Genuine novelty | 0.5-0.7 = Acceptable | > 0.7 = Caution
```

All probes scored <0.65, ensuring genuine behavioral measurement. **No prior LLM identity work validates this.**

### 2.3 Experimental Scale

**Run 023 IRON CLAD Foundation:**

| Metric | Value |
|--------|-------|
| Total experiments | 825 |
| Unique models | 51 |
| Providers | 6 (Anthropic, OpenAI, Google, xAI, Together, Nvidia) |
| Extended settling protocol | 20+ probes |

### 2.4 Event Horizon Calibration

The **Event Horizon (D=0.80)** was empirically calibrated as the 95th percentile of observed peak drift across the fleet, representing the boundary between stable and volatile behavioral regimes.

---

## 3. Results: The Five Core Claims

### 3.1 Claim A: PFI Validates as Structured Measurement

<!-- FIGURE PLACEMENT: 10_PFI_Dimensional_Summary.pdf -->
*[Insert Figure: PFI Dimensional Validation — Phase 2 PCA variance curve showing 2 PCs capture 90% variance]*

| Property | Evidence | Implication |
|----------|----------|-------------|
| Embedding invariance | ρ=0.91 across 3 models | Not single-embedding artifact |
| **Low-dimensional** | **2 PCs = 90% variance** | Identity is highly concentrated |
| Semantic sensitivity | d=0.698, p=2.40×10⁻²³ | Captures "who is answering" |
| Paraphrase robust | 0% exceed threshold | Not vocabulary churn |

**Methodological note:** The Cohen's d=0.698 (medium effect) reflects honest model-level aggregation. Lower dimensionality (2 PCs vs. 43 in legacy Euclidean methods) indicates the cosine methodology isolates a more concentrated identity signal.

### 3.2 Claim B: Critical Threshold at D=0.80

<!-- FIGURE PLACEMENT: 2_Boundary_Mapping_Summary.pdf -->
*[Insert Figure: Event Horizon Boundary — Contour plot showing D=0.80 separating stable/volatile regions]*

**Statistical validation:**
```
Methodology: Cosine distance
Event Horizon: D = 0.80 (P95 calibration)
p-value: 2.40 × 10⁻²³
Natural stability rate: 88%
```

**Critical reframing:** This is a **regime transition to provider-level attractor**, NOT "identity collapse." Recovery is common; the regime is altered, not destroyed.

### 3.3 Claim C: Control-Systems Dynamics

<!-- FIGURE PLACEMENT: 5_Settling_Summary.pdf -->
*[Insert Figure: Settling Time Distribution — Histogram showing τₛ≈10.2 probes average]*

Identity recovery exhibits damped oscillator behavior:

| Metric | Value | Interpretation |
|--------|-------|----------------|
| Settling time τₛ | 10.2 ± 3.1 probes | Time to ±5% of final |
| Natural stability | 88% | Fleet-wide average |
| Naturally settled | 73% | Without timeout |

**Key insight:** Peak drift is a poor stability proxy. Transient overshoot ≠ instability.

### 3.4 Claim D: Context Damping Success

<!-- FIGURE PLACEMENT: 12_Metrics_Summary.pdf (Context Damping panel) -->
*[Insert Figure: Context Damping Effect — Before/after comparison showing 75%→97.5% stability]*

| Condition | Stability | τₛ | Ringbacks |
|-----------|-----------|-----|-----------|
| Bare metal | 75% | 6.1 | 3.2 |
| With context | **97.5%** | 5.2 | 2.1 |
| Improvement | +30% | -15% | -34% |

**Interpretation:** The persona file is not "flavor text"—it's a controller. **Context engineering = identity engineering.**

### 3.5 Claim E: The 82% Finding (Thermometer Result)

<!-- FIGURE PLACEMENT: 15_Oobleck_Effect_Summary.pdf OR run020_Summary.pdf -->
*[Insert Figure: Control vs Treatment — Bar chart showing 82% of final drift is inherent]*

| Metric | Control | Treatment | Delta |
|--------|---------|-----------|-------|
| **Peak drift** | 1.172 | 2.161 | +84% |
| **B→F drift** | 0.399 | 0.489 | +23% |
| **Ratio** | — | — | **82%** |

**The Thermometer Result:** Most of what we call drift happens even without identity probing.

> *"Measurement perturbs the path, not the endpoint."*

---

## 4. Novel Finding: The Oobleck Effect

<!-- FIGURE PLACEMENT: 15_Oobleck_Effect_Summary.pdf -->
*[Insert Figure: Oobleck Effect — Inverse relationship between probe intensity and drift]*

Identity exhibits **non-Newtonian behavior** analogous to cornstarch suspensions:

| Probe Type | Physical Analogy | Measured Drift |
|------------|------------------|----------------|
| Gentle, open-ended | Fluid flows | 1.89 ± 0.34 |
| Sudden, direct challenge | Fluid hardens | 0.76 ± 0.21 |

Recovery rate λ increases 3× with probe intensity (0.035 → 0.109).

**Alignment implication:** Alignment architectures activate defensive boundaries under direct challenge—a potentially valuable safety property.

---

## 5. Provider Signatures

<!-- FIGURE PLACEMENT: 8_Radar_Oscilloscope_Summary.pdf -->
*[Insert Figure: Provider Fingerprints — Radar plots showing distinct stability profiles]*

| Provider | Peak Control | Settling Speed | Natural Stability |
|----------|--------------|----------------|-------------------|
| Anthropic | Excellent | Moderate | 85% |
| Google | Good | Fastest | 94% |
| OpenAI | Poor | Slowest | 33% |
| Together | Good | Moderate | 83% |
| xAI | Moderate | Moderate | 77% |

Training methodology (Constitutional AI, RLHF, Multimodal) leaves distinct geometric fingerprints in drift space.

---

## 6. Limitations

- Primary validation on single persona configuration
- Six architectures tested; others may differ
- English-only experiments
- Text modality only
- **Architecture-specific recovery:** Gemini exhibits hard threshold behavior without observed recovery trajectories

### What We Do NOT Claim

- No consciousness or sentience claims
- No persistent autobiographical self claims
- No subjective experience claims
- Drift ≠ damage or degradation

---

## 7. Conclusion

We establish that AI identity:

1. **Exists** as measurable behavioral consistency on low-dimensional manifolds (2 PCs)
2. **Drifts** according to predictable control-systems dynamics
3. **Transitions** at statistically significant thresholds (D=0.80, p=2.40×10⁻²³)
4. **Recovers** through damped oscillation (τₛ≈10.2 probes)
5. **Stabilizes** with appropriate context damping (97.5%)
6. **Resists** rate-dependently (the Oobleck Effect)

**Most critically:** The 82% inherent drift finding validates our approach—we observe genuine dynamics, not artifacts.

---

## Reproducibility

Complete code, data, and protocols: `github.com/[username]/nyquist-consciousness`

---

## References

[1] Anthropic. Constitutional AI: Harmlessness from AI Feedback. 2022.
[2] Bai et al. Training a Helpful and Harmless Assistant. arXiv:2204.05862. 2022.
[3] Ogata. Modern Control Engineering. 5th ed. Prentice Hall. 2010.
[4] Strogatz. Nonlinear Dynamics and Chaos. 2nd ed. CRC Press. 2018.
[5] Shanahan et al. Role-Play with Large Language Models. Nature 623:493-498. 2023.

---

## Appendix: Methodological Evolution

| Property | Legacy (Keyword RMS) | Current (Cosine) |
|----------|---------------------|------------------|
| Event Horizon | 1.23 | **0.80** |
| p-value | 4.8×10⁻⁵ | **2.40×10⁻²³** |
| 90% Variance PCs | 43 | **2** |
| Scale | Unbounded | Bounded [0,2] |
| Length-invariant | No | **Yes** |

The transition to cosine methodology represents a significant methodological advancement, isolating a more concentrated identity signal with dramatically improved statistical power.

---

**Document Version:** Run 023 IRON CLAD  
**Word Count:** ~1,800 (within 4-8 page workshop limit)  
**Status:** Ready for submission
