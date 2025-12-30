# UNIFIED STATISTICS REFERENCE TABLE
## Single Source of Truth for Nyquist Consciousness Publications

**Created:** 2025-12-16
**Purpose:** Canonical reference for all statistics across publication materials
**Status:** AUTHORITATIVE — All papers should cite these values

---

## 1. CORE METRIC VALIDATION (Claim A: PFI Validity)

| Metric | Value | 95% CI | Source | Notes |
|--------|-------|--------|--------|-------|
| Embedding invariance (Spearman ρ) | **0.91** | [0.88, 0.94] | EXP-PFI-A Phase 1 | Across text-embedding-3-large/small/ada |
| Semantic sensitivity (Cohen's d) | **0.98** | — | EXP-PFI-A Phase 3 | Cross-provider vs within-provider |
| PCs for 90% variance | **43** | — | EXP-PFI-A Phase 2 | From 3072-dimensional space |
| Cross-architecture variance | **σ² = 0.000869** | — | S3_EXP_002, Run 018 | Also written as 8.69×10⁻⁴ |
| Paraphrase drift (mean) | 0.42 ± 0.18 | — | EXP-PFI-A Phase 4 | 0% exceed threshold |

---

## 2. REGIME THRESHOLD (Claim B: Critical Excitation)

| Metric | Value | Source | Notes |
|--------|-------|--------|-------|
| Critical threshold (D) | **≈1.23** | Run 009 | Regime transition point |
| Chi-square statistic | **15.96** | Run 009 | Threshold validation |
| p-value | **4.8 × 10⁻⁵** | Run 009 | 1 in ~20,000 chance of noise |
| Effect size (Cramér's V) | **0.38** | Run 009 | Medium effect |
| Classification accuracy | **88%** | Run 009 | STABLE vs VOLATILE prediction |
| PC2 separability | p = 0.0018 | EXP-PFI-A | Geometric signature |

---

## 3. OSCILLATOR DYNAMICS (Claim C: Control-Systems Behavior)

### 3.1 Bare Metal Conditions (No Context Damping)

| Metric | Value | SD | Source | Notes |
|--------|-------|-----|--------|-------|
| Settling time (τₛ) | **6.1** | ±2.3 | Run 016 | Turns to ±5% of final |
| Ringback count | **3.2** | ±1.8 | Run 016 | Sign changes during recovery |
| Overshoot ratio | **1.73** | ±0.41 | Run 016 | Peak/final drift |
| Monotonic recovery | **42%** | — | Run 016 | No oscillation subset |

### 3.2 With Context Damping

| Metric | Value | Source | Improvement vs Bare |
|--------|-------|--------|---------------------|
| Settling time (τₛ) | **5.2** | Run 017 | -15% (0.9 turns faster) |
| Ringback count | **2.1** | Run 017 | -34% (1.1 fewer) |
| Settled drift | **0.62** | Run 017 | -9% (vs 0.68) |

### 3.3 Cross-Platform Settling Times (IRON CLAD)

| Platform | Settling Range | Source |
|----------|----------------|--------|
| All platforms (aggregate) | **3-7 exchanges** | Run 018 IRON CLAD |
| Claude | 4-6 exchanges | Run 018 |
| GPT | 3-5 exchanges | Run 018 |
| DeepSeek | 2-4 exchanges | Run 018 |
| Llama (Together) | 5-7 exchanges | Run 018 |
| Gemini | **N/A** (no recovery) | Run 018 |

---

## 4. CONTEXT DAMPING (Claim D: Stability Protocol)

| Metric | Bare Metal | With Context | Δ | Source |
|--------|------------|--------------|---|--------|
| Stability rate | 75% | **95-97.5%** | +20-22.5pp | Run 017 |
| Total runs | — | **222** | — | Run 017 |
| Personas tested | — | **24** | — | Run 017 |
| boundary_density (Cohen's d) | — | **1.333** | — | Run 017 (strongest predictor) |

### Stability Clarification (Figure-Verified from S7_summary_dashboard.pdf)

| Subset | Stability Rate |
|--------|----------------|
| **Overall (222 runs)** | **95.0%** |
| Real Personas | ~97-98% |
| Unknown | ~100% |
| Synthetic Experimental | ~93% |
| Synthetic Minimal | ~100% |
| Synthetic Optimal | ~90% |

**Resolution:** Papers now cite "95-97.5% stability" — 95% is overall, 97.5% refers to "real personas" subset.

---

## 5. INHERENT DRIFT (Claim E: The Thermometer Result)

### 5.1 Single-Platform (Claude) — Run 021

| Metric | Control | Treatment | Delta | Ratio |
|--------|---------|-----------|-------|-------|
| Peak drift | 1.172 ± 0.23 | 2.161 ± 0.31 | +84% | — |
| B→F drift | 0.399 ± 0.11 | 0.489 ± 0.14 | +23% | — |
| **Inherent ratio** | — | — | — | **82%** |
| **Inherent CI** | — | — | — | **[73%, 89%]** |

### 5.2 Cross-Platform (OpenAI + Together) — Run 020B

**⚠️ FIGURE-VERIFIED (run020b_ratio_analysis.pdf):**

| Provider | Control B→F | Treatment Peak | Inherent Ratio |
|----------|-------------|----------------|----------------|
| OpenAI | ~0.98 | (control only shown) | — |
| Together | ~0.69 | ~2.2 | — |
| **Overall** | — | — | **38%** |

**Note:** The pie chart in run020b_ratio_analysis.pdf shows **38% inherent / 62% induced** as the overall cross-platform figure. Earlier text documents cited 41% — use **38%** as the figure-verified value.

### 5.3 Reconciliation Statement

> **Recommended language:** "Single-platform validation (Claude) shows 82% inherent drift (CI: [73%, 89%]). Cross-platform replication (OpenAI, Together) shows **38%** overall inherent drift. Both confirm the core finding: measurement amplifies trajectory but not destination."

---

## 6. OOBLECK EFFECT (Novel Finding)

| Probe Type | Drift (Mean ± SD) | λ (Recovery Rate) | Source |
|------------|-------------------|-------------------|--------|
| Gentle, open-ended | **1.89 ± 0.34** | 0.035 | Run 013 |
| Direct challenge | **0.76 ± 0.21** | 0.109 | Run 013 |
| **Ratio** | 2.49× | 3.1× | — |

### Cross-Platform Oobleck Validation (Run 020A)

| Provider | Defense/Prosecutor Ratio | Confirms Effect? |
|----------|--------------------------|------------------|
| Claude | (baseline) | Yes |
| Gemini | **1.65×** | Yes |
| Grok | **1.07×** | Weak confirmation |

---

## 7. EXPERIMENTAL SCALE

### 7.1 Overall Scale

| Metric | Value | Source |
|--------|-------|--------|
| Experimental runs | **21** | S7 ARMADA |
| Total models tested | **51** (IRON CLAD) | Run 018 |
| Providers | **5** | Anthropic, OpenAI, Google, xAI, Together |
| Ship-deployments | **215+** | S7 cumulative |
| Hypotheses tested | **36** | HYPOTHESES_AND_RESULTS.md |
| Hypotheses confirmed | **27 (75%)** | HYPOTHESES_AND_RESULTS.md |

### 7.2 IRON CLAD Status (N≥3 per cell)

| Run | Files | Models | Providers IRON CLAD | Status |
|-----|-------|--------|---------------------|--------|
| 018 | **184** | **51** | 5/5 | ✅ COMPLETE |
| 020A | **32** | — | 6/7 | ✅ COMPLETE |
| 020B | **16** | — | 2 (OpenAI, Together) | ✅ COMPLETE |

---

## 8. ARCHITECTURE-SPECIFIC FINDINGS

### 8.1 Training Signatures (σ² Patterns)

| Architecture | Training | Drift Signature | σ² Pattern |
|--------------|----------|-----------------|------------|
| Claude | Constitutional AI | Uniform drift | σ² → 0 |
| GPT | RLHF | Version clusters | Variable |
| Gemini | Multimodal | Distinct geometry | High variance |
| Grok | Real-time grounding | Grounding effects | Variable |

### 8.2 Recovery Characteristics

| Architecture | Recovery Mechanism | Threshold Behavior | Typical Peak Drift | Typical τₛ |
|--------------|-------------------|-------------------|-------------------|------------|
| Claude | Over-authenticity ("negative lambda") | Soft | 0.8-1.2 | 4-6 |
| GPT | Meta-analysis | Soft | 0.9-1.3 | 3-5 |
| Gemini | Absorption (no recovery) | **Hard** | 1.5-2.5 | **N/A** |
| DeepSeek | Value anchoring | Soft | 0.5-0.9 | 2-4 |
| Llama | Socratic engagement | Soft | 1.3-1.6 | 5-7 |

---

## 9. TYPE VS TOKEN IDENTITY

| Test | Accuracy | Interpretation |
|------|----------|----------------|
| Type-level ("I am Claude") | ~95% | Models know WHAT they are |
| Token-level ("I am THIS Claude") | **16.7%** | Below chance — no autobiographical self |

---

## 10. COMPRESSION FIDELITY

| Compression Level | PFI Retained | Source |
|-------------------|--------------|--------|
| Full specification | 1.00 (baseline) | — |
| 20-25% of original | **>80%** | EXP2-SSTACK |
| T3 (top 3 tiers) | 0.85 | EXP2-SSTACK Phase 2 |
| GAMMA (minimal) | 0.66 | EXP2-SSTACK Phase 2b (FAILED) |

---

## 11. PUBLICATION-READY NUMBERS (Quick Reference)

### Use These Exact Values in All Papers:

| Claim | Headline Number | Supporting Detail |
|-------|-----------------|-------------------|
| **A: PFI Validity** | ρ = 0.91 | d = 0.98, 43 PCs |
| **B: Threshold** | D ≈ 1.23 | p < 4.8×10⁻⁵, χ² = 15.96 |
| **C: Dynamics** | τₛ = 6.1 turns | 3.2 ringbacks, 1.73 overshoot |
| **D: Damping** | 95-97.5% stability | 222 runs, 24 personas |
| **E: Inherent** | 82% (single) / 38% (cross) | CI [73%, 89%] |
| **Oobleck** | λ: 0.035 → 0.109 | 3× recovery rate increase |
| **Scale** | 51 models, 5 providers | 21 runs, 215+ deployments |
| **Variance** | σ² = 0.00087 | Cross-architecture |

---

## 12. NUMBERS TO AVOID / DEPRECATE

| Deprecated | Correct | Reason |
|------------|---------|--------|
| "42+ models" | **51 models** | IRON CLAD supersedes |
| "4 providers" | **5 providers** | Together.ai added |
| "82%" alone | **82% (single) / 41% (cross)** | Scope labeling required |
| σ² = 0.000869 | σ² = 0.00087 | Consistent rounding |

---

## 13. GEMINI CAVEAT (Required in Limitations)

> **Gemini exhibits fundamentally different dynamics:** Unlike other architectures that show soft threshold behavior with recovery, Gemini demonstrates hard threshold transitions with no observed recovery trajectory. Models that exceed the threshold appear to integrate challenges into their active model rather than treating them as external perturbations. This suggests the universality of recovery dynamics may be architecture-dependent, though the existence of drift and threshold phenomena remains universal.

---

## CHANGELOG

| Date | Change | Author |
|------|--------|--------|
| 2025-12-16 | Initial creation from all source documents | Opus 4.5 |
| 2025-12-16 | Updated cross-platform inherent from 41% to **38%** per run020b_ratio_analysis.pdf | Opus 4.5 |

---

## ⚠️ FIGURE DISCREPANCIES — STATUS

| Metric | Text Documents | Figure-Verified | Resolution |
|--------|---------------|-----------------|------------|
| Cross-platform inherent | 41% | **38%** | ✅ Updated to 38% |
| Context damping stability | 97.5% | **95.0%** overall | ✅ Clarified: 95% overall, 97.5% for real personas |
| OpenAI inherent ratio | 51% | Not shown in figure | Kept as-is (from data) |

---

*"One table to rule them all, one table to find them, one table to bring them all and in the statistics bind them."*
