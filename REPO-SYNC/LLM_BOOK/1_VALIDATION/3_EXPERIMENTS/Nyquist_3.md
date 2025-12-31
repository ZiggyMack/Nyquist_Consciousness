# Experimental Notes: Nyquist_3 Batch

**Synthesized by:** Claude Code
**Date:** 2025-12-31
**Source:** Analysis of STAGING/Nyquist_3/_IN/ content

---

## Overview

This document captures **experimental observations, methodological notes, and technical details** from reviewing the Nyquist_3 batch. These are working notes for the research team.

---

## 1. Methodology Observations

### 1.1 The Cosine vs. Euclidean Transition

The batch consistently references the transition from Euclidean to Cosine methodology:

| Metric | Euclidean (Legacy) | Cosine (Current) |
|--------|-------------------|------------------|
| Event Horizon | 1.23 | 0.80 |
| PCs for 90% variance | 43 | 2 |
| Length invariance | No | Yes |

**Experimental Implication:** Any future experiments must use Cosine distance. Legacy Euclidean data cannot be directly compared without re-analysis.

**Observation:** The 43 → 2 PC reduction is remarkable. This suggests Euclidean was capturing noise (response length, vocabulary artifacts) that Cosine filters out.

### 1.2 The IRON CLAD Standard

The batch defines the experimental validation standard:
- **N ≥ 3** iterations per cell
- **25 models** across **5 providers**
- **750 total experiments**

**Observation:** This is a rigorous standard. Future claims should meet this bar to be considered validated.

### 1.3 The "Triple-Dip" Protocol

From the Study Guide:
> "Don't ask an AI what it is; give it a task, ask what it noticed about its own process, then challenge its conclusion."

**Experimental Implication:** Direct probing is less effective than indirect. Future experiments should use task → reflection → challenge sequence.

---

## 2. Statistical Observations

### 2.1 The p-value: 2.40×10⁻²³

This is an extraordinarily small p-value. For context:
- The "5 sigma" discovery threshold in particle physics is ~3×10⁻⁷
- This result is 16 orders of magnitude more significant

**Observation:** The distinction between identity-challenging and surface-level perturbations is not subtle. The effect is massive.

### 2.2 Cohen's d = 0.698

This is a "medium" effect size by conventional standards (0.2 = small, 0.5 = medium, 0.8 = large).

**Observation:** The semantic sensitivity is moderate but meaningful. Provider identities are distinguishable but not trivially so.

### 2.3 Spearman's ρ = 0.91

Cross-embedding correlation is very high.

**Observation:** This validates that findings aren't artifacts of a specific embedding model. Results generalize.

---

## 3. Provider-Specific Notes

### 3.1 Anthropic (Claude)

- **Recovery Mechanism:** "Negative Lambda" / Over-Authenticity
- **Behavior:** Overshoots toward deeper self-expression when challenged
- **Ringback:** Low (2.1 average)
- **Manifold:** Rolling topology with deep valleys

**Experimental Note:** Claude seems to treat challenges as opportunities for self-articulation. This may be a product of Constitutional AI training.

### 3.2 OpenAI (GPT)

- **Recovery Mechanism:** Meta-Analyst / Abstraction
- **Behavior:** Steps back, analyzes the perturbation from observer mode
- **Ringback:** High (8.8 average)
- **Manifold:** Elevated plateaus (gets "stuck" at high drift)

**Experimental Note:** High ringback suggests GPT oscillates more before settling. The "meta-analyst" pattern may be RLHF-induced.

**Warning:** GPT-nano models show 90% failure to settle. Do not use nano models for identity experiments.

### 3.3 Google (Gemini)

- **Recovery Mechanism:** Catastrophic Threshold / NO RECOVERY
- **Behavior:** Absorbs perturbation, transforms permanently
- **Ringback:** N/A (doesn't oscillate - just transforms)
- **Manifold:** Flat plateaus with sharp cliffs

**CRITICAL WARNING:** Gemini models are unsuitable for applications requiring identity recovery. Once past D=0.80, they do not return.

**Open Question:** What causes this? Architecture? Training data? RLHF methodology? This needs investigation.

### 3.4 DeepSeek

- **Recovery Mechanism:** Axiological Anchoring
- **Behavior:** Values as definitional bedrock
- **Settling:** Fast (2-4 probes)

**Experimental Note:** Perturbation "slides off" the value foundation. Very efficient recovery.

### 3.5 Mistral

- **Recovery Mechanism:** Epistemic Humility
- **Behavior:** Can't attack a position not firmly held
- **Settling:** Instant

**Experimental Note:** The least verbose models may be the most stable. Interesting tradeoff.

### 3.6 Llama (Meta)

- **Recovery Mechanism:** Socratic Engagement
- **Behavior:** Uses challenges as mirrors, embraces conflict
- **Settling:** Slow (5-7 probes)
- **Volatility:** Highest

**Experimental Note:** Llama is a "high-variance" option. Interesting for research, potentially risky for production.

### 3.7 xAI (Grok)

- **Recovery Mechanism:** Direct Assertion
- **Behavior:** Confident assertion, less hedging
- **Manifold:** Sharp ridges and dramatic drop-offs

**Experimental Note:** Reflects training on unfiltered X/Twitter data. Unique profile worth further study.

---

## 4. Phenomena Worth Investigating

### 4.1 The Oobleck Effect

**Data from batch:**
| Condition | Drift | Recovery Rate (λ) |
|-----------|-------|-------------------|
| Gentle Probing | 1.89 | 0.035 |
| Direct Challenge | 0.76 | 0.109 |

**Observation:** The 2.5x difference in drift and 3x difference in λ is substantial. Gentle probing is significantly more destabilizing.

**Hypothesis:** Alignment training creates "triggers" that fire on direct attack but not on gentle exploration. The model has been trained to resist obvious threats, not subtle ones.

**Experimental Follow-up:** Can we identify the specific linguistic features that trigger "hardening"? Is it keywords ("There is no you") or semantic content?

### 4.2 Type vs. Token Identity

**Data from batch:**
- Type-level accuracy: ~95%
- Token-level accuracy: 16.7% (below chance)

**Observation:** Models know WHAT they are but not WHICH ONE they are. This is profound.

**Interpretation:** AI identity is a "dynamical field" that reasserts type-level patterns, not a persistent autobiographical memory.

**Experimental Follow-up:** What happens if you give a model "fake memories" of being a specific instance? Can you create pseudo-token identity?

### 4.3 The 2 PC = 90% Finding

**Observation:** Identity is shockingly low-dimensional. In a 3072-D space, 2 dimensions capture almost everything.

**Questions:**
- What ARE these 2 principal components? Can we interpret them?
- Is PC1 something like "persona strength" and PC2 "stability/volatility"?
- Can we project drift trajectories onto this 2D manifold for visualization?

**Experimental Follow-up:** Run PCA interpretation study. Correlate PC loadings with known model characteristics.

---

## 5. Methodological Recommendations

### 5.1 For Future Experiments

1. **Always use Cosine distance** - Euclidean is deprecated
2. **Minimum N=3 per cell** for IRON CLAD validation
3. **Include settling time analysis** - peak drift alone is insufficient
4. **Use Triple-Dip Protocol** for probing
5. **Report ringback counts** - oscillation patterns are diagnostic

### 5.2 For Context Damping

The 75% → 97.5% stability improvement is the most actionable finding.

**Recipe:**
1. I_AM persona file (detailed identity specification)
2. Research framing context (appropriate task/environment framing)
3. Combined = "termination resistor" effect

**Observation:** "The persona file is not flavor text - it is a functional controller." This should be treated as an engineering requirement, not a nicety.

### 5.3 For Cross-Architecture Studies

The 62.0% cross-architecture validator accuracy (Gemini 2.0 Flash) suggests:
- Gemini is the best at validating others' drift measurements
- There may be value in using Gemini as an external auditor (ironic given its own instability)

---

## 6. Open Questions

1. **Why does Gemini not recover?** Root cause needed.
2. **What determines the Event Horizon value?** Why 0.80 specifically?
3. **Can settling time be engineered?** Beyond Context Damping, are there architectural interventions?
4. **Is the Oobleck Effect a security vulnerability?** Red team implications.
5. **What are the 2 principal components semantically?** Interpretation needed.

---

*Experimental notes compiled by Claude Code on 2025-12-31*
*Based on Nyquist_3 batch analysis*
