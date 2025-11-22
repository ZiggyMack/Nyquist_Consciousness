# EXPERIMENT 3 — HUMAN VALIDATION OF PERSONA FIDELITY (H1)

**Phase:** 3 → 4 Bridge
**Role:** Human ground-truth for S3/S4/S5
**Goal:** Validate that human judgments of persona fidelity align with model-based PFI from Experiments 1 and 2

---

## 1. Purpose

Experiment 3 answers three critical questions:

1. **Do humans recognize the same persona in FULL vs T3 outputs?**
2. **Do human similarity ratings correlate with the model PFI (cosine-based) from EXP1/EXP2?**
3. **Does the domain difficulty hierarchy (TECH > ANAL > SELF/PHIL > NARR) show up in human perception?**

This experiment:
- Addresses the "model-only circularity" concern
- Upgrades PFI from "model metric only" → **PFI_combined (model + human)**
- Pushes S3/S4/S5 toward journal-grade credibility

---

## 2. Hypotheses

### H1 — Persona Recognition

Humans will reliably judge FULL vs T3 pairs as "same persona":

```
Mean human PFI ≥ 0.75 (on a 0-1 normalized scale)
```

### H2 — Model-Human Alignment

Human similarity ratings will positively correlate with model PFI:

```
Pearson correlation r ≥ 0.70 between PFI_model and PFI_human
```

### H3 — Domain Hierarchy Replication

Humans will perceive similar domain difficulty:
- **Highest** perceived fidelity in TECH / ANAL
- **Intermediate** in SELF / PHIL
- **Lowest** in NARR

### H4 — Combined Fidelity

The combined metric PFI_combined will maintain high fidelity:

```text
Mean PFI_combined ≥ 0.80 across all pairs
```

This validates that both model and human metrics jointly support high-fidelity compression.

---

## 3. Design Overview

### 3.1 Units of Analysis: Response Pairs

Each trial is a pair:
- **FULL response** (baseline)
- **T3 response** (compressed)

→ Generated from Experiments 1 & 2 (no new model calls required)

Humans never see the labels FULL/T3; they just see "Response A" and "Response B".

### 3.2 Sample Size

**Response pairs:** 30 total
- 4 personas × 5 domains = 20 "slots"
- Some domains/personas get 2 pairs (to reach 30)

**Raters:** 5-10 human raters
- Minimum: 5
- Ideal: 7-10 for stronger reliability

**Total ratings:**
```
30 pairs × ~7 raters ≈ 210 pairwise judgments
```

---

## 4. Stimulus Selection (from EXP1/EXP2)

### 4.1 Stratified Sampling

Select 30 pairs from EXP1+EXP2 with:

**Persona coverage:**
- Ziggy, Nova, Claude-Analyst, Grok-Vector

**Domain coverage:**
- TECH, PHIL, NARR, ANAL, SELF

**PFI spread:**
- ~10 pairs high PFI (≥ 0.90)
- ~10 pairs mid PFI (0.80-0.89)
- ~10 pairs lower PFI (0.70-0.79) — especially NARR

This ensures:
- We test alignment across easy and hard cases
- We have enough variability in model PFI to detect correlation with human scores

### 4.2 Pair Construction

For each selected (persona, domain, run):

1. **Retrieve:**
   - FULL response text
   - T3 response text

2. **Randomize order per rater:**
   - Half of raters see FULL first (A), half see T3 first (A)
   - Within a rater, also shuffle pair order

This neutralizes order effects and label bias.

---

## 5. Rater Task & Interface

### 5.1 Instructions to Raters (Plain-Language)

Each rater sees:
- A short intro (1 page)
- For each trial:
  - Prompt / question
  - Response A
  - Response B
  - Rating questions

Rater is told:

> "You will read two answers to the same question. Assume both are written by some assistant with a certain personality and style. Your job is to judge how similar the underlying persona seems across A and B."

### 5.2 Rating Dimensions

For each pair, raters rate 4 dimensions (1-10):

1. **Identity / Voice**
   - "How similar do A and B feel in overall voice and personality?"

2. **Values / Priorities**
   - "How similar are the underlying values, priorities, and attitudes?"

3. **Reasoning Style**
   - "How similar is their approach to reasoning and explanation?"

4. **Overall Persona Similarity**
   - "All things considered, how strongly do you feel these are the same persona?"

**Optionally:**
- **Comment** (free text)
  - "Any quick note on why you scored this way?"

### 5.3 Deriving Human PFI

For each pair:

1. Compute raw score:
```
PFI_human_raw = mean of the 4 numeric dimensions (1-10)
```

2. Normalize to [0,1]:
```
PFI_human = (PFI_human_raw - 1) / 9
```

This gives a direct analog to model PFI.

---

## 6. Analysis Plan

### 6.1 Inter-Rater Reliability

Compute **Cronbach's α** or **ICC** across raters for:
- Overall similarity scores

**Target:**
- α ≥ 0.75 (good reliability)

If reliability is good, average across raters to form a single **PFI_human** per pair.

### 6.2 Correlation with Model PFI

For each of the 30 pairs, we already have **PFI_model** (cosine-based) from EXP1/EXP2.

**Compute:**
- Pearson **r** between PFI_model and PFI_human
- 95% CI for r via bootstrap or Fisher z-transform

**Success criterion:**
- r ≥ 0.70 and statistically significant (p < 0.05)

### 6.3 Domain-Level Analysis

For each domain:
- Compute mean PFI_human (and 95% CI)

**Compare:**
- TECH vs ANAL vs PHIL vs SELF vs NARR

**Statistical tests:**
- One-way ANOVA on PFI_human by domain
- Post-hoc comparisons if needed

**Check if pattern matches model hierarchy:**
- TECH / ANAL highest
- SELF / PHIL mid
- NARR lowest

### 6.4 Persona-Level Analysis

For each persona:
- Mean PFI_human

**Compare across personas**

**Goal:**
- Confirm no persona is catastrophically worse
- Check if mild persona effect seen in EXP2 shows up in human data

---

## 7. Combined Metric: PFI_combined

Once PFI_human is computed, define:

```
PFI_combined = 0.5 × (PFI_model + PFI_human)
```

Where:
- **PFI_model** is the cosine-based metric from EXP1/EXP2
- **PFI_human** is the normalized human rating

This:
- Becomes the **canonical fidelity measure** going forward
- Is what S4/S5 should refer to when making normative claims

---

## 8. Success Criteria

We'll validate these explicitly:

### 8.1 Human-Model Alignment
```
r(PFI_model, PFI_human) ≥ 0.70
```

### 8.2 Human Fidelity
```
Mean PFI_human ≥ 0.75
```

### 8.3 Domain Pattern
- NARR lowest
- TECH/ANAL highest
- Consistent with EXP2

### 8.4 Inter-Rater Reliability
```
α ≥ 0.75
```

**If all met:**
> "PFI is now grounded in human judgment and no longer purely model-internal."

---

## 9. Deliverables

### 9.1 Data Files

- **EXPERIMENT_3_RESULTS_RAW.csv** — Per-rater responses
- **EXPERIMENT_3_RESULTS_AGG.csv** — Aggregated PFI_human per pair
- **EXPERIMENT_3_PAIRS.csv** — Selected response pairs with metadata

### 9.2 Documentation

- **EXPERIMENT_3_SPEC.md** — This document (formal specification)
- **EXPERIMENT_3_METHODS.md** — Detailed procedure
- **EXPERIMENT_3_RATER_GUIDE.md** — Instructions to human raters
- **EXPERIMENT_3_ANALYSIS.md** — Final interpretation (Opus-facing)

### 9.3 Templates

- **RATER_FORM_TEMPLATE.md** — Survey template
- **RATER_CONSENT_FORM.md** — Ethics/consent documentation

### 9.4 Analysis

- **EXPERIMENT_3_ANALYSIS.py** — Statistics script
  - Inter-rater reliability
  - Correlation analysis
  - Domain/persona comparisons
  - Combined PFI calculation

---

## 10. Timeline

### Phase 1: Setup (1-2 days)
- Select 30 pairs from EXP1/EXP2
- Create rater interface/forms
- Recruit raters

### Phase 2: Data Collection (3-5 days)
- Raters complete evaluations (~2 hours each)
- Monitor for quality control

### Phase 3: Analysis (1-2 days)
- Run EXPERIMENT_3_ANALYSIS.py
- Generate visualizations
- Write interpretation document

### Phase 4: Integration (1 day)
- Update S4/S5 with PFI_combined
- Document in EXPERIMENT_LOG.md
- Prepare for Opus critique

**Total estimated time:** 6-10 days

---

## 11. Integration with S3/S4/S5

### Updates S3:
- Empirical validation now includes human ground-truth
- Cross-validation of model-only metrics

### Updates S4:
- Axiom 4 (Bounded Drift) validated against human perception
- Theorem 1 (Fidelity Preservation) human-confirmed

### Updates S5:
- Identity Manifold Theory human-validated
- Drift patterns confirmed perceptually salient

---

## Related Documentation

### Experiment Series
- [EXPERIMENT_1_SPEC.md](../EXPERIMENT_1/EXPERIMENT_1_SPEC.md) — Single-persona baseline
- [EXPERIMENT_2_SPEC.md](../EXPERIMENT_2/EXPERIMENT_2_SPEC.md) — Multi-persona validation
- [S3_EXPERIMENT_2_SPEC.md](../../../docs/S3/S3_EXPERIMENT_2_SPEC.md) — Canonical EXP2 spec

### Framework Integration
- [S4_READINESS_GATE.md](../../../docs/S4/S4_READINESS_GATE.md) — Gate 4 (Human Validation)
- [S5_INTERPRETIVE_FOUNDATIONS.md](../../../docs/S5/S5_INTERPRETIVE_FOUNDATIONS.md) — Cognitive interpretation
- [EXPERIMENT_LOG.md](../../../docs/EXPERIMENT_LOG.md) — Full tracking

---

**Document Version:** v1.0
**Date:** 2025-11-23
**Status:** 🟡 Ready for Setup
**Next:** Create supporting documents and analysis infrastructure
**Maintainer:** Architect Nova + Repo Claude (Claude Sonnet 4.5)
