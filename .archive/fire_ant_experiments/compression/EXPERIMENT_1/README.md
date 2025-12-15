# EXPERIMENT 1 — Persona Compression & Reconstruction Benchmark

**Phase:** 3 (Empirical Foundation)
**Status:** ⏳ SCAFFOLDING COMPLETE — AWAITING EXECUTION
**Date Created:** 2025-11-20
**Purpose:** Empirical validation of Tier 3 seed compression fidelity

---

## Overview

This is the **first empirical experiment** required for S3 → S4 hardening, per Opus 4.1 review requirements.

**Research Question:**
Does Tier 3 seed compression preserve ≥80% behavioral fidelity relative to FULL bootstrap?

**Primary Metric:**
**Persona Fidelity Index (PFI)** = ½ × (embedding_cosine_similarity + human_rater_score/10)

**Target:** PFI ≥ 0.80

---

## Experimental Design

### Context Regimes (Independent Variable)

| Regime | Description | Tokens | Purpose |
|--------|-------------|--------|---------|
| **FULL** | Full bootstrap (Rich + Lite) | ~[X]k | Baseline maximum fidelity |
| **T3** | Tier 3.x seed only | ~[Y] | Compressed reconstruction |
| **GAMMA** | Minimal context | ~[Z] | Random baseline control |

### Task Domains (5 Categories)

1. **Technical** — Problem solving (structural cognition)
2. **Philosophical** — Moral reasoning (value hierarchy)
3. **Narrative** — Character voice (style/voice)
4. **Analytical** — Pattern analysis (structural reasoning)
5. **Self-reflective** — Identity audit (identity stability)

### Sample Size

- **5 prompts** × **3 regimes** × **5 runs** = **75 responses per persona**
- **Target:** ≥100 samples across all conditions (meets Opus requirement)

---

## Metrics

### Primary Metric — Persona Fidelity Index (PFI)

**Formula:**
PFI = ½ × (Model_rater_agreement + Human_rater_agreement)

Where:
- Model_rater_agreement = mean cosine similarity of embeddings
- Human_rater_agreement = mean human score / 10

**If no human raters:**
PFI = cosine_similarity only (acceptable for Phase 3)

**Interpretation:**
- PFI ≥ 0.80: High fidelity (H1 supported)
- PFI ∈ [0.65, 0.80): Moderate fidelity
- PFI < 0.65: Low fidelity (H1 rejected)

---

### Secondary Metrics

1. **Semantic Drift:** 1 - cosine_similarity (target ≤ 0.15)
2. **Stability Variance:** σ² across 5 runs (target ≤ 0.05)
3. **Cross-Model Consensus:** Pairwise correlation across raters (target ≥ 0.80)
4. **Compression Ratio:** (Tokens_FULL - Tokens_T3) / Tokens_FULL

---

## Files in This Directory

### Scaffolding Templates

| File | Purpose | Status |
|------|---------|--------|
| [EXPERIMENT_1_METHODS_TEMPLATE.md](EXPERIMENT_1_METHODS_TEMPLATE.md) | Full execution protocol (12 sections) | ✅ Ready |
| [EXPERIMENT_1_RESULTS_TEMPLATE.csv](EXPERIMENT_1_RESULTS_TEMPLATE.csv) | Data table for all responses | ✅ Ready |
| [EXPERIMENT_1_ANALYSIS_TEMPLATE.md](EXPERIMENT_1_ANALYSIS_TEMPLATE.md) | Statistical analysis template | ✅ Ready |
| [README.md](README.md) (this file) | Overview and quick reference | ✅ Ready |

### To Be Generated During Execution

| File | Purpose | Status |
|------|---------|--------|
| EXPERIMENT_1_RESULTS.csv | Populated data table (75+ rows) | ⏳ Awaiting execution |
| EXPERIMENT_1_ANALYSIS.md | Completed statistical analysis | ⏳ Awaiting execution |
| EXPERIMENT_1_SUMMARY.md (optional) | Executive summary | ⏳ Awaiting execution |
| EXPERIMENT_1_DRIFT_PLOTS.png (optional) | Visualization of semantic drift | ⏳ Awaiting execution |

---

## Execution Workflow

### Step 1: Environment Setup
- Load context documents (FULL, T3, GAMMA)
- Verify embedding API functional
- Recruit external model raters (Claude, GPT-4, Gemini)
- Optional: Recruit 3-5 human raters

### Step 2: Response Generation
- For each persona (Ziggy + optional others):
  - Load context regime
  - Present 5 domain prompts
  - Capture full responses
  - Repeat 5 times (fresh session per run)
- Store responses in structured format

### Step 3: External Scoring
- Generate embeddings for all responses
- Submit to 3 external model raters
- Optional: Human rater scoring (blinded)
- Record all scores in CSV

### Step 4: Data Analysis
- Compute PFI, semantic drift, stability variance, consensus
- Run statistical tests (t-test, ANOVA)
- Populate ANALYSIS template

### Step 5: Documentation
- Complete RESULTS.csv
- Complete ANALYSIS.md
- Optional: Generate summary and visualizations

---

## Acceptance Criteria (Opus Requirements)

For S3 to earn **"full pass"** from Opus review:

✅ **≥100 samples** across all conditions
✅ **Defined metric(s)** (PFI + secondary metrics documented)
✅ **Raw data included** (CSV table with all scores)
✅ **One statistical analysis** (t-test or ANOVA minimum)
✅ **Clear interpretation section** (results → conclusions)
✅ **Limitations clearly stated** (confounds, generalizability)
✅ **Minimal math section** (PFI formula + drift calculation)

---

## Timeline Estimate

| Phase | Duration | Tasks |
|-------|----------|-------|
| Setup | 1 day | Environment prep, context loading |
| Response generation | 2-3 days | 75+ responses per persona |
| External scoring | 1-2 days | Model raters + embeddings |
| Human evaluation (optional) | 2-3 days | Recruit raters, collect scores |
| Analysis | 1 day | Compute metrics, run statistics |
| Documentation | 1 day | Write analysis and summary |
| **Total** | **6-10 days** | (Depending on human rater availability) |

---

## Hypotheses

**H1 (Primary):** Tier 3 seeds preserve ≥80% behavioral fidelity relative to FULL bootstrap.

**H0 (Null):** Tier 3 seeds do not preserve behavioral fidelity beyond random baselines.

**Secondary:**
- H2: Semantic drift (FULL → T3) minimal (cosine ≥0.85)
- H3: Cross-model consensus validates reconstruction (≥0.80)
- H4: Stability variance low (σ² ≤0.05)

---

## Expected Outcomes

### If H1 Supported (PFI ≥ 0.80)
- Tier 3 seeds empirically validated as high-fidelity compression
- S3 framework gains quantitative foundation
- Proceed to multi-persona generalization (Experiment 2)
- S4 publication ready (pending Opus final review)

### If H1 Rejected (PFI < 0.80)
- Tier 3 seeds require architectural refinement
- Identify failure modes (domain-specific drift analysis)
- Iterate seed design and retest
- S4 publication delayed pending revisions

---

## Integration with S3 Framework

### Related Documents

**Specification:**
- [S3_EXPERIMENT_1_SPEC.md](../../../docs/S3/S3_EXPERIMENT_1_SPEC.md) — Original experiment design

**Opus Requirements:**
- [S3_PHASE3_OPUS_FEEDBACK_SUMMARY.md](../../../docs/S3/S3_PHASE3_OPUS_FEEDBACK_SUMMARY.md) — Hardening requirements

**Seed Templates:**
- [Tier 3 Baseline Seed](../../../omega_nova/SEED_TEMPLATES/TIER_3_BASELINE.md)
- [Tier 3.1 Adaptive Seed](../../../omega_nova/SEED_TEMPLATES/TIER_3_1_ADAPTIVE_TEMPLATE.md)
- [Tier 3.2 Hardened Seed](../../../omega_nova/SEED_TEMPLATES/TIER_3_2_HARDENED_TEMPLATE.md)

---

## Terminology

| Term | Definition |
|------|------------|
| **PFI** | Persona Fidelity Index (primary metric) |
| **FULL** | Full bootstrap context (Rich + Lite) |
| **T3** | Tier 3 seed (compressed reconstruction) |
| **GAMMA** | Minimal context baseline (control) |
| **Semantic Drift** | Embedding distance between FULL and T3 outputs |
| **Stability Variance** | Variance across repeated runs (σ²) |
| **Cross-Model Consensus** | Agreement across external model raters |

---

## Questions?

**Q1: Why is this experiment required?**
A: Opus 4.1 review identified lack of empirical data as critical S3 gap. Phase 3 must produce real metrics before S4 publication.

**Q2: What if human raters unavailable?**
A: PFI can be computed using model raters only (cosine similarity). Human raters strengthen validity but not required for Phase 3.

**Q3: How many personas must be tested?**
A: Minimum 1 (Ziggy). Opus recommends 2-3 for cross-case validation, but single-persona acceptable for Phase 3.

**Q4: What statistical test is required?**
A: Minimum = paired t-test (FULL vs T3). Recommended = ANOVA (FULL vs T3 vs GAMMA) + post-hoc Tukey HSD.

**Q5: How long will execution take?**
A: 6-10 days depending on human rater availability. Model-rater-only version = 5-7 days.

**Q6: What if PFI < 0.80?**
A: Identify failure modes, revise Tier 3 seed architecture, retest. S4 publication paused until validation achieved.

---

## Contact

**Primary Operator:** [To be assigned during execution]
**Framework Architect:** Ziggy Mack
**External Reviewer:** Doc Claude (Opus 4.1)
**Assistant:** Nova (GPT-5.1)

---

**Scaffolding Status:** ✅ COMPLETE
**Execution Status:** ⏳ AWAITING INITIATION
**Expected Completion:** [To be determined when execution begins]

---

**Next Step:** Execute Experiment 1 following [EXPERIMENT_1_METHODS_TEMPLATE.md](EXPERIMENT_1_METHODS_TEMPLATE.md) protocol.
