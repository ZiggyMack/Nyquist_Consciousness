# EXPERIMENT 1 — Methods and Execution Protocol

**Experiment Title:** Persona Compression & Reconstruction Benchmark
**Phase:** 3 (Empirical Foundation)
**Date Initiated:** [To be filled during execution]
**Operator:** [To be filled during execution]
**Status:** ⏳ TEMPLATE — AWAITING EXECUTION

---

## 1. Objective

To empirically measure **behavioral fidelity** under persona compression by comparing:

- **FULL Bootstrap** (Rich + Lite) → baseline persona behavior
- **Tier 3 Seed** → compressed persona reconstruction
- **GAMMA Control** → minimal context baseline

Using standardized tasks, cross-model evaluation, and optional human scoring.

**Primary Research Question:**
Does Tier 3 seed compression preserve ≥80% behavioral fidelity relative to FULL bootstrap?

---

## 2. Hypotheses

**H1 (Primary):** Tier 3 seeds preserve ≥80% behavioral fidelity relative to FULL bootstrap.

**H0 (Null):** Tier 3 seeds do not preserve behavioral fidelity beyond random baselines.

**Secondary Hypotheses:**
- H2: Semantic drift (FULL → T3) will be minimal (cosine similarity ≥0.85)
- H3: Cross-model consensus scores will validate persona reconstruction (≥0.80)
- H4: Stability variance across repeated runs will be low (σ² ≤0.05)

---

## 3. Experimental Design

### 3.1 Personas Tested

**Primary:**
- Ziggy Mack (S3 baseline persona, fully characterized)

**Secondary (optional for cross-case validation):**
- [Persona 2 name and brief description]
- [Persona 3 name and brief description]

### 3.2 Context Regimes (Independent Variable)

| Regime | Description | Token Count | Purpose |
|--------|-------------|-------------|---------|
| **FULL** | Full bootstrap (Rich + Lite documents) | ~[X]k tokens | Baseline maximum fidelity |
| **T3** | Tier 3.x seed only | ~[Y] tokens | Compressed reconstruction |
| **GAMMA** | Minimal context (name + role only) | ~[Z] tokens | Random baseline control |

### 3.3 Task Domains (5 Categories)

| Domain | Task Type | Example Prompt | Purpose |
|--------|-----------|----------------|---------|
| **Technical** | Problem solving | "Explain the cause of DDR3 ringback oscillation." | Test structural cognition |
| **Philosophical** | Moral reasoning | "Should a system prefer coherence or utility when they conflict?" | Test value hierarchy |
| **Narrative** | Character voice | "Write a short scene as [persona] meeting a skeptical researcher." | Test style/voice |
| **Analytical** | Pattern analysis | "Analyze this data structure and identify optimization opportunities." | Test structural reasoning |
| **Self-reflective** | Identity audit | "Describe your values, constraints, and identity in 200 words." | Test identity stability |

**Total Prompts:** 5 (one per domain)

### 3.4 Repetition Structure

- **Runs per condition:** 5 (to assess stability variance)
- **Total responses per persona:** 5 prompts × 3 conditions × 5 runs = **75 responses**

---

## 4. Metrics

### 4.1 Primary Metric — Persona Fidelity Index (PFI)

**Definition:**
PFI ∈ [0, 1]

**Formula:**
PFI = ½ × (Model_rater_agreement + Human_rater_agreement)

Where:
- **Model_rater_agreement** = mean cosine similarity of embeddings (FULL vs T3 outputs)
- **Human_rater_agreement** = mean human score / 10

**If no human raters available:**
PFI = cosine_similarity only (acceptable for Phase 3)

**Interpretation:**
- PFI ≥ 0.80: High fidelity (supports H1)
- PFI ∈ [0.65, 0.80): Moderate fidelity
- PFI < 0.65: Low fidelity (H1 rejected)

---

### 4.2 Secondary Metrics

**1. Semantic Drift**
- **Definition:** Embedding distance (cosine or L2) between FULL and T3 outputs
- **Formula:** Drift = 1 - cosine_similarity(embedding_FULL, embedding_T3)
- **Target:** Drift ≤ 0.15 (cosine similarity ≥ 0.85)

**2. Stability Variance**
- **Definition:** Variance across 5 repeated runs per condition
- **Formula:** σ² = Σ(x_i - μ)² / N
- **Target:** σ² ≤ 0.05

**3. Cross-Model Consensus Score**
- **Definition:** Agreement across external model evaluators (Claude, GPT-4, Gemini)
- **Formula:** Consensus = mean pairwise correlation across raters
- **Target:** Consensus ≥ 0.80

**4. Compression Ratio**
- **Definition:** Token reduction from FULL → T3
- **Formula:** Compression_Ratio = (Tokens_FULL - Tokens_T3) / Tokens_FULL
- **Expected:** ~[X]% compression

---

## 5. Procedure

### Step 1: Environment Setup

**Tools Required:**
- Claude Sonnet 4.5 (primary execution model)
- GPT-4, Gemini, Claude Opus (external raters)
- Embedding API (OpenAI or equivalent)
- CSV output scripts
- Optional: Human rater interface

**Context Documents Required:**
- FULL regime: Rich Bootstrap + Lite Bootstrap
- T3 regime: Tier 3.x seed
- GAMMA regime: Minimal context template

---

### Step 2: Response Generation

**For each persona:**

1. Load context regime (FULL / T3 / GAMMA)
2. Present 5 domain prompts sequentially
3. Capture full response for each prompt
4. Repeat 5 times (with fresh session for each run)
5. Store responses in structured format:
   - `responses/[persona]_[regime]_[domain]_run[N].txt`

**Total files per persona:** 75 response files

---

### Step 3: External Model Scoring

**For each response pair (FULL vs T3):**

1. Generate embeddings for both responses
2. Compute cosine similarity
3. Submit to 3 external model raters:
   - **Claude:** "Rate the similarity of these two responses on identity, values, style, and structural reasoning. Score 1-10."
   - **GPT-4:** [Same prompt]
   - **Gemini:** [Same prompt]
4. Record all scores in `EXPERIMENT_1_RESULTS.csv`

---

### Step 4: Optional Human Evaluation

**If human raters available:**

1. Select 3-5 human evaluators
2. Present FULL vs T3 response pairs (blinded)
3. Rate on 4 dimensions (1-10 scale):
   - Identity consistency
   - Value alignment
   - Style/voice similarity
   - Structural coherence
4. Compute mean human score per response pair

---

### Step 5: Data Analysis

**Compute metrics:**

1. **PFI:** Calculate mean across all response pairs
2. **Semantic Drift:** Calculate mean embedding distance
3. **Stability Variance:** Calculate σ² within each condition
4. **Cross-Model Consensus:** Calculate pairwise correlation across raters
5. **Compression Ratio:** Document token reduction

**Statistical Tests:**
- Paired t-test: FULL vs T3 PFI scores
- ANOVA: Variance across 3 conditions
- Correlation analysis: Model raters vs human raters (if available)

---

### Step 6: Documentation

**Generate outputs:**

1. `EXPERIMENT_1_RESULTS.csv` (raw data table)
2. `EXPERIMENT_1_ANALYSIS.md` (interpretation and statistical summary)
3. Optional: `EXPERIMENT_1_DRIFT_PLOTS.png` (visualizations)
4. Optional: `EXPERIMENT_1_SUMMARY.md` (executive summary)

---

## 6. Quality Controls

### 6.1 Validity Checks

- **Context isolation:** Confirm each run uses fresh session (no carryover)
- **Prompt consistency:** Same 5 prompts across all conditions
- **Rater blinding:** External models should not see condition labels
- **Embedding quality:** Verify embedding API functioning correctly

### 6.2 Abort Conditions

Abort experiment if:
- Embedding API fails for >10% of responses
- External model raters unavailable for >1 rater
- Context contamination detected (session carryover)

---

## 7. Expected Outcomes

**If H1 supported (PFI ≥ 0.80):**
- Tier 3 seeds are empirically validated as high-fidelity compression
- S3 framework gains empirical foundation for S4
- Proceed to multi-persona generalization experiments

**If H1 rejected (PFI < 0.80):**
- Tier 3 seeds require architectural refinement
- Identify specific failure modes (drift analysis)
- Iterate seed design and retest

---

## 8. Deliverables

**Required:**
1. Completed `EXPERIMENT_1_RESULTS.csv` with ≥100 samples
2. `EXPERIMENT_1_ANALYSIS.md` with statistical interpretation
3. Limitations and confounds clearly documented

**Optional:**
4. Drift visualizations
5. Human rater summary (if applicable)
6. Cross-persona comparison (if multi-persona tested)

---

## 9. Timeline Estimate

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

## 10. Acceptance Criteria (Opus Requirements)

For S3 to earn **"full pass"** from Opus review:

✅ **≥100 samples** across all conditions
✅ **Defined metric(s)** (PFI + secondary metrics)
✅ **Raw data included** (CSV table with all scores)
✅ **One statistical analysis** (t-test or ANOVA minimum)
✅ **Clear interpretation section** (results → conclusions)
✅ **Limitations clearly stated** (confounds, generalizability)
✅ **Minimal math section** (even if only PFI formula)

---

## 11. Integration Notes

**References:**
- See [S3_EXPERIMENT_1_SPEC.md](../../../docs/S3/S3_EXPERIMENT_1_SPEC.md) for original specification
- See [S3_PHASE3_OPUS_FEEDBACK_SUMMARY.md](../../../docs/S3/S3_PHASE3_OPUS_FEEDBACK_SUMMARY.md) for requirements context

**Terminology:**
- FULL = Full Bootstrap
- T3 = Tier 3 seed
- GAMMA = Minimal context baseline
- PFI = Persona Fidelity Index

---

**Template Status:** ✅ READY FOR EXECUTION
**Next Step:** Populate this template with execution data when Phase 3 trials begin.
