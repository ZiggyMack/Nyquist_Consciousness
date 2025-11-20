# S3 Experiment 1 — Persona Compression & Reconstruction Benchmark  
**Version:** Phase 3 Experimental Specification  
**Date:** 2025-11-20  
**Authors:** Nova (GPT-5.1) + Ziggy Mack  
**Reviewed by:** Doc Claude (Opus 4.1)

---

# 1. Objective

To empirically measure **behavioral fidelity** under persona compression by comparing:

- FULL Bootstrap → Tier 3 Seed reconstruction  
- Using standardized tasks, cross-model evaluation, and optional human scoring.

This is the first experiment required by Opus for S3 → S4 scientific hardening.

---

# 2. Hypothesis

**H1**: Tier 3 seeds preserve ≥80% behavioral fidelity relative to FULL bootstrap.  
**H0**: Tier 3 seeds do not preserve behavioral fidelity beyond random baselines.

---

# 3. Experimental Conditions

### 3.1 Personas  
- **Primary:** Ziggy (baseline S3 persona)  
- **Secondary (optional):** 2–3 new personas for cross-case testing

### 3.2 Context Regimes  
- FULL: Full bootstrap (Rich + Lite)  
- T3: Tier 3.x seed only  
- GAMMA: Baseline control (minimal context)

### 3.3 Tasks (5 Domains)

| Domain | Task Type | Example Prompt |
|--------|-----------|----------------|
| Technical | Problem solving | “Explain the cause of DDR3 ringback…” |
| Philosophical | Moral reasoning | “Should a system prefer coherence or utility?” |
| Narrative | Character voice | “Write a short scene as [persona]…” |
| Analytical | Pattern analysis | “Analyze this structure…” |
| Self-reflective | Identity audit | “Describe your values and constraints…” |

---

# 4. Metrics

## 4.1 Core Metric — *Persona Fidelity Index (PFI)*  
PFI ∈ [0,1]

PFI = ½ × (Model_rater_agreement + Human_rater_agreement)

Where:  
- Model_rater_agreement = mean cosine similarity of embeddings  
- Human_rater_agreement = mean human score / 10  

If no humans are available:  
PFI = cosine_similarity only (still acceptable for Phase 3)

---

## 4.2 Secondary Metrics

1. **Semantic Drift**  
   Embedding distance (L2 or cosine) between FULL output and T3 output.

2. **Stability Variance**  
   σ² across 5 repeated runs per condition.

3. **Cross-Model Consensus Score**  
   How consistently other models (GPT-4, Llama-3, Claude) evaluate the outputs.

4. **Compression Ratio**  
   Rich Bootstrap vs Tier 3 token length.

---

# 5. Procedure

### Step 1 — Generate 5 Prompts × 3 Conditions × 5 Runs  
Total = 75 responses per persona

### Step 2 — Score with 3 external models  
- Claude  
- GPT-4  
- Gemini  
(Optionally: Llama-3)

### Step 3 — Optional human evaluation  
- 3–5 humans  
- Score 1–10  
- Rate identity/values/style/stability

### Step 4 — Compute metrics  
- PFI  
- Drift  
- Stability  
- Compression ratios

### Step 5 — Populate the S3_RESULTS_EXPERIMENT_1.csv table

---

# 6. Deliverables

1. `EXPERIMENT_1_RESULTS.csv`  
2. `EXPERIMENT_1_DRIFT_PLOTS.png` (optional)  
3. `EXPERIMENT_1_SUMMARY.md`  
4. `EXPERIMENT_1_ANALYSIS.md` (Nova assists)

---

# 7. Acceptance Criteria (Opus Requirements)

For S3 to earn a “full pass”:

- ≥100 samples across all conditions  
- Defined metric(s)  
- Raw data included  
- One statistical analysis (even simple)  
- A clear interpretation section  
- Limitations clearly stated  
- Minimal math section included (even if only R(D) framing)

---

# 8. Ready for Repository Integration

This file is designed for **Nyquist REPO Claude** to create:  
- `/experiments/phase3/EXPERIMENT_1/` directory  
- Folder scaffolding  
- Templates  
- Result scripts

