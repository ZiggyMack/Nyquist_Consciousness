# EXPERIMENT 2 — Analysis Template

**Goal:** Provide a structured template for analyzing the Experiment 2 CSV
and reporting cross‑persona Tier‑3 fidelity metrics.

---

## 1. Data Sources

- `EXPERIMENT_2_RESULTS.csv` (metrics‑only)
- `responses/` (raw response text, optional for qualitative review)

Columns expected:

- persona_id, persona_label
- regime, domain, run_index
- embedding_cosine_similarity
- claude_score, gpt4_score, gemini_score
- pfi, semantic_drift

---

## 2. Core Aggregates

1. Per‑persona mean PFI (all domains)
2. Per‑persona × domain PFI
3. Global mean PFI (all personas, all domains)
4. Per‑persona drift statistics

Document all of these with tables and short commentary.

---

## 3. Statistical Tests (Recommended)

When data is available:

- One‑sample t‑tests:
  - H1: per‑persona mean PFI ≥ 0.80
  - H2: global mean PFI ≥ 0.80
- ANOVA:
  - PFI by domain (TECH vs PHIL vs NARR vs ANAL vs SELF)
  - PFI by persona
- Confidence intervals:
  - 95% CI for each persona’s mean PFI

---

## 4. Interpretation Checklist

For each persona:

- Did mean PFI exceed 0.75? 0.80?
- Which domains were strongest / weakest?
- Any surprising deviations from Ziggy’s pattern?

Cross‑persona:

- Is the TECH/ANAL > SELF/PHIL > NARR pattern broadly preserved?
- Are there signs of a “style bottleneck” across personas?
- Does any persona systematically underperform, suggesting seed issues?

---

## 5. Reporting Back to S3 / Opus

In the final write‑up:

- State clearly: N, number of personas, total pairs
- Highlight global mean PFI and per‑persona minima
- Explicitly connect results to Doc‑Claude’s checklist:
  - N>1
  - N≈100 pairs
  - Cross‑persona generalization
