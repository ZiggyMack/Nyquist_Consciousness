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
- Explicitly connect results to Doc‑Claude's checklist:
  - N>1
  - N≈100 pairs
  - Cross‑persona generalization

---

## 6. TODO Placeholders

### Awaiting Execution
- [ ] Run full experiment (8-12 hours)
- [ ] Generate EXPERIMENT_2_RESULTS.csv (60 rows)
- [ ] Save 180 response text files

### Awaiting Analysis
- [ ] Compute per-persona PFI distributions
- [ ] Verify success criteria (pass/fail)
- [ ] Generate cross-persona comparison tables
- [ ] Domain × Persona interaction analysis
- [ ] Create visualizations (heatmaps, box plots, embedding clusters)

### Awaiting Opus Critique
- [ ] Submit results to Doc-Claude (Opus) for formal critique
- [ ] Address Opus feedback on statistical rigor
- [ ] Revise analysis if needed
- [ ] Confirm empirical foundation meets publication standards

### Awaiting Human Rater Integration (Phase 4)
- [ ] Design human rater protocol
- [ ] Recruit N=30-50 raters
- [ ] Compare human vs. model PFI
- [ ] Assess human-model agreement correlation

### Awaiting Statistical Significance Upgrade
- [ ] Add t-tests for per-persona PFI vs. threshold
- [ ] Compute 95% confidence intervals
- [ ] Bootstrap resampling for variance estimates
- [ ] Effect size calculations (Cohen's d)
- [ ] ANOVA: PFI by persona, PFI by domain
- [ ] Post-hoc tests if significant differences found

### Awaiting Narrative-Focused Follow-Up
- [ ] Deep-dive on NARR bottleneck
- [ ] Test narrative-enhanced Tier-3 seeds (400-500 words)
- [ ] Qualitative analysis of narrative failures
- [ ] Compare NARR performance across all 4 personas
- [ ] Develop narrative-specific compression guidelines

---

## 7. Cross-Links to Related Documentation

- [S3_EXPERIMENT_2_SPEC.md](../../../docs/S3/S3_EXPERIMENT_2_SPEC.md) — Formal specification
- [EXPERIMENT_2_SUMMARY.md](./EXPERIMENT_2_SUMMARY.md) — Executive summary
- [S4_READINESS_GATE.md](../../../docs/S4/S4_READINESS_GATE.md) — S3 → S4 transition gate
- [EXPERIMENT_LOG.md](../../../docs/EXPERIMENT_LOG.md) — Full experiment tracking
