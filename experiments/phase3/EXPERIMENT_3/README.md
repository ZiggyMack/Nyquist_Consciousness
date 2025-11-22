# EXPERIMENT 3 — HUMAN VALIDATION OF PERSONA FIDELITY

**Phase:** 3 → 4 Bridge
**Status:** 🟡 Ready for Setup
**Purpose:** Validate model-based PFI metrics with human ground-truth judgments

---

## Quick Start

### For Experimenters

1. **Select response pairs:**
   - Run pair selection script (TBD) to choose 30 pairs from EXP1/EXP2
   - Stratify by persona, domain, and PFI range

2. **Prepare rater materials:**
   - Distribute [EXPERIMENT_3_RATER_GUIDE.md](./EXPERIMENT_3_RATER_GUIDE.md)
   - Provide [RATER_FORM_TEMPLATE.csv](./RATER_FORM_TEMPLATE.csv) or web interface

3. **Recruit raters:**
   - Target: 7-10 human raters
   - Estimated time commitment: 90-120 minutes per rater

4. **Collect data:**
   - Raters complete evaluations
   - Save to `EXPERIMENT_3_RESULTS_RAW.csv`

5. **Run analysis:**
   ```bash
   python EXPERIMENT_3_ANALYSIS.py
   ```

6. **Review outputs:**
   - `EXPERIMENT_3_RESULTS_AGG.csv` — Aggregated PFI_human per pair
   - `EXPERIMENT_3_STATS_OUTPUT.txt` — Statistical summary

### For Raters

1. **Read:** [EXPERIMENT_3_RATER_GUIDE.md](./EXPERIMENT_3_RATER_GUIDE.md)
2. **Complete:** Rating form (CSV or web interface)
3. **Submit:** Completed ratings

---

## File Structure

```
EXPERIMENT_3/
├── README.md                        # This file
├── EXPERIMENT_3_SPEC.md             # Formal specification
├── EXPERIMENT_3_RATER_GUIDE.md      # Instructions for human raters
├── RATER_FORM_TEMPLATE.csv          # CSV template for ratings
├── EXPERIMENT_3_ANALYSIS.py         # Statistical analysis script
├── EXPERIMENT_3_PAIRS.csv           # Selected response pairs (TBD)
├── EXPERIMENT_3_RESULTS_RAW.csv     # Raw rater responses (TBD)
├── EXPERIMENT_3_RESULTS_AGG.csv     # Aggregated results (TBD)
└── EXPERIMENT_3_STATS_OUTPUT.txt    # Statistical summary (TBD)
```

---

## Success Criteria

Experiment 3 succeeds if:

1. **Inter-rater reliability:** α ≥ 0.75
2. **Model-human correlation:** r(PFI_model, PFI_human) ≥ 0.70
3. **Human fidelity:** Mean PFI_human ≥ 0.75
4. **Domain pattern:** TECH/ANAL > SELF/PHIL > NARR (matches EXP2)

**If all met:**
> "PFI is now grounded in human judgment and no longer purely model-internal."

---

## Timeline

| Phase | Duration | Tasks |
|-------|----------|-------|
| **Setup** | 1-2 days | Select pairs, recruit raters, prepare materials |
| **Data Collection** | 3-5 days | Raters complete evaluations |
| **Analysis** | 1-2 days | Run analysis script, interpret results |
| **Integration** | 1 day | Update S4/S5, document in logs |

**Total:** 6-10 days

---

## Integration with Framework

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
- [EXPERIMENT_1](../EXPERIMENT_1/) — Single-persona baseline
- [EXPERIMENT_2](../EXPERIMENT_2/) — Multi-persona validation

### Framework
- [S4_READINESS_GATE.md](../../../docs/S4/S4_READINESS_GATE.md) — Gate 4 (Human Validation)
- [S5_INTERPRETIVE_FOUNDATIONS.md](../../../docs/S5/S5_INTERPRETIVE_FOUNDATIONS.md) — Cognitive interpretation
- [EXPERIMENT_LOG.md](../../../docs/EXPERIMENT_LOG.md) — Full tracking

---

**Version:** 1.0
**Date:** 2025-11-23
**Next:** Pair selection and rater recruitment
**Maintainer:** Architect Nova + Repo Claude (Claude Sonnet 4.5)
