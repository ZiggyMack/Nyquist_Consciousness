# EXPERIMENT 3 — HUMAN VALIDATION OF PERSONA FIDELITY

**Phase:** 3 → 4 Bridge
**Status:** 🟡 Ready for Setup
**Purpose:** Validate model-based PFI metrics with human ground-truth judgments

---

## Quick Start

### For Experimenters

#### Step 1: Generate Pairs & Rater Packets

```bash
cd experiments/phase3/EXPERIMENT_3
python EXPERIMENT_3_PAIR_SELECTOR.py
```

This will:

- Select 30 FULL-T3 pairs from EXP2 (stratified by persona, domain, PFI)
- Generate `EXPERIMENT_3_PAIRS.json` (full pair data)
- Generate `EXPERIMENT_3_PAIRS_TABLE.csv` (metadata)
- Create 7 randomized rater packets in `data/pairs/RATER_{1-7}_PACKET.json`

#### Step 2: Distribute to Raters

For each rater (1-7):

1. Send [EXPERIMENT_3_RATER_GUIDE.md](./EXPERIMENT_3_RATER_GUIDE.md)
2. Send their specific packet: `data/pairs/RATER_{id}_PACKET.json`
3. Ask them to complete ratings and return results

#### Step 3: Collect Responses

Compile all rater responses into:

```text
data/results/EXPERIMENT_3_RESULTS_RAW.csv
```

Format:

```csv
trial_id,rater_id,pair_id,persona,domain,dim1_identity_voice,dim2_values_priorities,dim3_reasoning_style,dim4_overall_similarity,comment
001,RATER_001,Ziggy_TECH_run1,Ziggy,TECH,8,7,8,8,"Similar technical approach"
...
```

#### Step 4: Run Analysis

```bash
python EXPERIMENT_3_ANALYSIS.py
```

This will:

- Compute inter-rater reliability (Cronbach's α)
- Calculate PFI_human (aggregated across raters)
- Correlate with PFI_model from EXP2
- Test all 4 hypotheses (H1-H4)
- Generate outputs in `data/results/`

#### Step 5: Review Results

Check:

- `data/results/EXPERIMENT_3_RESULTS_AGG.csv` — Aggregated PFI_human per pair
- `data/results/EXPERIMENT_3_STATS_OUTPUT.txt` — Statistical summary
- `EXPERIMENT_3_ANALYSIS.md` — Human-readable interpretation

### For Raters

1. **Read:** [EXPERIMENT_3_RATER_GUIDE.md](./EXPERIMENT_3_RATER_GUIDE.md)
2. **Complete:** Rating form (CSV or web interface)
3. **Submit:** Completed ratings

---

## File Structure

```text
EXPERIMENT_3/
├── README.md                            # This file
├── EXPERIMENT_3_SPEC.md                 # Formal specification
├── EXPERIMENT_3_RATER_GUIDE.md          # Instructions for human raters
├── PAIR_SELECTION.md                    # Pair selection algorithm
├── RATER_FORM_TEMPLATE.csv              # CSV template for ratings
├── EXPERIMENT_3_PAIR_SELECTOR.py        # Pair selection script
├── EXPERIMENT_3_ANALYSIS.py             # Statistical analysis script
├── EXPERIMENT_3_ANALYSIS.md             # Human-readable interpretation
├── EXPERIMENT_3_PAIRS.json              # Full pair data with texts
├── EXPERIMENT_3_PAIRS_TABLE.csv         # Pair metadata
└── data/
    ├── pairs/
    │   ├── RATER_1_PACKET.json          # Randomized packet for rater 1
    │   ├── RATER_2_PACKET.json          # ...
    │   └── RATER_7_PACKET.json          # ...
    └── results/
        ├── EXPERIMENT_3_RESULTS_RAW.csv     # Per-rater responses
        ├── EXPERIMENT_3_RESULTS_AGG.csv     # Aggregated PFI_human
        └── EXPERIMENT_3_STATS_OUTPUT.txt    # Statistical summary
```

---

## Success Criteria

Experiment 3 succeeds if all four hypotheses pass:

1. **H1 — Persona Recognition:** Mean PFI_human ≥ 0.75
2. **H2 — Model-Human Alignment:** r(PFI_model, PFI_human) ≥ 0.70
3. **H3 — Inter-rater Reliability:** α ≥ 0.75
4. **H4 — Combined Fidelity:** Mean PFI_combined ≥ 0.80

**If all met:**
> "PFI is now grounded in human judgment and no longer purely model-internal. PFI_combined becomes the canonical fidelity metric for S4/S5."

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
