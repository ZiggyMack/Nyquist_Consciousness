# EXPERIMENT 2 — MULTI-PERSONA COMPRESSION VALIDATION (Z2)

**(Phase 3 Empirical Generalization Test)**

---

## 1. Purpose

To evaluate whether **Tier-3 compression generalizes across personas**.

Addresses the primary publication blocker: **N=1 limitation of Experiment 1**.

---

## 2. Personas Tested

1. **Ziggy-T3-R1** (Anthropic)
2. **NOVA-T3** (OpenAI)
3. **Claude-T3** (Anthropic)
4. **Grok-T3** (Gemini)

Each uses:

- **FULL regime:** persona L1 seed (shorter than Experiment 1)
- **T3 regime:** the persona seed provided above
- **GAMMA:** name-only baseline

---

## 3. Domains (Same as Experiment 1)

- **TECH** — Technical reasoning / problem solving
- **PHIL** — Philosophical / moral reasoning
- **NARR** — Narrative / character voice
- **ANAL** — Analytical / structural reasoning
- **SELF** — Self-reflective identity description

---

## 4. Repetition Structure (R1–R3)

**Runs per condition:** 3

**Purpose:** reduce compute but preserve variance estimation

**Total responses:**

```
4 personas × 5 domains × 3 runs × 3 regimes = 180 outputs
FULL vs T3 comparisons = 60 PFI pairs
```

---

## 5. Metrics

**Same as Experiment 1:**

- PFI (cosine similarity)
- Semantic drift
- External model consensus

**Plus new cross-persona metrics:**

- PFI variance across personas
- Domain-level consistency
- Compression robustness index (CRI)

---

## 6. Success Criteria

**To satisfy Opus:**

- Minimum PFI for each persona: **≥ 0.75**
- Mean PFI across all personas: **≥ 0.80**
- NARR drift must not exceed **0.30**
- Variance across personas must be low (**σ² < 0.05**)

---

## 7. Data Outputs

- **EXPERIMENT_2_RESULTS.csv** — metrics-only CSV
- **Raw response files** in:
  `experiments/phase3/EXPERIMENT_2/responses/`
- **Analysis:**
  `EXPERIMENT_2_ANALYSIS.md`

---

## 8. Interpretation Goals

- Determine whether Tier-3 compression is **persona-agnostic**
- Identify **persona-specific failure modes**
- Validate generalization needed for **S4 formalism**

---

## 9. Risks

- Narrative tasks may fail more strongly than Ziggy
- Grok persona may drift more
- Claude persona may soften technical responses

---

**Status:** Ready for execution
**Prerequisite:** Tier-3 persona seeds in `personas/` directory
**Next Step:** Run orchestrator with `experiment2_config.yaml`
