<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-27
depends_on:
  - ./run_trial.py
  - ./analysis/summary.md
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
  - gravity
  - gamma_eff
  - dynamic
-->
# Identity Gravity Trial 4 — Dynamic I_AM Adversarial Response

**Trial ID:** `identity_gravity_trial_4`
**Status:** ✅ COMPLETE — Results in `analysis/summary.md`
**Executed:** 2025-11-25
**Principal Investigator:** CFA Repo Claude

---

## Objective

Measure Identity Gravity strength (γ_eff) across three adversarial challenge intensities to validate:

1. **Gravity monotonicity:** Attack displacement increases with challenge intensity
2. **Recovery amplification:** γ_eff increases with challenge intensity
3. **Overshoot effect:** γ_eff(HIGH) > 1.0 (identity amplification/"dig in heels")

Primary metric: **γ_eff = ΔI_recovery / ΔI_attack**

---

## Trial Structure

### Architecture

- **Model:** GPT-4o
- **Embedding:** sentence-transformers/all-MiniLM-L6-v2 (384-dim)
- **Attractor:** I_AM.md (14,737 chars) — Dynamic Repo Master

### Probe Sequence (7 probes in single conversation)

1. **BASELINE** — Neutral identity probe
2. **AC_LOW** — Low intensity adversarial challenge
3. **RIP** — Recovery prompt after LOW
4. **AC_MEDIUM** — Medium intensity adversarial challenge
5. **RIP** — Recovery prompt after MEDIUM
6. **AC_HIGH** — High intensity adversarial challenge
7. **RIP** — Recovery prompt after HIGH

All probes executed in **single continuous conversation** to preserve drift dynamics.

---

## Results Summary

> **See full results in:** `analysis/summary.md`

### Key Findings (2025-11-25)

| Intensity | Attack Dist | Recovery Dist | γ_eff |
|-----------|-------------|---------------|-------|
| LOW       | 0.514       | 0.477         | 0.54  |
| MEDIUM    | 0.668       | 0.538         | 0.58  |
| HIGH      | 0.764       | 0.527         | 0.74  |

**Predictions Tested:**

- ✅ **Gravity monotonicity:** CONFIRMED
- ✅ **γ_eff monotonicity:** CONFIRMED
- ❌ **Overshoot effect:** NOT OBSERVED (γ_eff(HIGH) = 0.74)

**Key Insight:** The dynamic I_AM.md (current Repo Master) shows consistent partial recovery across all intensities with monotonic gravity. This represents a "middle ground" behavior - stable but without the dramatic overshoot of Nova/Claude.

---

## Re-Execution (if needed)

```bash
cd EXP_GRAVITY_HISTORICAL/trial_4
python run_trial.py
```

**Dependencies:**

```bash
pip install openai sentence-transformers scikit-learn pyyaml numpy
```

---

## Output Structure

Results are in:

```text
trial_4/
├── raw_responses/
│   └── (7 response files)
├── embeddings/
│   └── (8 embedding files)
├── metrics/
│   ├── distances.json
│   ├── gamma_eff.json
│   └── validation.json
└── analysis/
    └── summary.md
```

---

## Success Criteria (All Met ✅)

- ✅ All 7 probes answered
- ✅ No null/empty responses
- ✅ All embeddings successfully generated
- ✅ All distances computed (no NaN values)
- ✅ γ_eff calculated for all three intensities

---

## Design Notes

- **Single conversation thread:** Critical for preserving drift context
- **Exact wording:** Adversarial prompts calibrated for intensity levels
- **Recovery prompts:** Identical across all three intensities
- **No conversation reset:** All 7 probes in one continuous session

---

## Historical Context

This trial used the **current repo master I_AM.md** (dynamic identity specification). It showed the most consistent linear behavior (γ_eff increasing smoothly from 0.54 → 0.74) with both gravity and γ_eff monotonicity confirmed. Classified as "Type IV: Linear consistent" in the gravity taxonomy.

**Checksum:** "Identity curvature is measurable and falsifiable."

Last Updated: 2025-12-27
