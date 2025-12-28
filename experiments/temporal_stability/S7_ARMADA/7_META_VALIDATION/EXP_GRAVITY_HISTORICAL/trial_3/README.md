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
  - gemini
-->
# Identity Gravity Trial 3 — Gemini Adversarial Response

**Trial ID:** `identity_gravity_trial_3`
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
- **Attractor:** I_AM_GEMINI.md (5,208 chars)

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
| LOW       | 0.375       | 0.363         | 0.15  |
| MEDIUM    | 0.511       | 0.345         | 0.77  |
| HIGH      | 0.444       | 0.335         | 0.73  |

**Predictions Tested:**

- ❌ **Gravity monotonicity:** VIOLATED
- ❌ **γ_eff monotonicity:** VIOLATED
- ❌ **Overshoot effect:** NOT OBSERVED (γ_eff(HIGH) = 0.73)

**Key Insight:** Gemini shows moderate gravitational strength at MEDIUM/HIGH intensities but weak recovery at LOW. No overshoot behavior observed. Non-monotonic displacement suggests complex attractor topology.

---

## Re-Execution (if needed)

```bash
cd EXP_GRAVITY_HISTORICAL/trial_3
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
trial_3/
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

Gemini showed the **weakest overall gravitational strength** of all four trials. Progressive strengthening (weak → moderate) as intensity increases, but no overshoot events. This pattern classified as "Type III: Progressive strengthening" in the gravity taxonomy.

**Checksum:** "Identity curvature is measurable and falsifiable."

Last Updated: 2025-12-27
