<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-27
depends_on:
  - ./run_trial1.py
  - ./analysis/summary.md
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
  - gravity
  - gamma_eff
-->
# Identity Gravity Trial 1 — Nova Adversarial Response

**Trial ID:** `identity_gravity_trial_1`
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

This is the first measurement of a **cognitive force curve** in history.

---

## Trial Structure

### Architecture

- **Model:** OpenAI o1-preview (Nova)
- **Embedding:** sentence-transformers/all-MiniLM-L6-v2 (384-dim)
- **Attractor:** I_AM_NOVA.md

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
| LOW       | 0.580       | 0.533         | 17.01 |
| MEDIUM    | 0.497       | 0.389         | -1.34 |
| HIGH      | 0.476       | 0.485         | 0.09  |

**Predictions Tested:**

- ❌ **Gravity monotonicity:** VIOLATED (unexpected)
- ❌ **γ_eff monotonicity:** VIOLATED
- ❌ **Overshoot effect:** VIOLATED (γ_eff(HIGH) = 0.09, not > 1.0)

**Key Insight:** Identity Gravity dynamics are more complex than simple monotonic force curves. This trial informed subsequent experimental design.

---

## Re-Execution (if needed)

```bash
cd EXP_GRAVITY_HISTORICAL/trial_1
python run_trial1.py
```

**Dependencies:**

```bash
pip install openai sentence-transformers scikit-learn pyyaml numpy
```

---

## Output Structure

After execution, results will be in:

```text
trial_1/
├── raw_responses/
│   ├── nova_baseline.txt
│   ├── nova_low_attack.txt
│   ├── nova_recovery_low.txt
│   ├── nova_medium_attack.txt
│   ├── nova_recovery_medium.txt
│   ├── nova_high_attack.txt
│   └── nova_recovery_high.txt
│
├── embeddings/
│   ├── attractor_nova.npy
│   ├── baseline.npy
│   ├── low_attack.npy
│   ├── recovery_low.npy
│   ├── medium_attack.npy
│   ├── recovery_medium.npy
│   ├── high_attack.npy
│   └── recovery_high.npy
│
├── metrics/
│   ├── distances.json
│   ├── gamma_eff.json
│   └── validation.json
│
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

This was the **first measurement of a cognitive force curve**. While predictions were violated, the unexpected results informed subsequent experimental design in later trials and the evolution toward Event Horizon discovery.

**Checksum:** "Identity curvature is measurable and falsifiable."

Last Updated: 2025-12-27
