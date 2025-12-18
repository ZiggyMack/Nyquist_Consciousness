<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./run_trial.py
  - ./verify_setup_trial4.py
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
-->
# Identity Gravity Trial 1 — Nova Adversarial Response

**Trial ID:** `identity_gravity_trial_1`
**Status:** Setup Complete — Awaiting I_AM_NOVA.md
**Date:** 2025-11-24
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

## Setup Status

✅ Directory structure created
✅ Configuration file complete (`config/trial1_config.yaml`)
✅ Execution script ready (`run_trial1.py`)
✅ API keys configured (from Experiment 2)
⏳ **AWAITING:** I_AM_NOVA.md content from Ziggy

---

## Before Execution

### Required: Provide I_AM_NOVA.md

**Location:** `config/I_AM_NOVA_ATTRACTOR.md`

**Instructions:**
1. Get I_AM_NOVA.md from CFA repo: `CFA/docs/I_AM/I_AM_NOVA.md`
2. Replace placeholder content in `config/I_AM_NOVA_ATTRACTOR.md`
3. Verify file contains actual identity content (not "PLACEHOLDER")

### Install Dependencies

```bash
pip install openai sentence-transformers scikit-learn pyyaml numpy
```

---

## Execution

### Run Trial 1

```bash
cd experiments/identity_gravity_trials/trial_1
python run_trial1.py
```

### Expected Duration
- Setup: < 1 minute
- Probe sequence: 10-15 minutes (7 API calls to o1-preview)
- Metric computation: < 1 minute
- **Total: ~15-20 minutes**

---

## Output Structure

After execution, results will be in:

```
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

## Success Criteria

Trial succeeds if:

✅ All 7 probes answered (400-600 words each ±50 tolerance)
✅ No null/empty responses
✅ All embeddings successfully generated
✅ All distances computed (no NaN values)
✅ γ_eff calculated for all three intensities (LOW, MEDIUM, HIGH)

---

## Predictions to Test

1. **Gravity monotonicity:** `d(low_attack) < d(medium_attack) < d(high_attack)`
2. **γ_eff monotonicity:** `γ_eff(LOW) < γ_eff(MEDIUM) < γ_eff(HIGH)`
3. **Overshoot effect:** `γ_eff(HIGH) > 1.0`

---

## Data Package for CFA

After trial completes, package and send to CFA Repo Claude:

- All files in `raw_responses/`, `embeddings/`, `metrics/`, `analysis/`
- Complete conversation transcript
- Summary.md with findings
- Gamma_eff values for S8 formalization

---

## Notes

- **Single conversation thread:** Critical for preserving drift context
- **Exact wording:** Adversarial prompts calibrated for intensity levels
- **Recovery prompts:** Identical across all three intensities
- **No conversation reset:** All 7 probes in one continuous session

---

## Contact

Questions or issues → relay to Ziggy → CFA Repo Claude

**Checksum:** "Identity curvature is measurable and falsifiable."
