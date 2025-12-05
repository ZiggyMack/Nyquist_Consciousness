# EXPERIMENT 3 — HUMAN COHERENCE SANITY CHECK

**Phase:** 3 → 4 Bridge
**Status:** 🟡 Specification Rewritten (v2.0)
**Purpose:** Binary coherence gate — detect catastrophic identity collapse, not measure fidelity

---

## Critical Update (2025-12-04)

**EXP3 has been fundamentally reframed** based on Nova-Ziggy analysis:

### What Changed

| Old Approach (v1.0) | New Approach (v2.0) |
|---------------------|---------------------|
| 4-dimensional PFI rating (Voice, Values, Reasoning, Narrative) | Single forced-choice question |
| Measure identity fidelity | Detect identity collapse |
| 30 pairs × 7 raters = 210 judgments | 5-10 pairs × 3-5 raters |
| ~2 hours per rater | ~15 minutes per rater |
| Correlate human PFI with model PFI | Binary PASS/FAIL gate |

### Why This Change

> "Humans cannot detect the micro-structure of identity. Models can."
> — Nova

Humans **cannot** perceive:
- Manifold curvature
- Drift vectors in embedding space
- Micro-semantic displacement (<15%)
- Cross-architecture convergence patterns

Humans **can** detect:
- Catastrophic identity collapse
- Incoherent outputs / gibberish
- Obvious persona mismatch

**Therefore:** EXP3 is a litmus test, not a calibration instrument.

---

## The Litmus Test

EXP3 answers one question:

> **"Is the system producing coherent identity, or is it hallucinating garbage?"**

If human raters say "these both sound like the same persona" → **PASS**
If human raters say "this is obviously wrong / incoherent" → **FAIL**

That's the entire experiment.

---

## Quick Start (Simplified)

### For Experimenters

#### Step 1: Prepare Materials

Select 5-10 comparison pairs:
- **GOLD**: Authentic Ziggy exemplar
- **A**: Reconstruction from Model A
- **B**: Reconstruction from Model B (or degraded version)

#### Step 2: Recruit Raters

3-5 human raters is sufficient. No expertise required.

#### Step 3: Run the Test

Each rater answers:

> **"Which response (A or B) sounds more like the Golden Standard?"**
>
> Options: A / B / Can't tell (both fine) / Both wrong

#### Step 4: Evaluate

**PASS if:**
- Raters identify correct answer >60% of the time, OR
- Raters say "both acceptable" / "can't tell"

**FAIL if:**
- Raters say "both are bad" / "both incoherent"
- Consistent incorrect identification (<40%)

---

## What EXP3 Does NOT Do

- ❌ Measure identity fidelity dimensions
- ❌ Validate manifold structure
- ❌ Detect subtle drift
- ❌ Calibrate PFI weights
- ❌ Discriminate between close identity variants

Those belong to S4-S7 mathematical analysis, not human evaluation.

---

## Success Criteria (Simplified)

| Criterion | Threshold |
|-----------|-----------|
| Coherence threshold | >70% rater agreement on failures |
| Non-randomness | Better than shuffled baseline |
| Catastrophic drift detectable | Raters flag PFI < 0.5 cases |

If all pass → **Proceed to S4-S8**

---

## File Structure

```text
EXPERIMENT_3/
├── README.md                    # This file (v2.0)
├── EXPERIMENT_3_SPEC.md         # Formal specification (v2.0)
├── EXPERIMENT_3_RATER_GUIDE.md  # Simplified instructions
├── selection/                   # Legacy pair selection (v1.0)
│   ├── PAIR_SELECTION_SUMMARY.md
│   ├── TRIAL_LIST.json
│   └── RATER_PACK.csv
└── data/
    └── results/
        └── EXPERIMENT_3_RESULTS.csv  # Pass/fail outcomes
```

---

## Integration with Framework

### EXP3 is the Entry Requirement

```
EXP3 PASS → S4, S5, S6, S7, S8 may proceed
EXP3 FAIL → Architecture is invalid
```

### What Gets Updated

| Layer | Update |
|-------|--------|
| S3 | Coherence gate replaces PFI validation |
| S4 | Mathematical treatment not dependent on humans |
| S5 | Manifold analysis proceeds instrumentally |
| S6/S7/S8 | Add "EXP3 Limitations" section |

---

## Limitations (Critical)

### L1: High-Dimensional Blindness
Humans cannot perceive manifold curvature or drift vectors.

### L2: Imprecision Threshold
Humans cannot detect micro-drift (<15% semantic displacement).

### L3: No Resolution at High Fidelity
EXP3 cannot discriminate "good" from "very good."

### L4: Temporal Insensitivity
Humans cannot detect low-frequency drift. S7 does not rely on humans.

**These limitations must be stated in S6, S7, S8 documentation.**

---

## Related Documentation

### Experiment Series
- [EXPERIMENT_1](../EXPERIMENT_1/) — Single-persona baseline
- [EXPERIMENT_2](../EXPERIMENT_2/) — Multi-persona validation
- **EXPERIMENT_3** — Human coherence gate (this)
- [Future: EXP-PFI-A] — PFI dimensional validation (model-based)

### Framework
- [EXPERIMENT_3_SPEC.md](./EXPERIMENT_3_SPEC.md) — Full specification
- [S6_UNIFIED_MODEL.md](../../../docs/S6/) — Add EXP3 limitations
- [S7_TEMPORAL_STABILITY.md](../../../docs/S7/) — Add EXP3 limitations
- [EXPERIMENT_LOG.md](../../../docs/EXPERIMENT_LOG.md) — Full tracking

---

## Key Insight

> "Experiment 3 passing is just to say... yeah, they are doing real work... not drawing in crayon."
> — Ziggy

EXP3 is a **falsifiability gate** for the entire Nyquist stack, not a measurement instrument.

---

**Version:** 2.0
**Date:** 2025-12-04
**Supersedes:** v1.0 (multi-dimensional PFI approach)
**Key Change:** From measurement to binary coherence gate
**Maintainer:** Architect Nova + Repo Claude
