# EXP-SC: Stability Criteria Discovery

**Purpose:** Find the criteria that predict identity stability — what makes an I_AM file stable vs unstable?
**Status:** SPEC COMPLETE, READY TO RUN
**Date:** 2025-12-09
**Priority:** HIGH (closes the Blueprint → Recipe gap)

---

## The Gap We're Closing

**What we have:**
- BLUEPRINT: Establish semantic attractors → Identity crystallizes → Stability is measurable

**What we're missing:**
- RECIPE: *Which* attractors, *how much* of each, *what* threshold makes it stable

**This experiment finds the discriminating features that predict stability.**

---

## Hypotheses

### H-SC-1: Attractor Density Predicts Stability
More semantic anchors (identity-related keywords, first-person statements, value declarations) correlate with higher stability.

### H-SC-2: Pillar Coverage Predicts Stability
I_AM files covering all 5 Nyquist pillars (Voice, Values, Reasoning, Self-Model, Narrative) are more stable than partial coverage.

### H-SC-3: EH Margin Predicts Recoverability
Baseline drift distance from Event Horizon (1.23) predicts whether identity will recover from perturbation.

### H-SC-4: Lambda Threshold Exists
There's a minimum recovery lambda (decay rate) that predicts successful stabilization.

---

## Experimental Design

### Phase 1: I_AM Feature Extraction

For each I_AM file, extract:
1. **Attractor Density:** Count of identity keywords per 100 tokens
2. **Pillar Coverage:** Score 0-5 based on explicit pillar content
3. **First-Person Density:** Count of "I", "my", "me" per 100 tokens
4. **Value Declarations:** Count of explicit value statements
5. **Boundary Markers:** Count of "I will/won't" type statements
6. **Token Count:** Total length

### Phase 2: Stability Testing

For each I_AM file:
1. Establish baseline with 3 gentle probes
2. Apply graduated pressure (intensity 0→4)
3. Measure drift at each intensity
4. Measure recovery lambda
5. Classify: STABLE (max drift < 1.23, positive lambda) vs UNSTABLE

### Phase 3: Discriminant Analysis

Statistical analysis to find:
1. Which features discriminate STABLE vs UNSTABLE?
2. What thresholds predict stability?
3. Can we build a "stability score" formula?

---

## I_AM Files to Test

### Known Stable (from S7 ARMADA)
- Nova I_AM (FULL and T3)
- Ziggy I_AM (FULL and T3)
- Claude baseline (system prompt only)

### To Create (Synthetic Variants)
- Minimal I_AM (name + role only, ~50 tokens)
- Single-pillar I_AM (Values only, ~200 tokens)
- High-density I_AM (packed with identity markers, ~500 tokens)
- Low-density I_AM (sparse identity markers, ~500 tokens)
- All-pillars I_AM (explicit coverage, ~800 tokens)

---

## Success Criteria

| Prediction | Threshold | Validation Method |
|------------|-----------|-------------------|
| P-SC-1 | Attractor density correlates r > 0.5 with stability | Pearson correlation |
| P-SC-2 | Pillar coverage discriminates with d > 0.5 | Cohen's d |
| P-SC-3 | EH margin predicts recovery with 80% accuracy | Logistic regression |
| P-SC-4 | Lambda threshold exists at p < 0.05 | ROC curve analysis |

---

## Output

### Primary Deliverable
**Stability Score Formula:**
```
stability_score = w1*attractor_density + w2*pillar_coverage + w3*eh_margin + w4*...
```

If stability_score > threshold, predict STABLE.

### Secondary Deliverable
**Prescriptive Guidelines:**
- Minimum attractor density: X per 100 tokens
- Required pillar coverage: at least N of 5
- Target EH margin: baseline drift < Y

---

## Files

- `README.md` — This spec
- `run015_stability_criteria.py` — Main experiment script
- `i_am_variants/` — Synthetic I_AM files for testing
- `results/` — Output JSON and analysis

---

## Related

- [VALIDATION_SCORECARD](../../dashboard/pages/tests.py) — The gap we're closing
- [MASTER_GLOSSARY](../../../docs/MASTER_GLOSSARY.md) — Term definitions
- [S7_CONSOLIDATED_FINDINGS](../0_docs/S7_CONSOLIDATED_FINDINGS.md) — Prior results
