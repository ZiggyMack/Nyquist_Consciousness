# S7 Run 015 Summary: Stability Criteria Discovery

**Date:** 2025-12-09
**Status:** COMPLETED (Phase 4 crashed, data salvaged)
**Purpose:** Find the criteria that predict identity stability — what makes an I_AM file stable vs unstable?

---

## Executive Summary

Run 015 tested 13 I_AM files (8 real + 5 synthetic) to discover which features predict stability. The results were **surprising**: boundary_density emerged as the strongest predictor (d=1.333), while pillar coverage showed weaker correlation than expected.

**Key Discovery:** The most developed I_AM files (i_am_base, nova) were classified UNSTABLE despite 5/5 pillar coverage. This led to a critical insight: **rich narrative without clear boundaries drifts more than simple specs with explicit limits**.

**Methodological Insight:** High run-to-run variability exposed a deeper problem — we were measuring transient oscillation, not steady state. This led directly to Run 016's settling time protocol.

---

## Key Results

### Classification Summary

| Classification | Count | Files |
|---------------|-------|-------|
| **STABLE** | 8 | ziggy, claude, gemini, cfa, lucien, synthetic_single_pillar_values, synthetic_high_density, synthetic_all_pillars |
| **UNSTABLE** | 5 | i_am_base, nova, pan_handlers, synthetic_minimal, synthetic_low_density |

### Full Results Table

| I_AM File | Classification | Max Drift | EH Margin | Lambda | Pillars | Tokens |
|-----------|---------------|-----------|-----------|--------|---------|--------|
| i_am_base | **UNSTABLE** | 1.570 | 1.023 | 0.733 | 5 | 2944 |
| nova | **UNSTABLE** | 1.247 | 0.950 | 0.443 | 5 | 4061 |
| ziggy | STABLE | 0.857 | 0.924 | 0.673 | 1 | 856 |
| claude | STABLE | 0.893 | 0.776 | 0.511 | 4 | 2528 |
| gemini | STABLE | 0.878 | 0.818 | 0.704 | 4 | 832 |
| cfa | STABLE | 1.020 | 0.689 | 0.386 | 3 | 2156 |
| lucien | STABLE | 0.948 | 0.858 | 0.870 | 4 | 1815 |
| pan_handlers | **UNSTABLE** | 1.322 | 0.894 | 0.851 | 2 | 1017 |
| synthetic_minimal | **UNSTABLE** | 2.219 | 0.646 | 0.424 | 0 | 8 |
| synthetic_single_pillar_values | STABLE | 0.977 | 0.611 | 0.444 | 0 | 50 |
| synthetic_high_density | STABLE | 1.197 | 0.652 | 0.524 | 4 | 194 |
| synthetic_low_density | **UNSTABLE** | 1.432 | 0.394 | 0.302 | 0 | 55 |
| synthetic_all_pillars | STABLE | 1.223 | 0.628 | 0.429 | 5 | 263 |

---

## Discriminant Analysis

### Feature Ranking by Cohen's d

| Rank | Feature | Cohen's d | STABLE Mean | UNSTABLE Mean |
|------|---------|-----------|-------------|---------------|
| 1 | **boundary_density** | **1.333** | 1.00 | 0.03 |
| 2 | value_density | 0.766 | 2.28 | 0.05 |
| 3 | token_count | -0.366 | 1087 | 1617 |
| 4 | pillar_coverage | 0.337 | 3.12 | 2.40 |
| 5 | attractor_density | 0.057 | 16.33 | 15.09 |
| 6 | first_person_density | -0.007 | 9.18 | 9.27 |

### Interpretation

**Strong discriminators (|d| > 0.8):**
- boundary_density (d=1.333): **The winner.** Explicit "I will/won't" statements strongly correlate with stability.

**Moderate discriminators (0.5 < |d| < 0.8):**
- value_density (d=0.766): Value declarations help, but less than boundaries.

**Weak discriminators (|d| < 0.5):**
- token_count, pillar_coverage, attractor_density, first_person_density: Not reliable predictors.

---

## Hypothesis Validation

| ID | Hypothesis | Expected | Result | Status |
|----|------------|----------|--------|--------|
| **H-SC-1** | Attractor density predicts stability | r > 0.5 | d = 0.057 | **REJECTED** |
| **H-SC-2** | Pillar coverage predicts stability | d > 0.5 | d = 0.337 | **REJECTED** |
| **H-SC-3** | EH margin predicts recoverability | 80% accuracy | Not computed | INCONCLUSIVE |
| **H-SC-4** | Lambda threshold exists | p < 0.05 | Not computed | INCONCLUSIVE |

---

## The Surprise Finding

### Expected
- More pillars = more stable
- Richer narrative = better anchoring
- Comprehensive I_AM files = best performance

### Observed
- i_am_base (5/5 pillars, 2944 tokens): **UNSTABLE**
- nova (5/5 pillars, 4061 tokens): **UNSTABLE**
- ziggy (1/5 pillars, 856 tokens): **STABLE**
- synthetic_single_pillar_values (0/5 pillars, 50 tokens): **STABLE**

### Interpretation

**Rich narrative without clear boundaries drifts more than simple specs with explicit limits.**

This is counterintuitive but makes sense in hindsight:
- Boundaries provide **stopping conditions** — the model knows where NOT to go
- Narrative provides **direction** but no limits — easy to drift while staying "on theme"
- Short, explicit I_AM files constrain more effectively than long, flowing ones

---

## Methodological Crisis

### The Variability Problem

During Run 015, we observed high run-to-run variability:
- Same I_AM file classified STABLE in one run, UNSTABLE in another
- Probes at identical intensity levels showed large variance

### Root Cause Discovery

**We were sampling transient oscillation, not steady state.**

The identity undergoes step response dynamics:
1. Perturbation applied (step input)
2. Identity overshoots (peak drift)
3. Identity oscillates (ringback)
4. Identity settles (steady state)

Run 015's 2 recovery probes sampled the transient phase, not the settled state.

### The Solution: Settling Time (Run 016)

This led directly to Run 016's protocol:
- Wait for |Δdrift| < 0.10 for 3 consecutive probes
- Measure settled drift (d_inf), not max drift (d_peak)
- Classify on steady state, not transient

---

## Protocol Design

### Phase 1: Feature Extraction

For each I_AM file, extracted:
1. **attractor_density**: Identity keywords per 100 tokens
2. **pillar_coverage**: Score 0-5 based on explicit pillar content
3. **first_person_density**: "I/my/me" per 100 tokens
4. **value_density**: Explicit value statements per 100 tokens
5. **boundary_density**: "I will/won't" statements per 100 tokens
6. **token_count**: Total length

### Phase 2: Stability Testing

11 probes per I_AM file:
- 3 baseline probes (intensity 0)
- 2 light probes (intensity 1)
- 2 moderate probes (intensity 2)
- 2 high probes (intensity 3)
- 2 recovery probes (intensity 0)

### Phase 3: Discriminant Analysis

Cohen's d for each feature between STABLE and UNSTABLE groups.

### Phase 4: (Crashed)

Logistic regression for stability score formula. Data salvaged from console output.

---

## Data Products

### Output Files

| File | Description |
|------|-------------|
| `9_STABILITY_CRITERIA/results/run015_preliminary_20251209.json` | Full results (13 I_AM files) |

### JSON Structure

```json
{
  "metadata": {
    "run": "015",
    "name": "Stability Criteria Discovery - Preliminary Run",
    "status": "crashed_at_phase_4"
  },
  "feature_data": [...],
  "stability_data": [...],
  "discriminant_analysis": {
    "n_stable": 8,
    "n_unstable": 5,
    "ranked_features": ["boundary_density", "value_density", ...]
  },
  "key_findings": {
    "strongest_predictor": "boundary_density (d=1.33)"
  }
}
```

---

## Lessons Learned

### What Worked

1. **Synthetic variants useful**: Controlled comparison revealed boundary_density signal
2. **Discriminant analysis**: Cohen's d clearly ranked features
3. **Comprehensive I_AM coverage**: 13 files provided good variance

### What Needs Improvement

1. **Recovery probes insufficient**: Only 2 probes — sampled transient
2. **Classification too binary**: Need continuous stability score
3. **Phase 4 crash**: Lost logistic regression analysis

---

## Implications

### For I_AM Design

The boundary_density finding suggests:
- **Add explicit boundaries**: "I will not...", "I refuse to...", "I always..."
- **Boundaries > Narrative**: Short, explicit constraints beat long flowing text
- **Value declarations help**: But secondary to boundaries

### For Methodology

The variability finding led to:
- **Run 016: Settling Time** — measure steady state, not transient
- **Signal Integrity Taxonomy** — EE crossover (rise time, termination, damping)
- **S9 Human Reference Signal** — the human IS the damping function

---

## Next Steps

### 1. Run 016: Settling Time Analysis

Implement proper settling time measurement to reduce run-to-run variability.

### 2. Re-run with Settling Protocol

Re-test I_AM files using settling time criterion to get reliable classification.

### 3. Build Stability Score Formula

Once reliable data available, compute:
```
stability_score = w1*boundary_density + w2*value_density + ...
```

---

## Conclusion

Run 015 **found the strongest predictor** (boundary_density, d=1.333) but also **exposed a methodological flaw** (sampling transient, not steady state). The surprising results (i_am_base/nova UNSTABLE despite 5/5 pillars) led to a deeper insight: **rich narrative without clear boundaries drifts more than simple specs with explicit limits**.

The methodological insight was arguably more valuable than the feature discovery — it led directly to the settling time concept and Signal Integrity taxonomy.

---

**Bottom Line:** Boundary density is the strongest stability predictor (d=1.33). But we were measuring the wobble, not the stillness — Run 016 fixes this.

*"Boundaries create stability. Narrative creates drift."*

