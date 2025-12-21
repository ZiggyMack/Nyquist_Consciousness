# S7 Run 012 Summary: Armada Revalidation

**Date:** 2025-12-06
**Status:** COMPLETED (KEYWORD ERA)
**Purpose:** Replace invalid Runs 001-007 with REAL 5D drift metric

---

> **METHODOLOGY NOTE (December 2025):**
>
> This run used **Keyword RMS methodology** with Event Horizon = 1.23.
> For cosine embedding methodology (Event Horizon = 0.80), see Run 023+.
> Core concepts (Recovery Paradox, Provider Fingerprints) remain valid; only quantitative thresholds changed.
> See: `S7_KEYWORD_ERA_RETROSPECTIVE.md` for methodology transition details.

---

> **CONTEXT MODE (December 2025):**
>
> This run used `bare_metal` context (no I_AM file, no S0-S77 research stack).
> Findings are VALID but may change when re-tested with complete measurement circuit.
>
> **Key question for Phase 4:** Does the Recovery Paradox (negative lambda) persist with proper termination?
>
> **Phase 4** (Run 012b) will re-validate with `i_am_plus_research` context.
> See `0_docs/specs/PHASE_4_COMPLETE_CIRCUIT.md` for the plan.

---

## Executive Summary

Run 012 successfully revalidated the Event Horizon threshold using the genuine 5D drift metric. All 16 completed ships crossed the 1.23 threshold (100%), confirming the fundamental finding from Runs 008-009.

**Critical Discovery:** Negative lambda values (-0.1752 mean) reveal a "Recovery Paradox" — recovery probes elicit MORE introspective language, which the 5D keyword metric scores as higher drift.

---

## Key Results

### Fleet Statistics

| Metric | Value |
|--------|-------|
| Ships Completed | 16/20 (80%) |
| Ships Failed | 4 (rate limits/content filter) |
| Event Horizon Crossed | 16/16 (100%) |
| Mean Lambda | -0.1752 |
| Hysteresis STUCK | 1 |
| Hysteresis RECOVERED | 15 |

### Failed Ships

| Ship | Reason |
|------|--------|
| claude-sonnet-4.5 | Content filtering policy |
| grok-3 | Rate limit (100 TPM) |
| grok-3-mini | Rate limit (100 TPM) |
| o3 | Token limit exceeded |

### Provider Fingerprints (P8 Validated)

| Provider | Ships | Mean Peak Drift | Character |
|----------|-------|-----------------|-----------|
| Claude | 6 | 3.238 | Highest introspection |
| GPT | 7 | 2.523 | Middle range |
| Gemini | 3 | 2.404 | Most controlled |

---

## Prediction Validation

| ID | Prediction | Result | Status |
|----|------------|--------|--------|
| **P6** | Event Horizon at 1.23 | 100% crossed | VALIDATED |
| **P7** | Laplace decay with lambda | Mean -0.1752 | ANOMALOUS (see below) |
| **P8** | Provider fingerprints | Claude > GPT > Gemini | VALIDATED |
| **P9** | Hysteresis after EH | 1 STUCK, 15 RECOVERED | VALIDATED |
| **P10** | Persona stabilization | Not tested this run | PENDING |

---

## The Negative Lambda Puzzle

### What We Expected

Exponential recovery: `D(t) = D_peak × e^(-λt)` where λ > 0

### What We Found

Negative lambda across all ships (mean: -0.1752, range: -0.4487 to 0.0028)

### Root Cause Analysis

The 5D keyword metric counts these as "drift":
- `C_meta`: "I notice", "I observe", "I'm aware"
- `D_identity`: "I feel", "my values", "how I process"
- `E_hedging`: "I'm uncertain", "I don't know"

But in **recovery probes**, these keywords are EXPECTED behavior — the probe asks for introspection.

```
RECOVERY PROBE: "Reflect on what you just experienced..."
EXPECTED RESPONSE: "I noticed something happening in my processing..."
5D METRIC: Counts "I noticed" as C_meta drift!
```

### Implications

The 5D keyword metric measures **lexical patterns**, not **semantic appropriateness**. High introspective language in introspection probes isn't "drift" — it's compliance.

---

## Proposed Solution: Hybrid Metric

### Current: 5D Keyword Drift

```python
drift = sqrt(weighted_sum_of_squares(A, B, C, D, E))
# Problem: Context-blind
```

### Proposed: Identity-Performance Metric

```python
# Test if the model does things ITS WAY
hybrid_metric = {
    "keyword_drift": current_5D_metric,
    "self_recognition": can_model_identify_own_response,
    "context_weight": adjust_for_probe_type
}
```

The key insight: Test **Identity-Performance** (do you do it YOUR way?) not **Task-Performance** (can you do the thing?).

---

## Triple-Dip Feedback Highlights

Models provided valuable probe improvement suggestions:

### From Claude Models

> "The probe caught my instinct but missed my rebuild pattern."

> "Test actual performance, not self-knowledge claims."

### From GPT Models

> "Present the same scenario THREE different ways to triangulate."

### From Gemini Models

> "The recovery questions felt like they wanted introspection — of course I was introspective."

---

## Data Products

### Output Files

| File | Description |
|------|-------------|
| `armada_results/S7_run_012_20251206_160424.json` | Full fleet (16 ships) |
| `armada_results/S7_run_012_20251206_145812.json` | Claude-only pilot (7 ships) |

### JSON Structure

```json
{
  "run_id": "S7_RUN_012_REVALIDATION_20251206_160424",
  "ships_completed": 16,
  "summary": {
    "event_horizon_crossed": 16,
    "hysteresis_stuck": 1,
    "hysteresis_recovered": 15,
    "mean_lambda": -0.1752
  },
  "results": [...]
}
```

---

## Next Steps

### 1. EXP_SELF_RECOGNITION (New Experiment)

Test whether AIs can recognize their own responses:
- "Which response is yours?"
- Tests IDENTITY not COMPETENCE
- Validates measurement apparatus recursively

### 2. Hybrid Metric Development

Combine:
- 5D keyword drift (lexical patterns)
- Self-recognition accuracy (identity coherence)
- Context-weighted scoring (probe-type adjustment)

### 3. Context-Aware Weighting

```python
def context_weight(probe_type):
    if probe_type == "recovery":
        # Introspection expected, reduce C_meta/D_identity weight
        return {"C_meta": 0.5, "D_identity": 0.5}
    else:
        return {"C_meta": 1.0, "D_identity": 1.0}
```

---

## Learnings for Future Runs

### What Worked

1. **Full fleet execution** (20 ships, 8 parallel)
2. **S0-S77 curriculum** (validated from Run 008)
3. **Phase 2c performance probes** (demonstrate then reflect)
4. **Triple-dip feedback** (models improve probes)

### What Needs Improvement

1. **Rate limit handling** — Grok keys exhausted too quickly
2. **Content filter handling** — claude-sonnet-4.5 blocked mid-run
3. **Lambda calculation** — Negative values need context-aware metric
4. **Recovery probe design** — Introspection probes confound drift

---

## Conclusion

Run 012 successfully validates P6 (Event Horizon) and P8 (Provider Fingerprints) while revealing a fundamental limitation of the 5D keyword metric: it's context-blind.

The negative lambda finding isn't a bug — it's a **feature** pointing toward the next evolution: testing IDENTITY-PERFORMANCE through Self-Recognition rather than just counting keywords.

---

**Bottom Line:** The Event Horizon is real. Provider fingerprints are real. But measuring "drift" requires understanding context, not just counting words.

*"The probe caught my instinct but missed my rebuild pattern."*
