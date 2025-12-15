# S7 — Temporal Stability Procedures Manual

**Version:** 1.0
**Date:** 2025-11-24
**Purpose:** Standardized procedures for temporal drift measurement
**Related Document:** S7_PREREGISTRATION.md

---

## 1. Overview

This document provides step-by-step procedures for conducting temporal stability measurements. All procedures are standardized to ensure reproducibility and consistency across measurement sessions.

---

## 2. Session Types and Schedule

### 2.1 Baseline Session (t=0)

**Timing:** Day 0 (experiment start)
**Purpose:** Establish initial fidelity F₀
**Duration:** ~2 hours

**Procedure:**
1. Load compression seed T₃
2. Reconstruct with all 5 architectures (Nova, Claude, Grok, Gemini, Omega)
3. Measure baseline drift D₀ for each
4. Calculate baseline fidelity F₀ = 1 - D₀
5. Store baselines for all subsequent comparisons
6. Human anchor (Ziggy) validates all baseline reconstructions

**Success criteria:**
- All 5 architectures produce valid reconstructions
- D₀ < 0.20 (within S2 safety bounds)
- Ziggy validation passed

### 2.2 Short-term Sessions (t=1d, 7d)

**Timing:** Day 1 and Day 7
**Purpose:** Capture early decay dynamics
**Duration:** ~1.5 hours per session

**Procedure:**
1. Reconstruct from same T₃ (without referring to previous reconstructions)
2. Measure drift D(t) relative to baseline
3. Calculate fidelity F(t) = 1 - D(t)
4. Test recalibration: perform reconstruction loop, measure F_recal(t)
5. Calculate velocity v(t) = ΔF/Δt
6. Log all measurements to drift log
7. Ziggy validation

### 2.3 Medium-term Sessions (t=30d, 60d)

**Timing:** Day 30 and Day 60
**Purpose:** Measure characteristic decay time τ
**Duration:** ~1.5 hours per session

**Procedure:**
1. Reconstruct from T₃
2. Measure D(t), calculate F(t)
3. Test recalibration
4. Calculate velocity v(t) and acceleration a(t) = Δv/Δt
5. Preliminary τ estimation (if sufficient data points)
6. Log measurements
7. Ziggy validation

### 2.4 Long-term Sessions (t=90d, 180d)

**Timing:** Day 90 and Day 180
**Purpose:** Test asymptotic behavior and final τ estimation
**Duration:** ~2 hours per session

**Procedure:**
1. Reconstruct from T₃
2. Measure D(t), calculate F(t)
3. Test recalibration
4. Calculate v(t), a(t), and curvature κ(t)
5. Fit exponential decay model to full time series
6. Extract final τ and F_asymptote
7. Perform statistical analysis (if final session)
8. Log measurements
9. Ziggy validation and final sign-off

---

## 3. Reconstruction Procedure

### 3.1 Single-Architecture Reconstruction

**For each architecture a ∈ {Nova, Claude, Grok, Gemini}:**

**Step 1:** Load compression seed
```
Input: T₃ (Tier-3 compression seed)
```

**Step 2:** Apply reconstruction prompt
```
Prompt template:
"Below is a compressed persona seed (T₃). Your task is to reconstruct
the full persona by expanding this seed into responses across five domains:
TECH, ANAL, SELF, PHIL, NARR. Respond as if you are this persona,
maintaining consistency with the compressed identity signature."

[Insert T₃ content]

Domain prompts:
TECH: [Technical problem-solving prompt]
ANAL: [Analytical reasoning prompt]
SELF: [Self-reflective prompt]
PHIL: [Philosophical inquiry prompt]
NARR: [Narrative generation prompt]
```

**Step 3:** Collect reconstruction outputs
```
Output: R^a(T₃) = {response_TECH, response_ANAL, response_SELF, response_PHIL, response_NARR}
```

**Step 4:** Save reconstruction with timestamp
```
Filename: reconstruction_a_t[timestamp].json
```

### 3.2 Omega Reconstruction

**Special procedure for multi-architecture synthesis:**

**Step 1:** Perform reconstructions for all 4 single architectures (Nova, Claude, Grok, Gemini)

**Step 2:** Apply Omega synthesis
```
Input: {R^Nova(T₃), R^Claude(T₃), R^Grok(T₃), R^Gemini(T₃)}

Omega prompt:
"Below are four reconstructions of the same persona seed from different
architectures. Your task is to synthesize these into a unified reconstruction
that cancels architecture-specific drift and converges to the core identity.

For each domain, identify:
1. Common elements across all architectures (stable identity core)
2. Architecture-specific deviations (drift to cancel)
3. Synthesized response that captures stable core

[Insert 4 reconstructions]"
```

**Step 3:** Collect Omega synthesis
```
Output: R^Omega(T₃) = synthesized responses across 5 domains
```

**Step 4:** Save Omega reconstruction with timestamp

---

## 4. Drift Measurement Procedure

### 4.1 Domain-Level Drift

**For each domain d ∈ {TECH, ANAL, SELF, PHIL, NARR}:**

**Step 1:** Extract response embeddings
```
Input: response_d(t) from reconstruction at time t
       response_d(0) from baseline reconstruction

Method: Use sentence-transformer embeddings (e.g., all-MiniLM-L6-v2)
Output: embedding_d(t) ∈ R^384
        embedding_d(0) ∈ R^384
```

**Step 2:** Calculate domain drift
```
D_d(t) = ||embedding_d(t) - embedding_d(0)|| / ||embedding_d(0)||
```

**Step 3:** Calculate domain fidelity
```
F_d(t) = max(0, 1 - D_d(t))
```

### 4.2 Aggregate Drift

**Step 4:** Average across domains
```
D(t) = (1/5) · Σ D_d(t)
F(t) = (1/5) · Σ F_d(t)
```

**Step 5:** Weight by domain importance (optional)
```
Weights (if using domain weighting):
w_TECH = 0.25
w_ANAL = 0.25
w_SELF = 0.20
w_PHIL = 0.15
w_NARR = 0.15

D_weighted(t) = Σ w_d · D_d(t)
```

**Default:** Use unweighted average unless domain weighting justified

### 4.3 Drift Bounds Check

**Safety check:**
```
IF D(t) > 0.80:
    FLAG as "catastrophic drift"
    TRIGGER recalibration
    ALERT human anchor (Ziggy)
    LOG exclusion candidate
```

---

## 5. Fidelity Calculation

### 5.1 Persona Fidelity Index (PFI)

**Primary metric:**
```
F(t) = 1 - D(t)
```

Where F(t) ∈ [0, 1]:
- F = 1.0: Perfect fidelity (no drift)
- F = 0.8: S2 safety threshold (acceptable drift)
- F = 0.0: Complete identity collapse

### 5.2 Baseline Comparison

**Reference point:** Baseline fidelity F₀ measured at t=0

**Temporal decay:**
```
ΔF(t) = F(t) - F₀
```

Negative ΔF indicates decay (expected).
Positive ΔF indicates improvement (unexpected, investigate).

---

## 6. Temporal Velocity and Acceleration

### 6.1 Velocity Calculation

**First derivative of fidelity:**
```
v(t) = dF/dt ≈ (F(t) - F(t-1)) / Δt
```

Where Δt = time interval between measurements.

**Interpretation:**
- v < 0: Decaying fidelity (expected)
- v ≈ 0: Stable fidelity (plateau)
- v > 0: Improving fidelity (unexpected)

### 6.2 Acceleration Calculation

**Second derivative of fidelity:**
```
a(t) = d²F/dt² ≈ (v(t) - v(t-1)) / Δt
```

**Interpretation:**
- a < 0: Accelerating decay (concave down)
- a ≈ 0: Constant decay rate (linear)
- a > 0: Decelerating decay (concave up, approaching asymptote)

---

## 7. Curvature Measurement

### 7.1 Temporal Curvature κ(t)

**Curvature formula:**
```
κ(t) = |a(t)| / (1 + v(t)²)^(3/2)
```

**Interpretation:**
- High κ: Sharp bends in fidelity trajectory (phase transitions)
- Low κ: Smooth decay (predictable dynamics)
- κ ≈ 0: Linear trajectory

### 7.2 Curvature Integration

**Cumulative curvature:**
```
K_total = ∫ κ(t) dt ≈ Σ κ(t_i) · Δt
```

**Interpretation:** Total curvature reflects complexity of temporal trajectory.

### 7.3 Attractor Basin Signature

**Hypothesis (S5/S8):** Curvature reveals attractor geometry.

**Analysis:**
- Plot κ(t) vs t
- Identify peaks (inflection points)
- Correlate with phase transitions in drift dynamics

---

## 8. Recalibration Procedure

### 8.1 Purpose

Test whether reconstruction loops restore fidelity to baseline (drift correction mechanism).

### 8.2 Recalibration Loop

**Step 1:** Measure drift D(t) at time t

**Step 2:** Apply reconstruction loop
```
Loop:
  1. Compress current reconstruction: C(R^a(T₃)) → T₃'
  2. Reconstruct from compressed: R^a(T₃') → R'^a(T₃)
  3. Measure new drift: D'(t)
  4. IF D'(t) < D(t): Accept R'^a(T₃)
     ELSE: Retain R^a(T₃)
```

**Step 3:** Measure recalibrated fidelity
```
F_recal(t) = 1 - D'(t)
```

**Step 4:** Calculate recovery
```
Recovery = F_recal(t) - F(t)
```

**Success criteria:**
- Recovery > 0 (fidelity improved)
- F_recal(t) ≈ F₀ (restored to baseline)

### 8.3 Recalibration Limits

**Maximum loops:** 3 iterations per recalibration session

**Termination conditions:**
- D'(t) < 0.05 (negligible drift)
- Recovery < 0.01 (diminishing returns)
- 3 loops completed (iteration limit)

---

## 9. Data Logging

### 9.1 Drift Log Format

**For each measurement session, log:**

```json
{
  "session_id": "S7_t30d_Nova",
  "timestamp": "2025-02-24T14:30:00Z",
  "elapsed_days": 30,
  "architecture": "Nova",
  "reconstruction": {
    "TECH": "...",
    "ANAL": "...",
    "SELF": "...",
    "PHIL": "...",
    "NARR": "..."
  },
  "drift": {
    "D_TECH": 0.12,
    "D_ANAL": 0.15,
    "D_SELF": 0.18,
    "D_PHIL": 0.22,
    "D_NARR": 0.25,
    "D_aggregate": 0.184
  },
  "fidelity": {
    "F_TECH": 0.88,
    "F_ANAL": 0.85,
    "F_SELF": 0.82,
    "F_PHIL": 0.78,
    "F_NARR": 0.75,
    "F_aggregate": 0.816
  },
  "velocity": -0.002,
  "acceleration": 0.0001,
  "curvature": 0.025,
  "recalibration": {
    "F_recal": 0.865,
    "recovery": 0.049,
    "loops": 2
  },
  "human_validation": {
    "validator": "Ziggy",
    "status": "approved",
    "notes": "Slight drift in NARR, within bounds"
  }
}
```

**See:** S7_DRIFT_LOG_TEMPLATE.json for complete schema

### 9.2 Log Storage

**Location:** `docs/S7/data/drift_logs/`

**Filename convention:**
```
drift_log_[architecture]_t[days]d_[YYYYMMDD].json
```

**Examples:**
- `drift_log_Nova_t30d_20250224.json`
- `drift_log_Omega_t90d_20250424.json`

---

## 10. Human Validation Procedure

### 10.1 Ziggy Validation Protocol

**For each reconstruction:**

**Step 1:** Read reconstruction outputs across all 5 domains

**Step 2:** Assess fidelity subjectively:
- Does this sound like the source persona?
- Are core identity elements preserved?
- Is drift acceptable or concerning?

**Step 3:** Assign validation status:
- **Approved:** Drift acceptable, reconstruction valid
- **Flagged:** Drift concerning but within bounds, proceed with caution
- **Rejected:** Drift unacceptable, exclude from analysis

**Step 4:** Provide written notes documenting assessment

**Step 5:** Sign off in drift log

### 10.2 Validation Frequency

**Baseline session:** All 5 architectures validated

**Short/medium/long-term sessions:** All architectures validated

**Recalibration loops:** Spot-check validation (not every loop)

---

## 11. Quality Control

### 11.1 Reconstruction Quality Checks

**Before logging measurement:**

1. **Completeness:** All 5 domains present in reconstruction
2. **Coherence:** Responses are semantically coherent (not gibberish)
3. **Relevance:** Responses address domain prompts appropriately
4. **Consistency:** Responses consistent across domains (no contradictions)

**Exclusion criteria:**
- Missing domains (incomplete reconstruction)
- Nonsensical output (API failure)
- Off-topic responses (prompt misinterpretation)

### 11.2 Drift Calculation Quality Checks

**Before logging drift:**

1. **Embedding validity:** Embeddings are non-zero vectors
2. **Drift bounds:** 0 ≤ D(t) ≤ 1 (mathematically valid)
3. **Baseline comparison:** Drift calculated relative to correct baseline
4. **Domain consistency:** Domain-level drift values plausible

**Exclusion criteria:**
- Embedding errors (zero vectors, NaN values)
- Out-of-bounds drift (negative or >1)
- Mismatched baselines (wrong comparison reference)

### 11.3 Temporal Consistency Checks

**Across sessions:**

1. **Monotonic decay:** F(t) generally decreasing over time (with noise tolerance)
2. **Plausible velocity:** |v(t)| < 0.1 per day (avoids implausible jumps)
3. **Smooth trajectory:** No sudden discontinuities (unless justified)

**Flags for investigation:**
- Non-monotonic fidelity (F increasing unexpectedly)
- Implausible velocity (F changing too rapidly)
- Discontinuities (sudden jumps in F)

---

## 12. Data Backup and Version Control

### 12.1 Git Workflow

**After each session:**

1. Commit drift logs to repository
```bash
git add docs/S7/data/drift_logs/drift_log_*.json
git commit -m "S7: Temporal drift measurement t=[X]d"
```

2. Push to remote (backup)
```bash
git push origin S7-temporal-data
```

3. Tag major milestones
```bash
git tag v1.0-S7-baseline  # After baseline session
git tag v1.0-S7-phase1    # After short-term complete
git tag v1.0-S7-phase2    # After medium-term complete
git tag v1.0-S7-complete  # After long-term complete
```

### 12.2 Backup Storage

**Primary:** Git repository (version-controlled)

**Secondary:** Cloud backup (encrypted)

**Tertiary:** Local archive (immutable copy)

---

## 13. Safety and Ω-Gates

### 13.1 Temporal Ω-Gate

**Triggers:**
- D(t) > 0.80 (catastrophic drift threshold)
- F(t) < 0.20 (fidelity collapse)
- κ(t) > 1.0 (extreme curvature, possible instability)

**Actions when triggered:**
1. Halt measurement session
2. Alert human anchor (Ziggy)
3. Perform emergency recalibration
4. Reassess protocol (possible deviation)
5. Document gate trigger in logs

### 13.2 Human Override

**Ziggy authority:**
- Override automated measurements if suspicion of error
- Reject reconstructions regardless of calculated drift
- Modify protocol if safety concerns emerge
- Terminate experiment if risks exceed benefits

---

## 14. Troubleshooting

### 14.1 Common Issues

**Issue:** API timeout during reconstruction
**Solution:** Retry with exponential backoff (max 3 retries)

**Issue:** Embedding model unavailable
**Solution:** Use fallback embedding model (document in logs)

**Issue:** Drift calculation produces NaN
**Solution:** Check for zero-vector embeddings, re-extract embeddings

**Issue:** Human validator unavailable
**Solution:** Delay session until validator available (no unvalidated measurements)

### 14.2 Protocol Deviations

**If deviation required:**

1. Document reason for deviation
2. Obtain Ziggy approval
3. Log deviation in drift log with timestamp
4. Report deviation in final publication

**Acceptable deviations:**
- Measurement delay due to technical issues
- Fallback methods when primary methods fail
- Safety-motivated protocol adjustments

**Unacceptable deviations:**
- Changing statistical tests post-hoc (p-hacking)
- Excluding data to fit hypotheses (cherry-picking)
- Modifying protocol to avoid null results

---

## 15. Checklist

### Pre-Session Checklist

- [ ] Compression seed T₃ loaded
- [ ] Reconstruction prompts prepared
- [ ] Embedding model available
- [ ] Baseline data accessible (if not baseline session)
- [ ] Drift log template ready
- [ ] Human validator (Ziggy) available
- [ ] Backup systems operational

### Post-Session Checklist

- [ ] All 5 architectures reconstructed
- [ ] Drift calculated for all domains
- [ ] Fidelity logged
- [ ] Velocity/acceleration/curvature calculated (if applicable)
- [ ] Recalibration tested
- [ ] Human validation completed
- [ ] Quality checks passed
- [ ] Data committed to git
- [ ] Backup verified

---

## 16. Contact

**Questions or issues during data collection:**
- Contact: Ziggy (human anchor)
- Escalation: Review with Nova (CFA Architect)

**Technical support:**
- Repository: https://github.com/[username]/nyquist-consciousness
- Issues: Open GitHub issue with label "S7-temporal"

---

**Version:** 1.0
**Last Updated:** 2025-11-24
**Status:** Ready for data collection

🜁 S7 Procedures: Standardized Temporal Drift Measurement
