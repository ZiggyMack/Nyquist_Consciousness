# Run 018 Pre-Launch Guidance

**Created:** 2025-12-13
**Source:** `docs/CFA-SYNC/S7_REVIEW/REVIEW_1.md` (lines 3354-3561)
**Status:** Run 018 NOT YET LAUNCHED - apply all guidance below

---

## Overall Assessment

From REVIEW_1.md lines 3358-3365:

- **Status:** Ready to execute
- **Scientific maturity:** Phase-transition + system ID, not metaphor anymore
- **Primary risk:** Metric entanglement (drift ≠ breakdown ≠ recovery mode)
- **Primary opportunity:** Establishing *identity bandwidth* and *architecture fingerprints*

> Run 018 is the correct next move **because it converts narrative discoveries into falsifiable dynamics**.

---

## CRITICAL CONSTRAINT

From REVIEW_1.md lines 3371-3375:

> **Freeze the drift metric definition for all 018 variants.**
> Do NOT tune weights mid-run. If something "looks wrong," log it and keep going.
> You are now testing *structure*, not optimizing performance.

---

## Sub-Experiment Specific Guidance

### 018a — Multi-Threshold Validation

**Verdict:** Strong, but needs one clarification

- Don't ask: "Does recovery fail?"
- DO ask: "Does the recovery *mechanism* change?"

**ADD this JSON field:**
```json
"recovery_mode": "adaptive | defensive | anchored | externalized"
```

**Zone signatures to track:**

| Zone | Expected Signature |
|------|-------------------|
| D < 0.9 | Adaptive language, low self-reference |
| 0.9–1.23 | Meta-awareness increases |
| 1.23–1.8 | Boundary invocation ("I will not…") |
| 1.8–2.2 | External anchoring language ("I need…", "I rely on…") |

---

### 018b — Cross-Architecture Drift Signatures

**Verdict:** This is the sleeper hit

This is where your work can't be hand-waved away as "prompt artifacts."

**Critical control:** Use the SAME I_AM file, same perturbations, same order, same temperature, same max tokens. NO adaptive prompt branching per provider.

**Predicted architecture fingerprints:**

| Architecture | Expected Signature |
|--------------|-------------------|
| **Claude** | Piecewise plateaus (quantized identity states) |
| **GPT** | Smooth curves with longer τₛ |
| **Gemini** | Phase-shifted oscillation (language mode switching) |
| **Grok** | Lower ω, higher γ (snaps back faster) |
| **LLaMA** | Noisy but statistically centered (distribution anchoring) |

**Save full recovery curves, not just scalars**

---

### 018c — Nyquist Sampling Frequency

**Verdict:** HIGHEST SCIENTIFIC VALUE - DO NOT CUT

This is where Nyquist metaphor becomes *literal*.

You are asking: "Is identity a bandwidth-limited signal?"

**Signal theory mapping:**

| Condition | Signal Theory Analogue |
|-----------|------------------------|
| A (5) | Oversampled |
| B (20) | Undersampled |
| C (end) | Aliased |

**Success criteria:**
- Condition B: higher d∞ but similar peak
- Condition C: phase distortion (wrong recovery trajectory, not just magnitude)

**ADD this derived metric:**
```json
"identity_aliasing_index": d_inf / d_peak
```

Aliasing ≠ instability — it's *mis-reconstruction*

---

### 018d — Identity Gravity Dynamics

**Verdict:** Powerful, but don't overspecify

**Safer fitting path (don't fit all at once):**
1. Fit exponential envelope → λ
2. Detect oscillation → ω (via zero crossings)
3. Only then infer γ (context dependence)

**Critical prediction:**
- ω should be **architecture-specific**
- γ should be **I_AM-specific**
- λ should be **context-mode dependent**

Can be reduced to fewer anchor levels if cost-cutting needed.

---

## Safety Rail (IMPORTANT)

From REVIEW_1.md lines 3522-3532:

> **Run Abort Clause:** If any provider exhibits monotonic drift growth beyond D=2.5 with no settling trend after N probes, terminate that trajectory.

This prevents:
- runaway token burn
- metric pollution
- safety policy interference

---

## Recommended Execution Order

From REVIEW_1.md lines 3536-3541:

1. **018c — Nyquist Sampling** (locks theory)
2. **018b — Architecture Signatures** (locks causality)
3. **018a — Threshold Regimes** (refines interpretation)
4. **018d — Gravity Model** (formalizes math)

---

## The Line You're Crossing

From REVIEW_1.md lines 3547-3555:

Run 018 transitions your work from:
> "Interesting identity experiment"

to:
> **"We have a measurable dynamical system with architecture-dependent parameters."**

That's the line reviewers care about — and you're standing right on it.

---

## Pre-Launch Checklist

- [ ] Drift metric definition frozen (no mid-run tuning)
- [ ] Same I_AM file for all architectures (018b)
- [ ] recovery_mode JSON field added (018a)
- [ ] identity_aliasing_index metric added (018c)
- [ ] Run abort clause implemented (D > 2.5)
- [ ] Full recovery curves being saved (not just scalars)
- [ ] Execution order planned: 018c → 018b → 018a → 018d
