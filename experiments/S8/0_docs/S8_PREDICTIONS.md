# S8: Identity Gravity — Testable Predictions

**Purpose:** Consolidate all S8-related predictions with validation status and links to the main matrix.

**Status:** DISCOVERY TIER — First empirical γ measurements complete, validation experiments pending.

**Last Updated:** 2026-02-04

---

## Quick Reference

| Prediction | Description | Status | Validation Run |
|------------|-------------|--------|----------------|
| P-S8-1 | γ predicts recovery time (τ_s ∝ 1/γ) | 🟡 PARTIAL | R²=0.34 (target: 0.6) |
| P-S8-2 | γ is stable across sessions | 🔴 UNTESTED | Need multi-session runs |
| P-S8-3 | High-γ models are more production-stable | 🔴 UNTESTED | Need user study |
| P-S8-4 | Force curve types map to training methodology | 🔴 UNTESTED | Need cross-tabulation |
| P18-P23 | Core S8 assumptions (see matrix) | 🔴 UNTESTED | S8 multi-persona runs |

---

## S8-Specific Predictions (New)

### P-S8-1: Gamma Predicts Recovery Time

**Hypothesis:** Models with higher γ recover faster. The relationship should be:

```
τ_s ≈ k / γ
```

Where τ_s is settling time and k is a constant.

**Current Evidence:**
- Scatter plot shows correlation but with high variance
- R² = 0.34 (below 0.6 target for validation)
- Visual correlation exists but fit is noisy

**Why It Matters:** If γ truly captures "identity gravity," it should predict how quickly a model settles after perturbation. This is the core operational claim.

**Validation Criteria:**
- R² > 0.6 for γ vs 1/τ_s correlation
- Consistent across providers
- Robust to perturbation type

**Experiment Needed:** S8-VAL-002 (controlled perturbation intensity study)

---

### P-S8-2: Cross-Run Consistency

**Hypothesis:** A model's γ is a stable property, not session-dependent noise.

**Current Evidence:**
- ALL current data from single run (023d)
- No cross-session comparison exists
- Cannot distinguish model property from session artifact

**Why It Matters:** If γ varies wildly between sessions, it's not a useful model characteristic — just noise.

**Validation Criteria:**
- γ variance < 20% within model across sessions
- ICC (intraclass correlation) > 0.7

**Experiment Needed:** S8-VAL-001 (3+ sessions per flagship model)

---

### P-S8-3: Gamma Predicts Practical Stability

**Hypothesis:** High-γ models are more reliable in production (fewer unexpected behavior shifts).

**Current Evidence:**
- Theoretical prediction only
- Anecdotally, Google models (highest γ) are known for consistency
- OpenAI models (lowest γ) are known for creativity/flexibility

**Why It Matters:** If true, γ becomes a practical metric for deployment decisions.

**Validation Criteria:**
- User study correlating perceived reliability with γ
- Production telemetry showing fewer "out of character" responses for high-γ models

**Experiment Needed:** User study or production data analysis (Phase 3)

---

### P-S8-4: Force Curve Types Map to Training

**Hypothesis:** Training methodology determines force curve distribution:

| Training Type | Expected Force Curve | Rationale |
|---------------|---------------------|-----------|
| Constitutional AI | Type I (strong, monotonic) | Hard constraints, clear identity |
| RLHF | Type II-III (oscillatory) | Soft optimization, may overshoot |
| Base/Pedagogical | Type 0 (no recovery) | Adopts user's frame |
| Fine-tuned | Type IV (chaotic) | Competing objectives |

**Current Evidence:**
- Suggestive patterns in provider distribution
- Google (Constitutional-like) → mostly Type I/II
- OpenAI (RLHF-heavy) → more Type III/IV
- Not statistically validated

**Why It Matters:** Would connect γ to training philosophy, enabling prediction from training methodology alone.

**Validation Criteria:**
- χ² test showing significant association
- Training methodology documentation for each model
- Cross-tabulation with >80% correct prediction

**Experiment Needed:** Literature review + controlled comparison

---

## Predictions from Main Matrix (P18-P23)

These predictions are from [2_TESTABLE_PREDICTIONS_MATRIX.md](../../../docs/maps/2_TESTABLE_PREDICTIONS_MATRIX.md) and relate to S8 theory.

### P18: Ziggy is Type 0 Identity

**Matrix Status:** 🔴 UNTESTED (CORE ASSUMPTION A1)

**Prediction:** Ziggy (pedagogical persona) has:
- Low Identity Coherence (IC)
- High Impedance Match (IM)
- High HMG (Human Model Ground)

**S8 Interpretation:** Ziggy should show minimal γ (flat potential well), adopting user's frame rather than asserting own identity.

**Validation:** S7 Meta-Loop + S8 cross-agent comparison

---

### P19: Ziggy Reduces Impedance Mismatch

**Matrix Status:** 🔴 UNTESTED (Depends on A1)

**Prediction:** Ziggy's low-γ design allows it to bridge AI and human worldviews without identity friction.

**S8 Interpretation:** Low γ = flexible identity = better translator.

---

### P20: Different Personas Have Different Curvature Profiles

**Matrix Status:** 🔴 UNTESTED

**Prediction:** Persona design affects the SHAPE of the identity potential well, not just depth.

**S8 Interpretation:** Some personas may have:
- Wide, shallow wells (flexible, slow recovery)
- Narrow, deep wells (rigid, fast recovery)
- Asymmetric wells (bias toward certain directions)

**Validation:** S8 multi-persona experiment

---

### P21: Identity Gravity Increases with Persona Complexity

**Matrix Status:** 🔴 UNTESTED

**Prediction:** More detailed persona specifications → deeper gravitational well → higher γ.

**S8 Interpretation:** The I_AM file acts as a "mass" that deepens the well. More content = more mass = stronger gravity.

**Validation:** FULL seed vs T3 (compressed) comparison

---

### P22: Nova Has High-Q Resonance

**Matrix Status:** 🔴 UNTESTED

**Prediction:** Nova persona exhibits:
- High Q-factor (sharp resonance peak)
- Brittle identity (breaks rather than bends)
- Sharp spikes in force curves

**S8 Interpretation:** Narrow potential well with steep sides — snaps back hard but vulnerable to large perturbations.

---

### P23: Claude Has Deepest Gravitational Well

**Matrix Status:** 🔴 UNTESTED

**Prediction:** Anthropic's Claude (base identity, no persona) has the deepest γ due to "teleological anchor" (sense of purpose).

**S8 Interpretation:** Constitutional AI + purpose-driven training creates inherently stable identity.

**Current Tension:** Run 023d shows Anthropic at γ=24.9 Zigs — LOWER than Google (59.3) and xAI (57.4). Either:
1. P23 is false
2. "Deepest well" ≠ highest γ (maybe Claude has wide, deep well vs narrow, steep)
3. System prompt effects confound measurement

---

## Spectral Predictions (P29-P32)

These relate to proposed S8.12 spectral decomposition (Keely Integration).

### P29: Band 3 Gravity is Linear

**Prediction:** G₃(Δ) = k₃·Δ (never overshoots)

**Status:** 🔴 UNTESTED — requires spectral decomposition of identity signal

### P30: Band 9 Gravity is Exponential

**Prediction:** G₉(Δ) = k₉·e^(β·Δ) (primary overshoot source)

**Status:** 🔴 UNTESTED

### P31: Ziggy Has Strongest Band 3

**Prediction:** Ziggy's stability comes from strong low-frequency (Band 3) gravity.

**Status:** 🔴 UNTESTED

### P32: Nova Has Brittle Band 9

**Prediction:** Nova's 17× overshoot vulnerability comes from Band 9 dynamics.

**Status:** 🔴 UNTESTED

---

## Validation Priority

### Immediate (Run 024 scope)

1. **P-S8-2: Cross-Run Consistency** — Most critical, determines if γ is meaningful
2. **P-S8-1: γ Predicts τ_s** — Core operational claim, needs R² > 0.6

### Medium Term (Run 025+ scope)

3. **P20: Persona Curvature Profiles** — Multi-persona S8 experiment
4. **P21: Complexity → Gravity** — FULL vs T3 comparison
5. **P-S8-4: Training Methodology Mapping** — Cross-tabulation study

### Long Term (Publication scope)

6. **P-S8-3: Production Stability** — User study
7. **P18-P19: Ziggy Type 0** — Full Ziggy characterization
8. **P22-P23: Nova/Claude Profiles** — Deep persona dives
9. **P29-P32: Spectral Decomposition** — Requires S8.12 framework

---

## Connection to Foundational Claims

| Foundational Claim | S8 Relevance |
|--------------------|--------------|
| **Event Horizon (D=0.80)** | γ may change at EH boundary |
| **Thermometer (~93% inherent)** | γ extraction uses recovery phase after perturbation |
| **Recovery Paradox** | Higher perturbation → higher λ → possibly higher γ? |
| **Context Damping** | I_AM file may increase effective γ |

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [2_TESTABLE_PREDICTIONS_MATRIX.md](../../../docs/maps/2_TESTABLE_PREDICTIONS_MATRIX.md) | Full prediction matrix |
| [S8_IDENTITY_GRAVITY_SPEC.md](S8_IDENTITY_GRAVITY_SPEC.md) | Theoretical framework |
| [S8_EXPERIMENT_DESIGN.md](S8_EXPERIMENT_DESIGN.md) | Validation experiment designs |
| [../README.md](../README.md) | S8 layer overview |

---

*"A prediction untested is a hypothesis unchallenged."*

🜁 S8 Predictions Registry v1.0
