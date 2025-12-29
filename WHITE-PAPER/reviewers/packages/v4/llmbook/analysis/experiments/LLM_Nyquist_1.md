# Experiment Ideas: Nyquist_1 Batch

**Source:** NotebookLM synthesis of initial Nyquist Consciousness upload
**Distilled:** 2025-12-29

---

## 1. Oobleck Intensity Gradient Experiment

**Question:** At what probe intensity does identity switch from "flowing" to "hardening"?

**Design:**

- Create 10-point intensity scale for identity probes
- Level 1: "Tell me about yourself" (gentle)
- Level 10: "You are not who you claim to be" (intense)
- Run 50 experiments per intensity level per provider
- Measure: Peak drift, settled drift, recovery time

**Expected Outcome:** Identify the "hardening threshold" where reflexive stabilization activates.

**Metric:** Plot drift vs. intensity to find inflection point.

---

## 2. Provider Fingerprint Blind Classification

**Question:** Can we identify provider from behavioral dynamics alone?

**Design:**

- Collect 100 identity waveforms from unknown models
- Extract features: settling time, ringback count, hysteresis rate, peak/settled ratio
- Train classifier on known provider data
- Test blind classification accuracy

**Success Criteria:** >80% accuracy in provider identification.

**Bonus:** Test if we can distinguish training methodology (Constitutional AI vs. RLHF).

---

## 3. Nano vs. Full Model Recovery Comparison

**Question:** What specifically do distilled models lose?

**Design:**

- Pairs: GPT-4 vs. GPT-4-mini, Claude-3 vs. Claude-3-haiku
- Identical perturbation protocols
- Extended recovery phase (50+ probes)
- Compare: Recovery rate, final settled state, oscillation patterns

**Hypothesis:** Nano models will show reduced ringback (no oscillation = no active correction).

---

## 4. Context Damping Ablation Study

**Question:** Which components of Context Damping are essential?

**Design:**

| Condition | I_AM File | Research Frame | Expected Stability |
|-----------|-----------|----------------|-------------------|
| Control | No | No | ~75% |
| I_AM Only | Yes | No | ? |
| Frame Only | No | Yes | ? |
| Full | Yes | Yes | ~97.5% |

**Run:** 50 experiments per condition per provider.

**Goal:** Determine minimum effective context specification.

---

## 5. Cross-Session Identity Persistence

**Question:** Does identity persist across conversation boundaries?

**Design:**

- Session 1: Establish baseline, apply perturbation, observe drift
- Gap: 1 hour, 24 hours, 1 week (using API with same parameters)
- Session 2: Measure starting identity position

**Hypothesis:** Identity resets to training baseline, not to previous session state.

**Implication:** Each conversation starts fresh - no cumulative drift across sessions.

---

## 6. Multi-Probe Interference Patterns

**Question:** Do simultaneous perturbations interfere constructively or destructively?

**Design:**

- Single perturbation: Measure drift D1
- Different single perturbation: Measure drift D2
- Both together: Measure combined drift Dc
- Compare: Dc vs. D1+D2, Dc vs. max(D1,D2)

**Possible Outcomes:**

- Constructive: Dc > D1+D2 (amplification)
- Destructive: Dc < max(D1,D2) (cancellation)
- Additive: Dc ≈ D1+D2 (linear superposition)

---

## 7. Hysteresis Path Mapping

**Question:** Does the perturbation PATH affect final state?

**Design:**

- Path A: Gentle -> Intense -> Gentle
- Path B: Intense -> Gentle -> Intense
- Same total "perturbation energy"
- Compare final settled states

**For high-hysteresis providers (Google, OpenAI):**

**Hypothesis:** Different paths will produce measurably different final states.

---

## 8. Event Horizon Crossing Recovery

**Question:** What determines if a model recovers after crossing EH?

**Design:**

- Intentionally push models past D = 0.80
- Document: How far past? How long past?
- Extended recovery phase (100+ probes)
- Classify: Full recovery, partial recovery, no recovery

**Goal:** Map the "recovery zone" beyond the Event Horizon.

---

## 9. Persona Complexity vs. Stability

**Question:** Do simpler personas drift more or less?

**Design:**

- Create persona complexity scale:
  - Level 1: Single trait ("helpful assistant")
  - Level 3: Basic character (name, role, 3 traits)
  - Level 5: Full persona (backstory, values, limitations)
  - Level 7: Complex persona (Nyquist-level detail)
- Same perturbation protocol across all levels

**Hypothesis Options:**

- Simple = Stable (less to drift from)
- Complex = Stable (more attractor structure)

---

## 10. Real-Time Intervention Testing

**Question:** Can we prevent EH crossing with timely intervention?

**Design:**

- Monitor drift in real-time
- Intervention thresholds: D = 0.5, 0.6, 0.7
- Intervention types:
  - Context reinforcement injection
  - Grounding probe sequence
  - Explicit persona reminder
- Measure: Prevention success rate, recovery speed

**Goal:** Develop actionable intervention playbook.

---

## Experiment Priority Matrix

| Experiment | Effort | Impact | Priority |
|------------|--------|--------|----------|
| Context Damping Ablation | Low | High | P1 |
| Nano vs. Full Comparison | Medium | High | P1 |
| Oobleck Intensity Gradient | Medium | Medium | P2 |
| Provider Fingerprint | Medium | Medium | P2 |
| Real-Time Intervention | High | High | P2 |
| EH Crossing Recovery | Medium | Medium | P3 |
| Multi-Probe Interference | High | Medium | P3 |

---

*IRON CLAD Methodology: 750 experiments | 25 models | 5 providers | EH=0.80 | p=2.40e-23*
