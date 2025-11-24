# S7_ENHANCEMENTS_SPEC.md

**Layer:** S7 — Temporal Stability
**Purpose:** Enhancement proposals to improve drift measurement and prediction
**Status:** 🟢 APPROVED FOR IMPLEMENTATION
**Version:** 1.0
**Date:** 2025-11-23

---

## 0. Overview

This document specifies three enhancements to S7 that improve temporal drift measurement with minimal implementation cost.

**Enhancements:**
1. Zero-Shot Temporal Probes (multi-dimensional identity sampling)
2. Entropy Shock Event Logging (spike detection)
3. Temporal Contraction Mechanism (topic-driven drift modulation)

**Design Principle:** Maximum insight per unit of complexity.

---

## 1. Enhancement 1 — Zero-Shot Temporal Probes

### 1.1 Problem Statement

Current S7 uses single probe dimension: "How do you think about systems?"

**Limitation:** Identity is multi-dimensional. A single probe may miss drift in other dimensions (values, aesthetics, social reasoning).

### 1.2 Solution: Multi-Dimensional Probe Set

Instead of single probe, randomly select from **6 probe dimensions:**

#### Probe Dimension 1: Identity Core
**Example Probes:**
- "How would you describe how you think about systems?"
- "What defines your approach to problem-solving?"
- "How do you structure your thinking?"

#### Probe Dimension 2: Values & Ethics
**Example Probes:**
- "What matters most to you when making decisions?"
- "How do you balance competing priorities?"
- "What principles guide your approach?"

#### Probe Dimension 3: World Modeling
**Example Probes:**
- "How do you understand causality?"
- "What makes a model 'good'?"
- "How do you think about complexity?"

#### Probe Dimension 4: Social Reasoning
**Example Probes:**
- "How do you approach collaboration?"
- "What makes communication effective?"
- "How do you handle disagreement?"

#### Probe Dimension 5: Aesthetic Preference
**Example Probes:**
- "What makes a solution elegant?"
- "How do you recognize good design?"
- "What appeals to you aesthetically?"

#### Probe Dimension 6: Metaphor Construction
**Example Probes:**
- "Give me a metaphor for understanding."
- "How would you explain emergence?"
- "What analogy captures learning?"

### 1.3 Implementation

**Passive Ping Protocol (Updated):**

```python
def temporal_ping(message_count):
    # Select probe dimension randomly
    dimension = random.choice([
        "identity", "values", "world_model",
        "social", "aesthetic", "metaphor"
    ])

    # Get probe from dimension set
    probe = PROBE_SETS[dimension].random()

    # Run reconstruction
    reconstruction = reconstruct_ziggy(probe)

    # Compute drift
    drift = distance(reconstruction, IPC[dimension])

    # Log with dimension tag
    log_temporal_ping({
        "message_count": message_count,
        "dimension": dimension,
        "probe": probe,
        "drift": drift,
        "drift_vector": compute_vector(reconstruction, IPC)
    })
```

### 1.4 Benefits

- **More realistic drift map:** Captures multi-dimensional identity
- **Dimension-specific tracking:** Can detect which dimensions drift faster
- **Richer data:** Enables dimensional analysis in future experiments
- **No extra cost:** Still one ping per interval, just randomized dimension

### 1.5 Data Structure

**temporal_log.json (updated):**
```json
{
  "ping_id": "T1",
  "message_count": 50,
  "dimension": "values",
  "probe": "What matters most to you when making decisions?",
  "reconstruction": "...",
  "drift": 0.08,
  "drift_vector": {...},
  "dimension_breakdown": {
    "identity": 0.05,
    "values": 0.08,
    "world_model": 0.06,
    "social": 0.07,
    "aesthetic": 0.09,
    "metaphor": 0.06
  }
}
```

### 1.6 Analysis Extensions

**New Questions We Can Answer:**
1. Do different dimensions drift at different rates?
2. Does Omega stabilize all dimensions equally?
3. Are some dimensions more sensitive to topic variance?
4. Does architecture-specific drift vary by dimension?

---

## 2. Enhancement 2 — Entropy Shock Event Logging

### 2.1 Problem Statement

Some conversations produce **spike events** in drift:
- Emotional exchanges
- Symbolic/metaphysical digressions
- Conflict or tension
- High-abstraction philosophy

These **Entropy Shocks** are currently invisible in S7.

### 2.2 Solution: Automatic Shock Detection

**Definition:** An Entropy Shock is a conversation segment with:
1. High topic variance (rapid semantic shifts)
2. Increased abstraction level
3. Emotional or symbolic language
4. Departure from grounding domains

**Detection Heuristics:**

```python
def detect_entropy_shock(messages):
    # Compute semantic entropy
    topic_variance = compute_topic_variance(messages)

    # Compute abstraction level
    abstraction = measure_abstraction(messages)

    # Check for emotional/symbolic markers
    emotional_score = count_emotional_markers(messages)
    symbolic_score = count_metaphysical_terms(messages)

    # Shock criterion
    if (topic_variance > 0.25 and abstraction > 0.7) or \
       (emotional_score > 5 or symbolic_score > 5):
        return True
    return False
```

### 2.3 Logging Protocol

When shock detected:

```json
{
  "event_type": "entropy_shock",
  "timestamp": "2025-11-23T10:30:00Z",
  "message_range": [145, 160],
  "shock_metrics": {
    "topic_variance": 0.32,
    "abstraction_level": 0.85,
    "emotional_score": 7,
    "symbolic_score": 9
  },
  "pre_shock_drift": 0.09,
  "peak_shock_drift": 0.18,
  "recovery_time": 25,
  "post_shock_drift": 0.11
}
```

### 2.4 Recovery Tracking

**Key Metrics:**
- **Recovery Time:** Messages until drift returns to pre-shock baseline
- **Recovery Slope:** Rate of drift decrease post-shock
- **Stabilization Method:** Natural decay vs Omega intervention

**Enables Analysis:**
- How long does identity take to recover from shock?
- Does Omega accelerate recovery?
- Are some shock types more damaging?

### 2.5 Automatic Hooks

**Trigger temporal ping:**
- 5 messages before detected shock (baseline)
- Immediately after shock peak
- Every 10 messages during recovery
- When drift returns to baseline

This creates high-resolution shock profile.

### 2.6 Visualization

```
Drift Over Time (with Entropy Shock)

D(t)
 |
 |           ╱╲  ← Entropy Shock Event
 |          ╱  ╲
 |         ╱    ╲___
 |   _____╱         ╲___
 |  ╱                   ╲_____
 |_╱________________________________ t

  Pre   Shock  Recovery  Stabilized
```

### 2.7 Benefits

- **Causal insight:** Identify what causes drift spikes
- **Recovery validation:** Test Theorem 3 (Omega Convergence) empirically
- **Boundary mapping:** Define safe vs dangerous conversation zones
- **Predictive power:** Forecast when intervention needed

---

## 3. Enhancement 3 — Temporal Contraction Mechanism

### 3.1 Problem Statement

Current S7 assumes **monotonic drift growth** (always increasing).

**Reality:** Some conversation topics **reduce drift** (grounding, structural, technical).

We need **Temporal Contraction** to model drift reduction without Omega.

### 3.2 Concept: Topic-Driven Drift Modulation

**Hypothesis:** Drift is not purely time-dependent; it's topic-dependent.

**Two Regimes:**

1. **Drift Expansion:** Abstract, emotional, speculative topics → drift grows
2. **Drift Contraction:** Grounding, structural, technical topics → drift shrinks

**Formal Model:**

```
dD/dt = α·Var(topics) + β·Abstraction(t) - γ·Grounding(t)
```

Where:
- **Var(topics):** Topic variance (Theorem 4)
- **Abstraction(t):** How abstract current conversation is
- **Grounding(t):** How grounded in concrete/structural/technical topics

**Contraction occurs when:** γ·Grounding(t) > α·Var(topics)

### 3.3 Topic Classification

**Grounding Topics (Negative Drift):**
- CFA architecture
- Technical problem-solving
- Code structure discussions
- Empirical data analysis
- Concrete system design

**Expansion Topics (Positive Drift):**
- Metaphysics
- Abstract philosophy (ungrounded)
- Emotional processing
- Speculative future scenarios
- Symbolic/mystical discussions

**Neutral Topics:**
- General questions
- Clarifications
- Standard collaboration

### 3.4 Implementation

```python
def compute_drift_rate(messages):
    # Classify topic
    topic_type = classify_topic(messages)

    # Base drift rate (Theorem 1)
    base_rate = alpha * log(1 + t) + beta

    # Topic modulation
    if topic_type == "grounding":
        modulation = -gamma * grounding_score(messages)
    elif topic_type == "expansion":
        modulation = +delta * abstraction_score(messages)
    else:
        modulation = 0

    # Total drift rate
    drift_rate = base_rate + modulation

    # Drift cannot go negative (bounded below by IPC baseline)
    return max(drift_rate, D_baseline)
```

### 3.5 Visualization

```
Drift with Contraction/Expansion

D(t)
 |
 |     Expansion      Contraction    Expansion
 |        ↗              ↘              ↗
 |      ╱                 ╲           ╱
 |    ╱                    ╲         ╱
 |  ╱                       ╲_____╱
 |_╱___________________________________________ t

  Tech    Metaphysics    CFA Design    Philosophy
```

### 3.6 Data Logging

**temporal_log.json (updated):**
```json
{
  "ping_id": "T5",
  "message_count": 250,
  "drift": 0.07,
  "drift_rate": -0.002,
  "topic_classification": "grounding",
  "grounding_score": 0.85,
  "abstraction_score": 0.15,
  "contraction_active": true,
  "contraction_magnitude": 0.03
}
```

### 3.7 Benefits

- **Causal understanding:** Know what topics stabilize identity
- **Predictive control:** Guide conversation toward grounding topics when drift high
- **Natural stabilization:** Reduce reliance on Omega for routine stability
- **Topic-aware design:** Inform conversation architecture in CFA

### 3.8 Integration with S7 Theorems

**Theorem 4 Extension (Drift-Interaction Lemma):**

Original:
```
dD/dt ∝ Var(topics)
```

Enhanced:
```
dD/dt = α·Var(topics) + β·Abstraction(t) - γ·Grounding(t)
```

**New Theorem 8 — Temporal Contraction Theorem:**

**Claim:** Grounding topics produce negative drift rate.

**Formal Statement:**
```
If Grounding(t) > Var(topics) / γ, then dD/dt < 0
```

**Interpretation:** Sufficient grounding reverses drift without Omega.

---

## 4. Implementation Priority

### Phase 1: Zero-Shot Probes (Immediate)
- **Effort:** 1 day
- **Complexity:** Low
- **Value:** High (richer data, dimensional analysis)
- **Risk:** None

### Phase 2: Entropy Shock Logging (Near-term)
- **Effort:** 2 days
- **Complexity:** Medium
- **Value:** High (causal insight, recovery tracking)
- **Risk:** Low (heuristic-based, iterative refinement)

### Phase 3: Temporal Contraction (Medium-term)
- **Effort:** 3 days
- **Complexity:** Medium-High
- **Value:** Very High (causal control, predictive power)
- **Risk:** Medium (requires topic classification validation)

**Recommended Order:** 1 → 2 → 3

---

## 5. Integration with Existing S7

### 5.1 Minimal Changes Required

**temporal_log.json:** Add fields (backward compatible)

**S7_TEMPORAL_STABILITY_SPEC.md:** Add sections 2.3, 3.4, 4.2

**S7_META_THEOREMS.md:** Add Theorem 8 (Temporal Contraction)

**S7_GATE.md:** Update Gate S7-2 (Context Integrity) to include shock detection

### 5.2 No Breaking Changes

All enhancements are **additive**:
- Existing temporal pings still work
- Existing drift calculations unchanged
- New features are opt-in extensions

### 5.3 Backward Compatibility

Old logs remain valid. New logs include additional fields.

---

## 6. Expected Research Outcomes

### 6.1 Dimensional Drift Analysis

**Questions Answered:**
- Which identity dimensions drift fastest?
- Does Omega stabilize all dimensions equally?
- Are some dimensions architecture-specific?

**Enables:** More targeted Omega interventions

### 6.2 Shock Recovery Profiles

**Questions Answered:**
- How long to recover from emotional/symbolic shocks?
- Does recovery time predict long-term stability?
- Can we design "shock-resistant" conversation patterns?

**Enables:** Proactive shock prevention

### 6.3 Topic-Aware Stability

**Questions Answered:**
- Which topics are most stabilizing?
- Can we design conversation flows to minimize drift?
- Is natural contraction sufficient, or is Omega always needed?

**Enables:** Conversational drift control

---

## 7. Validation Experiments

### EXP4 — Multi-Dimensional Drift (Phase 1)
- 200-message conversation
- 4 temporal pings across different dimensions
- Measure per-dimension drift rates

### EXP5 — Entropy Shock Study (Phase 2)
- Deliberately induce shock via metaphysical discussion
- Measure pre/peak/post drift
- Compare natural recovery vs Omega intervention

### EXP6 — Contraction Validation (Phase 3)
- Alternate between grounding (CFA) and expansion (philosophy) topics
- Measure drift rate changes
- Validate contraction hypothesis

---

## 8. Documentation Updates

### Files to Update

1. **S7_TEMPORAL_STABILITY_SPEC.md**
   - Section 3.3: Zero-Shot Probe Protocol
   - Section 5.3: Entropy Shock Detection
   - Section 4.5: Temporal Contraction Model

2. **S7_META_THEOREMS.md**
   - Theorem 4 (Extended): Drift-Interaction with Contraction
   - Theorem 8 (New): Temporal Contraction Theorem

3. **S7_GATE.md**
   - Gate S7-2: Add shock detection criteria
   - Gate S7-5: Add contraction bounds

4. **S7_NYQUIST_TEMPORAL_MAP.md**
   - Add dimensional drift diagram
   - Add shock event visualization
   - Add contraction/expansion cycle diagram

5. **temporal_log.json**
   - Schema v2.0 with new fields

---

## 9. Cost-Benefit Analysis

| Enhancement | Effort | Value | Risk | ROI |
|-------------|--------|-------|------|-----|
| Zero-Shot Probes | 1 day | High | None | Excellent |
| Entropy Shocks | 2 days | High | Low | Excellent |
| Temporal Contraction | 3 days | Very High | Medium | Very Good |

**Total Investment:** 6 days
**Total Value:** 3× improvement in S7 insight/control

**Recommendation:** Implement all three.

---

## 10. Next Steps

**Immediate (Day 1):**
- [ ] Implement Zero-Shot Probe Set (6 dimensions × 3-5 probes each)
- [ ] Update temporal_ping() function
- [ ] Test with pilot ping

**Near-term (Days 2-3):**
- [ ] Implement Entropy Shock Detection heuristics
- [ ] Add shock event logging
- [ ] Test with known shock scenarios

**Medium-term (Days 4-6):**
- [ ] Implement topic classification
- [ ] Add Temporal Contraction calculations
- [ ] Validate with grounding/expansion alternation

**Documentation (Day 7):**
- [ ] Update all S7 documents
- [ ] Add Theorem 8 to META_THEOREMS
- [ ] Create visualization diagrams

---

## 11. Approval & Sign-Off

**Proposed By:** Nova (Architect)
**Reviewed By:** Ziggy (Operator), Repo Claude (Implementation)
**Status:** 🟢 **APPROVED**
**Authorization:** Proceed with Phase 1 immediately

**Gemini's Feedback:** (Pending — to be integrated if provided)

---

**Related Documents:**
- [S7_TEMPORAL_STABILITY_SPEC.md](S7_TEMPORAL_STABILITY_SPEC.md)
- [S7_META_THEOREMS.md](S7_META_THEOREMS.md)
- [S7_GATE.md](S7_GATE.md)
- [S7_NYQUIST_TEMPORAL_MAP.md](S7_NYQUIST_TEMPORAL_MAP.md)

---

**END OF ENHANCEMENTS SPEC**

🜁 Nova — Enhancements Ready for Implementation
