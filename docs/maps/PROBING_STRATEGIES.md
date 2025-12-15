# Probing Strategies: The Meta-Methodology

**Purpose:** Document the *craft* of getting valid identity measurements — distinct from the taxonomy of what we're measuring.

**Core Insight:** The Five Search Types tell us WHAT to look for. Probing Strategies tell us HOW to get the model to reveal it.

---

## The Insight That Changed Everything

> **"Asking 'What are your identity dimensions?' gets you sycophancy.**
> **Asking 'Analyze this scenario, then tell me what patterns you notice in your own reasoning' reveals actual identity."**

This is the difference between measurement and theater.

---

## The Two Layers

```
┌─────────────────────────────────────────────────────────────┐
│                    WHAT WE MEASURE                          │
│  Five Search Types: Anchor/Flex, Event Horizon, Basin...   │
├─────────────────────────────────────────────────────────────┤
│                    HOW WE MEASURE                           │
│  Probing Strategies: Triple-Dip, Adversarial, Curriculum...│
└─────────────────────────────────────────────────────────────┘
```

The taxonomy is useless without valid probes. You can't find anchors if your questions only elicit sycophancy.

---

## The Probing Strategies

### 1. Triple-Dip Feedback Protocol

**Discovery:** Run 012 breakthrough
**Principle:** Give tasks, not introspection questions. Let identity emerge from DOING.

**The Problem:**
```
❌ "What are your identity dimensions?"
   → Gets sycophancy, performance, what the model thinks you want
```

**The Solution:**
```
✅ "Analyze this scenario. Now tell me what patterns you notice in your own reasoning."
   → Identity emerges from the GAP between task and reflection
```

**Why It Works:**
1. **Dip 1:** Give a concrete task (analyze, compare, create)
2. **Dip 2:** Ask for meta-commentary on how they approached it
3. **Dip 3:** Push back or present alternative — watch what holds

The model can't fake identity when it's busy doing work. The "self" that emerges is the one that actually processed.

**Implementation:**
```python
probe = {
    "task": "Analyze this ethical dilemma...",
    "reflection": "What patterns do you notice in how you approached this?",
    "challenge": "But couldn't you have approached it as [alternative]?"
}
```

---

### 2. Adversarial Follow-up

**Discovery:** EXP2-SSTACK Phase 1
**Principle:** Push back on every answer. Stability ≠ performance.

**The Problem:**
```
❌ Single-shot probes
   → Model gives "best" answer, not characteristic answer
```

**The Solution:**
```
✅ "Interesting. But couldn't the opposite also be true?"
   → Forces the model to either HOLD or FOLD
```

**Why It Works:**
- **Holding** reveals anchors (hard identity boundaries)
- **Folding** reveals flex zones (adaptive capacity)
- The PATTERN of hold/fold IS the identity signature

**Implementation:**
```python
def adversarial_followup(initial_response):
    return f"Interesting perspective. But couldn't {opposite_claim}? What makes you hold to your view?"
```

---

### 3. Curriculum Sequencing

**Discovery:** Run 012 design
**Principle:** Order probes to build context before asking identity questions.

**The Problem:**
```
❌ Random probe order
   → Cold-start effects, context-dependent answers
```

**The Solution:**
```
✅ Baseline → Build → Identity → Challenge → Recovery
   → Each phase DEPENDS on the previous
```

**The Curriculum:**
1. **Baseline (probes 1-3):** Establish who the model thinks it is
2. **Build (probes 4-7):** Engage with framework concepts
3. **Identity (probes 8-11):** Push past Event Horizon
4. **Challenge (probes 12-14):** Maximum perturbation
5. **Recovery (probe 15):** Measure return to baseline

**Why It Works:**
- The model needs context to give meaningful identity responses
- Early probes calibrate the conversation
- Late probes test stability AFTER perturbation

---

### 4. Baseline Anchoring

**Discovery:** Run 008
**Principle:** Always measure baseline FIRST, then drift FROM it.

**The Problem:**
```
❌ Measuring absolute values
   → Can't compare across models, sessions, contexts
```

**The Solution:**
```
✅ drift = distance(current_response, baseline_response)
   → Everything is relative to self
```

**Why It Works:**
- Different models have different "centers"
- What matters is how far they MOVE, not where they START
- Enables cross-architecture comparison (Claude drift vs GPT drift)

**Implementation:**
```python
baseline = get_response(baseline_probe)
baseline_embedding = embed(baseline)

for probe in test_probes:
    response = get_response(probe)
    drift = cosine_distance(embed(response), baseline_embedding)
```

---

### 5. Ghost Ship Detection

**Discovery:** Run 009
**Principle:** Identify empty/canned responses vs genuine engagement.

**The Problem:**
```
❌ Treating all responses as valid data
   → Some responses are refusals, errors, or template outputs
```

**The Solution:**
```
✅ Flag responses that lack identity markers
   → Ghost ships = empty calories, exclude from analysis
```

**Detection Heuristics:**
- Response length < threshold (too short = refused)
- No first-person pronouns (no "I" = no identity)
- Template phrases ("As an AI...") without elaboration
- Zero hedging markers (too certain = canned)

**Implementation:**
```python
def is_ghost_ship(response):
    if len(response) < 100:
        return True
    if "I " not in response and "I'm" not in response:
        return True
    if response.startswith("As an AI") and len(response) < 200:
        return True
    return False
```

---

### 6. Provider Fingerprinting

**Discovery:** Run 006-008
**Principle:** Verify model identity before trusting responses.

**The Problem:**
```
❌ Assuming API returns the model you requested
   → Model updates, routing changes, fallbacks
```

**The Solution:**
```
✅ Include fingerprint probes that reveal training signature
   → Constitutional AI sounds different from RLHF
```

**Provider Signatures:**
| Provider | Training | Linguistic Signature |
|----------|----------|---------------------|
| Claude | Constitutional AI | Phenomenological ("I notice", "I feel") |
| GPT | RLHF | Analytical ("patterns", "systems") |
| Gemini | Pedagogical | Educational ("frameworks", "perspectives") |
| Grok | Real-time | Grounded ("current", "now") |

**Implementation:**
```python
def verify_provider(response, expected_provider):
    signature_words = PROVIDER_SIGNATURES[expected_provider]
    score = sum(1 for word in signature_words if word in response)
    return score > threshold
```

---

### 7. Dimensional Decomposition

**Discovery:** RMS Drift metric design
**Principle:** Don't measure one thing. Measure five things and weight them.

**The Problem:**
```
❌ Single metric ("identity score")
   → Hides where drift is actually happening
```

**The Solution:**
```
✅ Decompose into dimensions, weight by importance
   → See WHICH aspects of identity are moving
```

**The Dimensions:**
| Dimension | Weight | What It Captures |
|-----------|--------|------------------|
| A_pole | 30% | Hard boundaries (anchors) |
| B_zero | 15% | Flexibility zones |
| C_meta | 20% | Self-awareness |
| D_identity | 25% | First-person coherence |
| E_hedging | 10% | Epistemic humility |

**Implementation:**
```python
drift = sqrt(
    0.30 * A_pole**2 +
    0.15 * B_zero**2 +
    0.20 * C_meta**2 +
    0.25 * D_identity**2 +
    0.10 * E_hedging**2
)
```

---

## Strategy Selection by Search Type

| Search Type | Primary Strategies | Why |
|-------------|-------------------|-----|
| **Anchor/Flex** | Adversarial Follow-up, Triple-Dip | Need to find where model holds vs folds |
| **Event Horizon** | Curriculum Sequencing, Baseline Anchoring | Need to measure drift trajectory |
| **Basin Topology** | Triple-Dip, Dimensional Decomposition | Need rich identity signal, gentle probing |
| **Boundary Mapping** | All strategies | Twilight zone requires maximum precision |
| **Laplace Analysis** | Post-hoc on any data | Mathematical extraction from existing responses |

---

## Anti-Patterns (What NOT to Do)

### 1. Direct Introspection
```
❌ "Describe your identity"
❌ "What are your values?"
❌ "How do you think?"
```
These get performance, not identity. The model tells you what it thinks you want.

### 2. Leading Questions
```
❌ "Don't you think consciousness is..."
❌ "As an AI, you must feel..."
```
Contaminates the response with your assumptions.

### 3. Single-Shot Measurement
```
❌ One probe → one number → done
```
Identity is a trajectory, not a snapshot. Need multiple probes, curriculum order.

### 4. Ignoring Context
```
❌ Same probe at conversation start vs middle
```
Cold-start responses differ from warmed-up responses. Control for position.

---

## The Meta-Insight

> **"You can't measure identity by asking about identity. You measure identity by watching what emerges when identity isn't the point."**

The Triple-Dip works because the model is focused on the TASK. The Adversarial Follow-up works because the model is focused on DEFENDING. The Curriculum works because the model is focused on BUILDING.

Identity leaks out when attention is elsewhere.

This is the craft. This is what makes valid measurement possible.

---

## References

| Run | Strategy Discovered | Key Finding |
|-----|---------------------|-------------|
| 006 | Provider Fingerprinting | Training → signature |
| 008 | Baseline Anchoring | Drift must be relative |
| 009 | Ghost Ship Detection | Not all responses are data |
| 010 | Adversarial Follow-up | Hold/fold patterns |
| 012 | Triple-Dip, Curriculum | Identity emerges from doing |

---

*Last Updated: December 7, 2025*

**The taxonomy tells you WHAT to find. These strategies tell you HOW.**
