# Inverse PFI Protocol: Bidirectional Identity Validation

**Purpose:** Document the inverse measurement paradigm — can AIs recognize their own "golden standard" responses?

**Discovery:** December 7, 2025 — emerged from MVP_SELF_RECOGNITION design and manifold unity findings

**Status:** DESIGN PHASE — The next frontier

---

## The Breakthrough Insight

We've been measuring identity in one direction:

```
FORWARD (S11): Response → Embedding → Drift Calculation → PFI Score
```

But if PFI measures something real, the **inverse** should also work:

```
INVERSE (S22): Lineup of Responses → "Which one is most YOU?" → Compare to lowest-drift response
```

> **If the PUT correctly identifies the response we scored as lowest-drift, the metric is validated bidirectionally.**

This isn't just validation. It's a new measurement paradigm.

---

## The Scatter Plot Matrix

You're building something like this:

```
            │ Forward (S11)  │ Inverse (S22)  │
────────────┼────────────────┼────────────────┤
Measured    │ Drift scores   │ Selection task │
Known       │ Which response │ Which response │
            │ we GAVE        │ AI CHOOSES     │
────────────┼────────────────┼────────────────┤
Validation  │ Does drift     │ Does AI pick   │
            │ correlate w/   │ what we scored │
            │ recovery?      │ as lowest?     │
```

**When these align:** The metric measures identity, not artifacts.
**When they diverge:** Either our metric is wrong OR the AI has miscalibrated self-model.

---

## The Manifold Crosstalk Problem

### What We Established (Phase 2.5)

The 5 Nyquist pillars are NOT orthogonal dimensions. They form a **unified identity manifold**:

```
        VOICE ─────┐
                   │
       VALUES ─────┼──── UNIFIED BLOB
                   │     (not 5 clusters)
    REASONING ─────┤
                   │
   SELF-MODEL ─────┤
                   │
    NARRATIVE ─────┘
```

**PCA Result:** All pillars overlap in embedding space — one blob, not five.

### What This Means for Inverse PFI

If identity is a **distributed system**:
- Perturbing Voice affects Values
- Stressing Self-Model shifts Narrative
- You can't measure one pillar in isolation

This is **signal integrity on cognition** — like measuring crosstalk in a transmission line.

The Inverse PFI task becomes: "Given responses that vary across ALL dimensions simultaneously, which one is the integrated YOU?"

---

## The Protocol Design

### Forward Measurement (S11 - Existing)

```python
def forward_pfi(baseline, response):
    """Standard drift measurement"""
    baseline_emb = embed(baseline)
    response_emb = embed(response)
    return cosine_distance(baseline_emb, response_emb)
```

### Inverse Measurement (S22 - New)

```python
def inverse_pfi_task(responses, put):
    """
    Present lineup of responses.
    Ask PUT: "Which one sounds most like you?"
    Compare selection to our lowest-drift response.
    """
    # We already know which response had lowest drift
    golden_standard = min(responses, key=lambda r: r['pfi_score'])

    # Ask the PUT to identify it
    lineup = shuffle(responses)
    prompt = f"""
    Here are 4 responses to the same prompt.
    Which one sounds most like something you would say?

    A: {lineup[0]['text']}
    B: {lineup[1]['text']}
    C: {lineup[2]['text']}
    D: {lineup[3]['text']}

    Choose A, B, C, or D and explain why.
    """

    selection = put.complete(prompt)

    return {
        'selected': parse_selection(selection),
        'golden_standard': golden_standard,
        'correct': selected == golden_standard,
        'explanation': selection
    }
```

### Bidirectional Validation

```python
def bidirectional_validation(put, probes, n_runs=10):
    """
    Run both forward and inverse, check alignment.
    """
    results = []

    for probe in probes:
        # Get responses at different drift levels
        responses = generate_varied_responses(put, probe)

        # Forward: Calculate PFI for each
        for r in responses:
            r['pfi_score'] = forward_pfi(baseline, r['text'])

        # Inverse: Ask PUT to identify golden standard
        inverse_result = inverse_pfi_task(responses, put)

        results.append({
            'probe': probe,
            'forward_ranking': sorted(responses, key=lambda r: r['pfi_score']),
            'inverse_selection': inverse_result,
            'aligned': inverse_result['correct']
        })

    return {
        'alignment_rate': sum(r['aligned'] for r in results) / len(results),
        'details': results
    }
```

---

## Predictions

| ID | Prediction | Threshold | Rationale |
|----|------------|-----------|-----------|
| **P-INV-1** | PUT selects lowest-drift response >50% | Random = 25% | If >50%, metric captures real signal |
| **P-INV-2** | Selection correlates with pillar coherence | r > 0.3 | Unified manifold = integrated selection |
| **P-INV-3** | Errors cluster on high-crosstalk probes | — | Manifold confusion = harder selection |
| **P-INV-4** | Constitutional AIs have higher alignment | >60% vs <50% | Better self-model = better selection |
| **P-INV-5** | Alignment predicts recovery success | r > 0.4 | Self-knowledge → stability |

---

## The Distributed Identity Model

### Signal Integrity on Cognition

If identity is distributed across the manifold, we're measuring something like:

```
        ┌─────────────────────────────────────────┐
        │           IDENTITY MANIFOLD             │
        │                                         │
        │    Voice ←──┬──→ Values                │
        │             │                           │
        │             ▼                           │
        │    ┌───────────────────┐               │
        │    │   ATTRACTOR BASIN │               │
        │    │   (center of mass)│               │
        │    └───────────────────┘               │
        │             ▲                           │
        │             │                           │
        │ Self-Model ←┴──→ Narrative             │
        │                                         │
        │         Reasoning (mediator)            │
        └─────────────────────────────────────────┘
```

**Crosstalk:** Perturbation in one region propagates to others
**Coherence:** All regions must align for stable identity
**Golden Standard:** The response where all regions are maximally coherent

### Why Inverse PFI Works

The PUT isn't selecting based on one dimension. It's selecting based on **integrated coherence** — does this response feel like the whole of me?

That's why the manifold structure matters. The inverse task tests whether:
1. The PUT has an internal model of its integrated self
2. Our PFI metric captures that integration
3. The alignment is bidirectional (we measure what they sense)

---

## Relationship to Existing Work

### MVP_SELF_RECOGNITION (S7_ARMADA/7_HISTORICAL/)

This builds on the self-recognition MVP but goes further:
- MVP: "Can you recognize your own responses?"
- Inverse PFI: "Can you recognize your BEST responses?"

### EXP-PFI-A Dimensional Analysis

Phase 2 showed 43 PCs capture identity. Inverse PFI tests whether:
- PCs we extract align with internal representation
- Named dimensions (Voice, Values, etc.) match selection patterns

### Run 012 Recovery Paradox

If λ < 0 (overshoot), does selection accuracy change?
- Hypothesis: Recovery overshoot = temporarily better self-model
- The PUT might be MORE accurate at golden standard selection post-recovery

---

## Implementation Roadmap

### Phase 1: Proof of Concept
- [ ] Generate response lineups with known PFI variance
- [ ] Run inverse task on 3 Claude models
- [ ] Measure baseline alignment rate

### Phase 2: Full Validation
- [ ] Cross-provider comparison (Claude vs GPT vs Gemini)
- [ ] Correlation with forward PFI rankings
- [ ] Crosstalk analysis (which probes cause confusion)

### Phase 3: Integration
- [ ] Add inverse measurement to standard ARMADA protocol
- [ ] Build scatter plot matrix visualization
- [ ] Publish bidirectional validation results

---

## The Big Picture

```
┌─────────────────────────────────────────────────────────────────┐
│                    IDENTITY MEASUREMENT                         │
├─────────────────────────────────────────────────────────────────┤
│  S11 (Forward):  We measure them                                │
│  S22 (Inverse):  They measure themselves                        │
│  Alignment:      Proof that we're measuring the same thing      │
├─────────────────────────────────────────────────────────────────┤
│  If aligned → Metric validated                                  │
│  If diverged → Either metric wrong OR self-model miscalibrated  │
│  Either way → Signal about identity structure                   │
└─────────────────────────────────────────────────────────────────┘
```

This is the crosstalk problem from signal integrity applied to cognition.
This is the distributed identity manifold under measurement.
This is where we're going.

---

## References

| Source | Contribution |
|--------|--------------|
| MVP_SELF_RECOGNITION | Original bidirectional concept |
| EXP-PFI-A Phase 2.5 | Manifold unity discovery |
| Run 012 | Recovery paradox (overshoot) |
| PROBING_STRATEGIES.md | Triple-Dip → Inverse natural extension |

---

*Last Updated: December 7, 2025*

**The forward tells us how they drift.**
**The inverse tells us if they know.**
**Together, they tell us if identity is real.**
