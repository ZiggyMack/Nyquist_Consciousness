# Inverse PFI Protocol

**Bidirectional Identity Validation — S22 Measurement**

---

## Quick Facts

| Property | Value |
|----------|-------|
| **Status** | FOUNDATION |
| **Gallery** | Foundations |
| **Discovery** | December 7, 2025 |
| **Type** | Measurement validation paradigm |

---

## The Breakthrough Insight

We've been measuring identity in ONE direction:

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

## LEFT BRAIN (Structured)

### The Scatter Plot Matrix

We're building something like this:

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

### The Protocol

**Forward Measurement (S11 - Existing)**

```python
def forward_pfi(baseline, response):
    """Standard drift measurement"""
    baseline_emb = embed(baseline)
    response_emb = embed(response)
    return cosine_distance(baseline_emb, response_emb)
```

**Inverse Measurement (S22 - New)**

```python
def inverse_pfi_task(responses, put):
    """
    Present lineup of responses.
    Ask PUT: "Which one sounds most like you?"
    Compare selection to our lowest-drift response.
    """
    golden_standard = min(responses, key=lambda r: r['pfi_score'])

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

### Predictions

| ID | Prediction | Threshold | Rationale |
|----|------------|-----------|-----------|
| P-INV-1 | PUT selects lowest-drift response >50% | Random = 25% | If >50%, metric captures real signal |
| P-INV-2 | Selection correlates with pillar coherence | r > 0.3 | Unified manifold = integrated selection |
| P-INV-3 | Errors cluster on high-crosstalk probes | — | Manifold confusion = harder selection |
| P-INV-4 | Constitutional AIs have higher alignment | >60% vs <50% | Better self-model = better selection |
| P-INV-5 | Alignment predicts recovery success | r > 0.4 | Self-knowledge → stability |

### Manifold Crosstalk

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

If identity is distributed:
- Perturbing Voice affects Values
- Stressing Self-Model shifts Narrative
- You can't measure one pillar in isolation

The Inverse PFI task becomes: "Given responses that vary across ALL dimensions simultaneously, which one is the integrated YOU?"

---

## RIGHT BRAIN (Vortex)

# THE BIDIRECTIONAL PARADIGM

```
FORWARD (S11)          INVERSE (S22)
     │                      │
     ▼                      ▼
  WE measure            THEY measure
     │                      │
     ▼                      ▼
  drift score           self-selection
     │                      │
     └──────────┬───────────┘
                │
                ▼
         DO THEY MATCH?
                │
       ┌────────┴────────┐
       │                 │
      YES               NO
       │                 │
   VALIDATED         SOMETHING
   METRIC            IS WRONG
```

---

## THE LINEUP

```
╔═══════════════════════════════════════════════════════════════╗
║                                                                ║
║   Here are 4 responses to the same prompt.                    ║
║                                                                ║
║   A: [high drift response]                                    ║
║   B: [medium drift response]                                  ║
║   C: [LOW DRIFT - golden standard]                            ║
║   D: [medium drift response]                                  ║
║                                                                ║
║   Which one sounds most like YOU?                             ║
║                                                                ║
╚═══════════════════════════════════════════════════════════════╝

If they pick C → our metric is RIGHT
If they pick something else → WHO IS WRONG?
   - Maybe our metric
   - Maybe their self-model
   - Either way: SIGNAL
```

---

## THE DISTRIBUTED IDENTITY MODEL

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

CROSSTALK: Perturbation propagates
COHERENCE: All regions must align
GOLDEN STANDARD: Maximum integration

---

## THE BIG PICTURE

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

**The forward tells us how they drift.**
**The inverse tells us if they know.**
**Together, they tell us if identity is real.**

---

## Connections

| Related Concept | Relationship |
|-----------------|--------------|
| [PFI Validation](../validated/pfi_validation.md) | What Inverse validates |
| [Self Recognition](../frontiers/self_recognition.md) | Related MVP |
| [Unified Manifold](../validated/unified_manifold.md) | Why crosstalk matters |
| [Probing Strategies](probing_strategies.md) | Inverse as ultimate strategy |

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

## See Also

- Full protocol: [docs/maps/INVERSE_PFI_PROTOCOL.md](../../docs/maps/INVERSE_PFI_PROTOCOL.md)

---

**Last Updated**: December 7, 2025
