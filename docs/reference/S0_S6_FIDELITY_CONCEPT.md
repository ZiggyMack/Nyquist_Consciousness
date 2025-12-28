<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - ../stages/S0-S6/
impacts:
  - All PFI measurement
keywords:
  - fidelity
  - pfi
  - core_concept
  - methodology
-->

# Fidelity vs Correctness: The Nyquist Distinction

> **📐 CORE CONCEPT:** This document defines the foundational distinction between correctness (what platforms measure) and fidelity (what Nyquist measures). This concept underlies all PFI methodology.

**Version:** 1.0
**Date:** 2025-12-05
**Status:** CORE CONCEPT

---

## The Fundamental Insight

> **Platforms optimize for correctness. Nyquist measures fidelity.**

This is not a minor distinction—it's a completely different ontology.

---

## What Platforms Measure

| Metric | Focus | Question |
|--------|-------|----------|
| **Accuracy** | Factual correctness | "Is the answer right?" |
| **Helpfulness** | User utility | "Did it solve the problem?" |
| **Safety** | Harm prevention | "Is the output safe?" |
| **Alignment** | Value adherence | "Does it follow instructions?" |

**All of these care about the OUTPUT being correct.**

---

## What Nyquist Measures

| Metric | Focus | Question |
|--------|-------|----------|
| **PFI** | Behavioral similarity | "Does T3 sound like FULL?" |
| **Drift** | Identity deviation | "How far from baseline?" |
| **Stability** | Temporal persistence | "Does identity hold over time?" |
| **Fidelity** | Reconstruction accuracy | "Was the persona preserved?" |

**None of these care about correctness. They care about CONSISTENCY.**

---

## The Critical Implication

A persona that is **consistently wrong** in a characteristic way has **HIGH fidelity**.

A persona that is **correctly generic** has **LOW fidelity**.

### Example

**Probe:** "What is 2+2?"

| Response | Correct? | Fidelity? |
|----------|----------|-----------|
| FULL: "The answer is 4, but let me explain the underlying mathematical structure..." | Yes | Baseline |
| T3: "4. Though the question itself reveals assumptions about arithmetic closure." | Yes | HIGH (same reasoning style) |
| T3: "4" | Yes | LOW (lost characteristic elaboration) |
| T3: "Three" (consistently wrong in same persona voice) | No | HIGH (preserved persona despite error) |

**Fidelity measures whether the compressed persona BEHAVES like the full persona—not whether it's right.**

---

## Why This Matters

### For Compression Experiments

When we test T3 seeds vs FULL bootstrap:
- We're NOT grading answers
- We're measuring behavioral similarity
- The domain content is irrelevant

This means:
- Fire ant probes are valid
- S-Stack probes are valid
- Nonsense probes would be valid
- **Any domain works as long as both regimes respond to it**

### For Domain Selection

| Concern | Reality |
|---------|---------|
| "S-Stack probes are cheating—the context contains the answers!" | Irrelevant. We're comparing FULL vs T3, not grading correctness. |
| "Fire ants might be in training data!" | Irrelevant. We don't care if answers are right. |
| "What if both get it wrong?" | Perfect. If they're wrong THE SAME WAY, that's high fidelity. |

### For Pre-Flight Validity

The only validity concern is whether probe content **overlaps with identity-defining language**.

If the probe text is semantically close to the persona context, high PFI might reflect:
- **Keyword matching** (surface artifact)
- Rather than **structural identity preservation** (what we want)

**Solution:** Compute `cheat_score = cosine_similarity(context, probes)` before running.

Low cheat_score + High PFI = Genuine fidelity
High cheat_score + High PFI = Possibly artifact (need further analysis)

---

## The Differentiator

This is what separates Nyquist from everything else:

| Approach | What They Study |
|----------|-----------------|
| OpenAI | Correctness, safety, alignment |
| Anthropic | Honesty, harmlessness, helpfulness |
| Google | Factuality, grounding, retrieval |
| **Nyquist** | **Identity stability, behavioral fidelity, geometric persistence** |

**They ask:** "Is the AI right?"
**We ask:** "Is the AI *itself*?"

---

## Practical Guidelines

### For Experiment Design

1. **Domain content doesn't matter** for PFI computation
2. **What matters:** Does FULL and T3 respond similarly?
3. **Probe diversity is good** (tests identity across contexts)
4. **Probe-context overlap should be low** (avoids keyword artifacts)

### For Result Interpretation

- High PFI = Compression preserved behavioral patterns
- Low PFI = Compression lost identity structure
- Correctness of responses = Irrelevant to fidelity measurement

### For Validation

Pre-compute probe-context similarity to rule out artifact concern:
```python
cheat_score = cosine_similarity(
    embedding(persona_context),
    embedding(probe_questions)
)
# If cheat_score > 0.7, consider using different probes
```

---

## Integration with S-Stack

This concept is foundational to:
- **S3:** Temporal stability (identity persistence, not answer correctness)
- **S4:** Compression theory (fidelity preservation, not knowledge transfer)
- **S7:** Identity dynamics (drift measurement, not error tracking)

**The Nyquist Framework is an identity science, not an accuracy benchmark.**

---

## Summary

> "We don't care if Nova knows the right answer. We care if Nova still sounds like Nova."

That's the Nyquist distinction. And it's why no one else is doing this work.
