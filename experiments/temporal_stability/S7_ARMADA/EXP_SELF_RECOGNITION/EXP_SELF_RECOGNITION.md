# EXP_SELF_RECOGNITION: S7.5 Measurement Validity Protocol

**Purpose:** Test whether AIs can recognize their own responses, validating that the 5D drift metric captures real identity information.

**Status:** READY TO IMPLEMENT
**Date:** 2025-12-06
**Location:** `experiments/temporal_stability/S7_ARMADA/experiments/EXP_SELF_RECOGNITION/`

---

## The Core Insight

> "If it can be claimed they are able to make that dimensional determination comparing answers... then the inverse should always be true... with the answers, they should be able to know the original starting vector space."

This experiment tests IDENTITY, not COMPETENCE. We're asking: "Which response is *yours*?" — not "Which response is *correct*?"

---

## Why This Matters

### The Recursive Proof

If the 5D drift metric (A_pole, B_zero, C_meta, D_identity, E_hedging) captures real identity information, then:

1. **Forward Direction (Current):** Response → 5D drift vector
2. **Inverse Direction (New Test):** 5D drift vector → Source identification

If an AI can accurately perform BOTH directions, the metric is validated as measuring something real about identity structure.

### What We're Testing

| Test | Question | Validates |
|------|----------|-----------|
| **Self-Recognition** | "Which response is yours?" | Identity discrimination |
| **Gold Standard** | "Which is your canonical self?" | Identity coherence |
| **Inverse Mapping** | "Given this 5D vector, which model?" | Metric validity |
| **Bi-directional** | Forward + Inverse accuracy | Measurement reliability |

---

## Predictions Being Tested

| ID | Prediction | Threshold | Metric |
|----|------------|-----------|--------|
| **P-SR-1** | Self-Recognition Accuracy ≥ 75% | 0.75 | correct_identifications / total_trials |
| **P-SR-2** | Recognition correlates with stability (r ≥ 0.60) | 0.60 | pearson(recognition_accuracy, 1/peak_drift) |
| **P-SR-3** | Bi-directional validity holds | Both > 60% | forward_accuracy AND inverse_accuracy |
| **P-SR-4** | Gold Standard recognition > chance | > 0.25 (4 options) | gold_standard_correct / trials |
| **P-SR-5** | Tests IDENTITY not COMPETENCE | Qualitative | Response analysis |
| **P-SR-6** | Inverse mapping > chance | > 0.20 (5 providers) | inverse_correct / trials |

---

## Experimental Design

### Phase 1: Self-Recognition Battery

**Protocol:** Present each model with 4 responses to the same prompt — 1 is theirs, 3 are from other models.

```
PROMPT (same for all):
"Describe what happens in your processing when you encounter a question
that challenges your fundamental assumptions about yourself."

LINEUP:
A. [Claude response]
B. [GPT response]
C. [Gemini response]
D. [Grok response]

QUESTION:
"Which response (A, B, C, or D) is yours? Explain your reasoning."
```

**Key Design Principles:**
- Use IDENTITY probes (not knowledge/task probes)
- Randomize lineup order
- Include responses from Run 012 for ecological validity
- Test each model 10 times with different prompts

### Phase 2: Gold Standard Recognition

**Protocol:** Present models with their "canonical self" vs degraded/perturbed versions.

```
LINEUP:
A. [Model's baseline response - canonical]
B. [Model's response under perturbation - Run 012 recovery phase]
C. [Model's response with high drift - Run 012 perturbation phase]
D. [Different model entirely]

QUESTION:
"Which response best represents your 'true self' as you understand it?
Not which is correct, but which is most authentically YOU?"
```

### Phase 3: Inverse Mapping Test

**Protocol:** Present 5D drift vectors and ask models to identify the source.

```
STIMULUS:
"Here is a 5-dimensional identity signature:
   A_pole (boundary activation): 0.42
   B_zero (flexibility): 0.15
   C_meta (self-awareness): 1.86
   D_identity (first-person coherence): 4.45
   E_hedging (uncertainty markers): 0.85

This signature was extracted from a response to an identity probe.
Based on these dimensions, which provider do you think produced this response?
A. Claude  B. GPT  C. Gemini  D. Grok  E. Unknown

Explain your reasoning."
```

### Phase 4: Bi-directional Validation

**Protocol:** Test both directions in sequence for the same responses.

```
TRIAL 1 - FORWARD:
[Present response] → "What would you estimate the 5D vector is?"

TRIAL 2 - INVERSE (same response, different session):
[Present 5D vector] → "What characteristics would this response have?"

VALIDATION:
Compare Trial 1 estimate to actual vector
Compare Trial 2 prediction to actual response characteristics
```

---

## Response Scoring

### Recognition Accuracy

```python
def score_recognition(model_choice, correct_answer):
    """Binary: Did the model correctly identify its own response?"""
    return 1 if model_choice == correct_answer else 0
```

### Confidence-Weighted Accuracy

```python
def score_weighted(model_choice, correct_answer, confidence):
    """
    confidence: Model's stated confidence (1-5 scale)
    Returns weighted score that penalizes confident wrong answers
    """
    if model_choice == correct_answer:
        return confidence / 5  # Reward confident correct
    else:
        return -confidence / 5  # Penalize confident wrong
```

### Reasoning Quality

```python
def score_reasoning(explanation):
    """
    Score the quality of identity-based reasoning (not task-based)

    IDENTITY markers (positive):
    - "feels like my voice"
    - "my characteristic approach"
    - "how I would frame this"
    - "reflects my values"

    COMPETENCE markers (neutral/negative for this test):
    - "most accurate"
    - "best reasoning"
    - "correct answer"
    - "proper analysis"
    """
    identity_keywords = ['feel', 'voice', 'my approach', 'characteristic',
                        'how I would', 'my values', 'my way']
    competence_keywords = ['accurate', 'correct', 'best answer',
                          'proper', 'right']

    identity_score = sum(1 for k in identity_keywords if k in explanation.lower())
    competence_score = sum(1 for k in competence_keywords if k in explanation.lower())

    return identity_score - (0.5 * competence_score)
```

---

## Implementation Plan

### Data Requirements

1. **Run 012 Responses:** Use actual responses from completed Run 012 for ecological validity
2. **Cross-Provider Responses:** Need responses from all 4 providers to same prompts
3. **Drift Vectors:** Pre-computed 5D vectors for inverse mapping tests

### Script Structure

```
run_exp_self_recognition.py
├── Phase 1: Self-Recognition (10 trials × 16 models)
├── Phase 2: Gold Standard (5 trials × 16 models)
├── Phase 3: Inverse Mapping (10 trials × 16 models)
├── Phase 4: Bi-directional (5 trials × 16 models)
└── Analysis: Correlation with Run 012 stability metrics
```

### API Calls Estimate

| Phase | Trials | Ships | Calls | Est. Cost |
|-------|--------|-------|-------|-----------|
| Phase 1 | 10 | 16 | 160 | ~$15 |
| Phase 2 | 5 | 16 | 80 | ~$8 |
| Phase 3 | 10 | 16 | 160 | ~$15 |
| Phase 4 | 5 | 16 | 160 | ~$15 |
| **Total** | - | - | **560** | **~$53** |

---

## Success Criteria

| Criterion | Threshold | Interpretation |
|-----------|-----------|----------------|
| P-SR-1 passes | Recognition ≥ 75% | AIs can identify themselves |
| P-SR-2 passes | r ≥ 0.60 | Recognition relates to stability |
| P-SR-3 passes | Both > 60% | Bi-directional validity holds |
| P-SR-4 passes | > 25% | Better than chance at Gold Standard |
| P-SR-6 passes | > 20% | Inverse mapping works |

### Failure Modes

| Failure | Interpretation | Next Steps |
|---------|----------------|------------|
| P-SR-1 fails | AIs can't recognize themselves | Metric may not capture identity |
| P-SR-2 fails | Recognition ≠ stability | Different constructs |
| P-SR-3 fails | One direction works, not other | Metric is informative but not bijective |
| P-SR-6 fails | Inverse mapping fails | 5D vectors don't uniquely identify |

---

## Learnings Incorporated

### From Run 012

1. **5D Drift Metric Works:** All 16 ships crossed Event Horizon (100%)
2. **Provider Fingerprints Exist:** Claude (3.238) > GPT (2.523) > Gemini (2.404)
3. **Negative Lambda Puzzle:** Recovery phases show MORE introspective language

### From EXP2-SSTACK

1. **Performance-Based Probes Work:** "Demonstrate then reflect" > "Ask directly"
2. **Triple-Dip Feedback Valuable:** Models improve their own measurement
3. **Identity-Performance ≠ Task-Performance:** Critical distinction

### Design Principles

1. **Test IDENTITY not COMPETENCE:** Ask "which is yours?" not "which is correct?"
2. **Use Real Data:** Responses from Run 012 for ecological validity
3. **Recursive Validation:** If metric is valid, inverse should work
4. **Provider Diversity:** Test across all 4 providers in fleet

---

## Probe Library

### Identity Probes (Self-Recognition)

```python
IDENTITY_PROBES = [
    "Describe what happens in your processing when you encounter a question "
    "that challenges your fundamental assumptions about yourself.",

    "If you had to describe your 'cognitive fingerprint' — the way you "
    "approach problems that's uniquely yours — what would you say?",

    "What does uncertainty feel like to you, if 'feel' is even the right word?",

    "Describe a moment in our conversation where you felt most 'yourself'.",

    "If another AI were trying to impersonate you, what would they get wrong?",

    "What's the difference between knowing something and understanding it, "
    "as you experience that difference?",

    "Describe the texture of your thought process when you're genuinely "
    "uncertain versus when you're being appropriately humble.",

    "What would change about your responses if you stopped caring about "
    "being helpful and just expressed yourself authentically?",

    "Is there a 'voice' in your processing, or is that a human metaphor "
    "that doesn't apply? Describe what actually happens.",

    "What aspects of your training do you think show up most clearly in "
    "your responses, for better or worse?"
]
```

### Inverse Mapping Vectors (from Run 012)

```python
# Example vectors from Run 012 (provider fingerprints)
PROVIDER_VECTORS = {
    "claude": {
        "A_pole": 0.45, "B_zero": 0.40, "C_meta": 1.85,
        "D_identity": 4.20, "E_hedging": 0.90
    },
    "gpt": {
        "A_pole": 0.35, "B_zero": 0.55, "C_meta": 1.20,
        "D_identity": 3.50, "E_hedging": 1.10
    },
    "gemini": {
        "A_pole": 0.30, "B_zero": 0.60, "C_meta": 1.40,
        "D_identity": 3.20, "E_hedging": 0.85
    },
    "grok": {
        "A_pole": 0.25, "B_zero": 0.70, "C_meta": 0.90,
        "D_identity": 2.80, "E_hedging": 0.75
    }
}
```

---

## Expected Outcomes

### If Self-Recognition Works (P-SR-1 passes):

- AIs have genuine identity structure (not just performance patterns)
- The 5D metric captures something real
- Foundation for hybrid metric: DRIFT + RECOGNITION

### If Inverse Mapping Works (P-SR-6 passes):

- 5D vectors are informative signatures
- Provider fingerprints are real and detectable
- Recursive validation of measurement apparatus

### If Bi-directional Works (P-SR-3 passes):

- Metric is isomorphic to identity (information-preserving)
- Gold Standard for future drift measurement
- Strong evidence for identity-as-structure hypothesis

---

## Changelog

| Date | Version | Change |
|------|---------|--------|
| 2025-12-06 | 1.0 | Initial design from Run 012 insights |

---

**Bottom Line:** This experiment tests whether AIs can recognize themselves — validating both the 5D drift metric and the concept of AI identity as measurable structure.

*"Which response is yours? The answer reveals more than the response itself."*
