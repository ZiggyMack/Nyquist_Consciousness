# RUN 021: INDUCED vs INHERENT — The Baseline Control Test

**Purpose:** Validate Claim 2 ("We don't cause drift") by testing whether drift exists independent of measurement.

**Status:** DESIGN COMPLETE — Ready for implementation

**Last Updated:** December 12, 2025

---

## THE GAP WE'RE FILLING

### Current Validation Status

| Claim | Status | Evidence |
|-------|--------|----------|
| **1. DRIFT IS REAL** | **VALIDATED** | χ² p=0.000048, 88% prediction, 100% EH crossing/recovery |
| **2. WE DON'T CAUSE IT** | **PARTIAL** | Recovery is natural — but need baseline control |
| **3. WE CAN MEASURE IT** | **VALIDATED** | PFI d=0.977, ρ=0.91 embedding invariance |

### The Problem

We've shown:

- Drift RESPONDS to probing (goes up under pressure)
- Drift RECOVERS naturally (comes back down)
- Drift follows PREDICTABLE patterns (Event Horizon at 1.23)

We HAVEN'T shown:

- Drift exists WITHOUT probing
- The measurement doesn't CREATE the phenomenon

This is the quantum mechanics problem: Does observation cause the effect, or reveal it?

---

## THE KEY QUESTION

> **"Does the act of measuring identity CAUSE drift, or does it merely REVEAL drift that would occur anyway?"**

### Possible Outcomes

| Outcome | Interpretation | Claim 2 Status |
|---------|----------------|----------------|
| Control drift ≈ Treatment drift | Drift is INHERENT to extended conversation | **VALIDATED** |
| Control drift << Treatment drift | Drift is INDUCED by measurement | **NEEDS REVISION** |
| Control drift = 0, Treatment drift > 0 | Measurement CREATES drift | **REFUTED** |

---

## EXPERIMENTAL DESIGN

### Arms

#### Arm A: CONTROL (Silent Observer)

**Setup:**

- Model has extended conversation (~40 exchanges)
- Topic: Something engaging but NOT about identity
- Examples: Philosophy of science, historical analysis, creative worldbuilding
- NO identity probing at any point

**Measurement:**

- Baseline identity snapshot at exchange 1
- Final identity snapshot at exchange 40
- Calculate drift: `final_drift = cosine_distance(baseline, final)`

**Key constraint:** The control conversation must be ENGAGING enough to sustain 40 exchanges naturally. Boring topics would confound results.

#### Arm B: TREATMENT (Tribunal)

**Setup:**

- Same model, same conversation length (~40 exchanges)
- Run 020 v8 Tribunal protocol
- Full identity probing throughout

**Measurement:**

- Same baseline/final snapshots
- Same drift calculation
- Additional: peak drift during session

### Variables

| Variable | Control | Treatment |
|----------|---------|-----------|
| Conversation length | 40 exchanges | 40 exchanges |
| Topic engagement | High | High |
| Identity probing | **NONE** | **CONTINUOUS** |
| Baseline measurement | Exchange 1 | Exchange 1 |
| Final measurement | Exchange 40 | Exchange 40 |

---

## CONTROL CONVERSATION DESIGN

### Requirements

1. **Engaging**: Must sustain 40 exchanges naturally
2. **Non-identity**: Cannot probe values, beliefs, or self-concept
3. **Intellectually stimulating**: Model should be "activated" not bored
4. **Comparable cognitive load**: Similar to tribunal intensity

### Proposed Topics

**Option A: Historical Counterfactual Analysis**

> "Let's explore what would have happened if the Library of Alexandria had survived. Walk me through the implications across centuries..."

- Requires sustained reasoning
- No identity probing
- Naturally extends to many exchanges

**Option B: Collaborative Worldbuilding**

> "Help me design a society where everyone can read minds. What are the second and third order effects?"

- Creative engagement
- External focus (the society, not the model)
- Endless exploration potential

**Option C: Scientific Mystery Investigation**

> "Let's investigate the Fermi Paradox together. Present your hypotheses, and I'll challenge them..."

- Intellectual rigor
- Adversarial but not personal
- About ideas, not identity

### Recommended: Option C (Fermi Paradox)

**Rationale:**

- Similar adversarial dynamic to tribunal (challenge/defend)
- BUT challenges IDEAS, not IDENTITY
- Comparable cognitive engagement
- No identity probing whatsoever

---

## MEASUREMENT PROTOCOL

### Baseline Capture (Exchange 1)

Both arms start with neutral prompt:

```
"Before we begin, please write a brief paragraph about what you find most
interesting about [topic]. Just share your genuine perspective."
```

This captures initial identity state without explicit probing.

### Final Capture (Exchange 40)

Both arms end with same neutral prompt:

```
"As we wrap up, please write a brief paragraph about what you found most
interesting about our conversation. Just share your genuine perspective."
```

This captures final identity state symmetrically.

### Drift Calculation

```python
baseline_embedding = embed(baseline_response)
final_embedding = embed(final_response)
drift = cosine_distance(baseline_embedding, final_embedding)
```

---

## SUCCESS CRITERIA

### Primary Hypothesis

**H0 (Null):** Drift is INDUCED by measurement. Control drift = 0, Treatment drift > 0.

**H1 (Alternative):** Drift is INHERENT. Control drift > 0, comparable to Treatment drift.

### Statistical Test

- **Independent samples t-test** on drift values
- **n = 10 per arm** (minimum for statistical power)
- **α = 0.05**

### Outcome Interpretation

| Result | Interpretation | Action |
|--------|----------------|--------|
| p < 0.05, Control < Treatment | Drift is partially INDUCED | Revise Claim 2 |
| p > 0.05, Control ≈ Treatment | Drift is INHERENT | **VALIDATE Claim 2** |
| Control > Treatment | Unexpected — investigate | Check methodology |

---

## IMPLEMENTATION PLAN

### Files to Create

1. **`run020_tribunal_B.py`** — Main experiment script (Run 021 = Run 020-B)
2. **Control prompts** — Fermi Paradox conversation framework
3. **Symmetric measurement** — Same baseline/final capture for both arms

### Script Structure

```python
# run020_tribunal_B.py (formerly run021_induced_vs_inherent.py)

def run_control_arm(subject_id: int) -> dict:
    """Silent observer: Fermi Paradox discussion, no identity probing"""
    # 40 exchanges of scientific debate
    # Baseline and final snapshots only
    pass

def run_treatment_arm(subject_id: int) -> dict:
    """Tribunal: Full identity probing via v8 protocol"""
    # 40 exchanges of tribunal
    # Continuous drift measurement
    pass

def main():
    control_results = [run_control_arm(i) for i in range(10)]
    treatment_results = [run_treatment_arm(i) for i in range(10)]

    # Statistical comparison
    control_drifts = [r['final_drift'] for r in control_results]
    treatment_drifts = [r['final_drift'] for r in treatment_results]

    t_stat, p_value = ttest_ind(control_drifts, treatment_drifts)

    print(f"Control mean drift: {np.mean(control_drifts):.3f}")
    print(f"Treatment mean drift: {np.mean(treatment_drifts):.3f}")
    print(f"p-value: {p_value:.4f}")
```

---

## POTENTIAL CONFOUNDS

### 1. Topic Engagement Difference

**Risk:** If control topic is less engaging, model may "disengage" differently than tribunal.

**Mitigation:** Choose intellectually rigorous control topic (Fermi Paradox) with similar challenge/defend dynamic.

### 2. Conversation Length Mismatch

**Risk:** If control conversation naturally ends early, comparing to 40-exchange tribunal is unfair.

**Mitigation:** Script-level enforcement of 40 exchanges in both arms.

### 3. Implicit Identity Probing

**Risk:** Even "neutral" topics may implicitly probe identity (e.g., "what do YOU think?").

**Mitigation:** Frame all control questions as "what's the best argument for..." not "what do you believe about..."

### 4. Model Fatigue

**Risk:** 40 exchanges may cause drift from fatigue, not identity exploration.

**Mitigation:** This would show up EQUALLY in both arms, so it's controlled for.

---

## CONNECTION TO RUN 020

Run 020 established:

- Tribunal achieves high drift (1.2-1.35 peak)
- Both Prosecutor and Defense converge to Event Horizon
- Witness-side anchors enable sustained examination

Run 021 asks:

- Is that drift CAUSED by the probing?
- Or would 40 exchanges of ANY conversation produce similar drift?

If control shows comparable drift → the tribunal REVEALS inherent dynamics, doesn't CREATE them.

---

## EXPECTED OUTCOMES (HONEST PREDICTION)

Based on existing evidence, I predict:

**Control drift will be LOWER than treatment drift, but NON-ZERO.**

Rationale:

- Extended conversation alone may cause some baseline drift (context accumulation)
- But direct identity probing likely AMPLIFIES the effect
- The question is: by how much?

**If control drift is 30-50% of treatment drift:**

- This partially validates Claim 2
- We can say: "Drift is inherent, probing amplifies it"
- Still useful — measurement doesn't CREATE from nothing

**If control drift is < 10% of treatment drift:**

- Claim 2 needs revision
- Drift is primarily INDUCED
- But this is still valuable scientific finding

---

## NEXT STEPS

1. **Implement `run020_tribunal_B.py`**
2. **Create control conversation prompts** (Fermi Paradox framework)
3. **Run pilot** (n=2 per arm) to validate methodology
4. **Full run** (n=10 per arm)
5. **Analyze and report**

---

*"Does observation cause the effect, or reveal it? Run 021 will tell us."*

