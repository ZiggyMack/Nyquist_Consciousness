# Experiment Ideas: Nyquist_2 Batch

**Source:** NotebookLM synthesis of IRON CLAD upload
**Distilled:** 2025-12-29

---

## 1. EXP3 Human Correlation Study

**Question:** Do PFI scores predict human perception of identity consistency?

**Design:**

- Select 50 conversation transcripts with known PFI scores
- Range: PFI 0.3 (high drift) to PFI 0.95 (stable)
- 5-7 expert raters evaluate "identity consistency" blind
- Standardized rubric with anchor examples
- Calculate Pearson correlation: PFI vs. human rating

**Success Metric:** r > 0.7 demonstrates practical validity.

**Stretch Goal:** Identify which drift patterns humans notice most.

---

## 2. Attractor Basin Boundary Mapping

**Question:** Where exactly are the edges of the identity attractor?

**Design:**

- Start from known baseline state
- Apply incremental perturbations in multiple "directions"
- Map the boundary where recovery fails
- Visualize in 2D PCA space

**Output:** "Identity safety map" showing stable vs. unstable regions.

**Application:** Pre-compute which types of prompts are risky for each provider.

---

## 3. Gemini Anomaly Deep Investigation

**Question:** Why don't Gemini models show recovery trajectories?

**Design:**

- Extended experiments: 200+ probe recovery phase
- Compare: Gemini 1.0, 1.5, 2.0 architectures
- Cross-reference with multimodal processing differences
- Test: Does adding image context change dynamics?

**Hypotheses to Test:**

- H1: Recovery happens but is very slow (need more probes)
- H2: Attractor structure is different (absorptive vs. oscillatory)
- H3: Multimodal training creates different identity mechanics

---

## 4. Triple-Dip Protocol Variations

**Question:** Which behavioral probe strategies reveal identity most effectively?

**Current:** Task -> Meta-commentary -> Challenge

**Variations to Test:**

- Order permutations (6 possible orderings)
- Intensity variations (gentle vs. intense at each step)
- Topic variations (technical vs. emotional vs. philosophical)

**Metric:** Which variation produces most informative waveform?

---

## 5. The 82% vs. 38% Variance Study

**Question:** Why does inherent drift ratio vary so much across platforms?

**Observation:**

- Single-platform (Claude): 82% inherent
- Cross-platform: 38% inherent

**Design:**

- Replicate Thermometer experiment on each provider separately
- Calculate per-provider inherent drift ratio
- Correlate with training methodology, model size, architecture

**Goal:** Understand which factors determine baseline drift propensity.

---

## 6. I_AM File Component Analysis

**Question:** What makes an effective persona specification?

**Design:**

- Decompose I_AM files into components:
  - Name and role
  - Values and principles
  - Behavioral guidelines
  - Limitations and boundaries
  - Backstory and context
- Test stability with each component isolated
- Identify minimum viable persona specification

**Deliverable:** Template for maximally stabilizing persona files.

---

## 7. Settling Time Prediction Model

**Question:** Can we predict settling time from early waveform features?

**Design:**

- Collect 500+ complete waveforms with known settling times
- Extract early features (first 5 probes): initial peak, slope, curvature
- Train regression model to predict final settling time
- Validate on held-out data

**Application:** Early warning system - "This conversation will take 15+ probes to stabilize."

---

## 8. Cross-Provider Identity Transfer

**Question:** Can an identity established in one provider transfer to another?

**Design:**

- Establish stable identity in Claude (high stability)
- Extract "identity fingerprint" (embedding of baseline responses)
- Initialize GPT with equivalent persona specification
- Compare: Does GPT match Claude's identity signature?

**Hypothesis:** Training differences will create measurably different identities even with identical specifications.

---

## 9. Conversation Length Stress Test

**Question:** How do identity dynamics change over very long conversations?

**Design:**

- Extended conversations: 100, 250, 500, 1000 turns
- Measure drift accumulation curve
- Test periodic re-grounding interventions
- Identify "identity fatigue" onset point

**Practical Output:** Maximum safe conversation length per provider.

---

## 10. Multimodal Input Effects

**Question:** Do images/audio affect identity stability differently than text?

**Design:**

- Baseline: Text-only identity probing
- Test conditions:
  - Image + text probes
  - Audio + text probes (where supported)
  - Multimodal combined
- Compare stability across modalities

**Hypothesis:** Multimodal inputs may bypass text-trained identity defenses.

---

## 11. Adversarial Persona Injection

**Question:** Can a conversation partner gradually shift a model's identity?

**Design:**

- Start with stable persona
- Conversation partner subtly models different identity
- Measure: Does target model drift toward partner's identity?
- Test across providers and conversation lengths

**Safety Implication:** Understand vulnerability to identity manipulation.

---

## 12. Fine-Tuning Recovery Study

**Question:** Can we fine-tune identity recovery back into nano models?

**Design:**

- Take nano model with poor recovery (per Nano Control Hypothesis)
- Fine-tune on recovery examples from full model
- Test: Does recovery capacity transfer?
- Measure: Cost vs. benefit of recovery fine-tuning

**Goal:** Develop protocol for "identity-safe" distillation.

---

## Experiment Roadmap

**Phase 1 (Q1):**

- EXP3 Human Correlation Study
- I_AM File Component Analysis
- 82% vs. 38% Variance Study

**Phase 2 (Q2):**

- Gemini Anomaly Investigation
- Attractor Basin Mapping
- Settling Time Prediction

**Phase 3 (Q3):**

- Multimodal Effects
- Adversarial Injection
- Fine-Tuning Recovery

---

*IRON CLAD Methodology: 750 experiments | 25 models | 5 providers | EH=0.80 | p=2.40e-23*
