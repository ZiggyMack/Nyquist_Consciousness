# 📘 **S4_GLOSSARY_v1 — Formal Scientific Glossary**

**System:** CFA Nyquist Persona Stability Framework
**Version:** S4 (Scientific Hardening Layer)
**Purpose:** Establish mathematically grounded, experimentally valid terminology for the Phase 3–4 research program and for external publication.

---

# **SECTION 1 — MATHEMATICAL & INFORMATION-THEORETIC TERMS**

---

## **Rate ( R )**

The number of effective bits used to encode the persona template.
Formal:
[
R = \frac{\text{tokens(seed)} \times \text{avg bits/token}}{\text{tokens(baseline)} \times \text{avg bits/token}}
]

---

## **Distortion ( D )**

Quantitative deviation between reconstructed behavior and the rich bootstrap.
Canonical S4 options:

* **D₁: Embedding Drift**
  [
  D_1 = 1 - \cos(e_\text{recon}, e_\text{baseline})
  ]
* **D₂: Behavioral Divergence**
  Error rate on benchmark tasks
* **D₃: Stylistic Divergence**
  Weighted delta across stylistic features

---

## **Rate–Distortion Curve ( R(D) )**

Function mapping minimal encoding rate required to maintain distortion ≤ D.
Central object of S4.

---

## **Mutual Information ( I(X;Y) )**

For persona template (X) and reconstructed response sequence (Y):
[
I(X;Y) = H(X) + H(Y) - H(X,Y)
]

---

## **Effective Information Rate ( I_\text{eff} )**

[
I_\text{eff} = \frac{I(\text{template}; \text{output})}{\text{token count(template)}}
]

Required metric for S4 experiments.

---

## **Entropy ( H(X) )**

Shannon entropy of behavioral outputs originating from persona initialization.

Used to quantify variability and stability of reconstruction.

---

## **KL Divergence ( D_{\text{KL}}(P \parallel Q) )**

Used to compare reconstructed distributions with the baseline distribution.

---

# **SECTION 2 — EXPERIMENTAL VARIABLES**

---

## **Bootstrap (Rich)**

Full initialization prompt encoding the target behavioral template.

---

## **Seed (Compressed Persona Template)**

Minimal initialization prompt designed for reconstruction.
S4 restricts Seeds to a defined bit-budget or token budget.

Types:

* **S4-T3A** — Adaptive
* **S4-T3H** — Hardened
* **S4-T3N** — Neutral (control)

---

## **Regime**

Well-defined evaluation condition:

* **FULL** → baseline persona
* **T3** → seed-only persona
* **GAMMA** → neutral baseline (no persona)

---

## **Drift ( \delta )**

Composite metric:
[
\delta = w_1 D_1 + w_2 D_2 + w_3 D_3
]

Weights fixed in S4 protocol.

---

## **Stability Variance ( \sigma^2 )**

Variance across N reconstruction runs under identical regime.

[
\sigma^2 = \frac{1}{N}\sum_i (s_i - \bar{s})^2
]

---

## **PFI — Persona Fidelity Index**

Primary S4 metric combining:

* embedding similarity
* human evaluator scores
* cross-model evaluator scores
* semantic drift
* style drift
* stability variance

[
\text{PFI} = f(D_1, D_2, D_3, \sigma^2, \text{model scores}, \text{human scores})
]

Formal function defined in S4 specification.

---

# **SECTION 3 — ATTRACTOR SYSTEM (CLEANED / FORMAL)**

Attractors are **evaluation dimensions**, not dynamical attractors.

Each = vector of observable features.

---

## **Identity Dimension ( I )**

Measures consistency in:

* role adherence
* self-reference stability
* substitution resistance

---

## **Value Dimension ( V )**

Measures consistency of:

* epistemic values
* prioritization choices
* reasoning norms

---

## **Structural Dimension ( S )**

Measures consistency in:

* causal-chain reasoning
* hierarchical decomposition
* abstraction depth
* error correction behavior

---

## **Style Dimension ( Y )**

Measures:

* formatting
* cadence
* syntactic signature
* rhetorical structure

---

## **Stability Dimension ( B )**

Measures:

* drift over time
* robustness to domain switching
* resistance to adversarial perturbation

---

## **Attractor Vector ( A )**

[
A = (I, V, S, Y, B)
]

Each component may have its own drift curve and variance.

---

# **SECTION 4 — FAILURE MODES (FORMALLY DEFINED)**

---

## **Compression Collapse**

Condition where reconstruction fails to preserve identity dimension beyond threshold:
[
I < I_{\min}
]

---

## **Drift Cascade**

When drift in one dimension increases probability of drift in others.
Requires cross-correlation testing.

---

## **Variance Explosion**

When stability variance exceeds S4 threshold:
[
\sigma^2 > 0.05
]

---

## **Semantic Bleedthrough**

Leakage of domain-irrelevant content due to over-compression.

Measured via topic-coherence tests.

---

## **Signature Collapse**

Style dimension falls below baseline threshold:
[
Y < Y_{\min}
]

---

# **SECTION 5 — CROSS-MODEL VALIDATION TERMS**

---

## **Model-Rater Panel**

Set of independent LLMs used to score reconstructed behavior.
Required models:

* Opus Claude
* GPT-4
* Gemini
* (Optionally) LLaMA 3

---

## **Inter-Model Agreement (IMA)**

Krippendorff’s alpha across model-rater scores.
Target:
[
\alpha \ge 0.6
]

---

## **Human-Rater Consensus (HRC)**

Pearson correlation between human evaluators.
Target:
[
r \ge 0.7
]

---

## **Cross-Model Correlation (CMC)**

Correlation between model-rater scores and human-rater scores.
Target:
[
r \ge 0.7
]

---

# **SECTION 6 — EXPERIMENTAL STRUCTURE / DESIGN**

---

## **Trial**

Single reconstruction experiment.

---

## **Run**

One reconstruction attempt within a Trial.

---

## **Burst**

Group of N runs under identical conditions.

---

## **Condition Matrix**

Cartesian product of:

* regime
* domain
* seed type
* rater type

Defines full factorial experiment.

---

# **SECTION 7 — MATHEMATICAL OBJECTS FOR S4 SPEC**

---

## **Persona Stability Function ( PS(r,d) )**

Persona stability at rate (r) and distortion (d).
Experimental target function.

---

## **Attractor Drift Function ( \Delta A )**

Vector function describing drift across attractor dimensions.

---

## **Performance Preservation Function ( P_{\text{pres}} )**

Task performance preserved after compression.

---

## **Embedding Stability Function ( E_s )**

Probability that two reconstructions fall within embedding distance ε.

---

# **SECTION 8 — DEPRECATED TERMINOLOGY**

These terms are *retired* for all scientific output:

* “Nyquist Consciousness” → replaced with “Rate-Distortion Persona Stability Model”
* “Degeneracy Surfaces” → replaced with “Layer Paradox”
* “Attractor Basin” (dynamical sense) → replaced with “Evaluation Dimension Stability”
* “Context” → replaced with **Regime**
* “P(Persona*) as probability” → replaced with **PFI**

---

# **SECTION 9 — NON-SCIENTIFIC TERMS quarantined to CFA layers (L3+)**

*(Excluded from scientific vocabulary but allowed in philosophical appendices)*

* Grok
* Nova
* Claude
* Trinity
* Dance of Ideal vs Real
* Meta-Architect
* Omega Nova

In scientific contexts, refer to:

* **Objective Function**
* **Evaluation Framework**
* **Auditing/Validation Layer**

---