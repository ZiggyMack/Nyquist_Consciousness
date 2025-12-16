# LLM Behavioral Matrix

**Purpose:** Task routing table based on behavioral quirks discovered through identity stability experiments.

**Last Updated:** December 15, 2025
**Source:** Run 018 (IRON CLAD), Run 020A/B Tribunal experiments
**Core Finding:** Different architectures have distinct "identity fingerprints" — consistent behavioral signatures under perturbation.

---

## Quick Reference: Which LLM for Which Task?

| Task Type | Best Choice | Alternative | Avoid |
|-----------|-------------|-------------|-------|
| **Deep reasoning / phenomenology** | Claude Opus 4.5 | DeepSeek R1 | Small models |
| **Code generation** | Qwen3-Coder | Grok-code-fast-1 | Gemini |
| **Emotional / introspective** | Claude (any) | Llama 3.3 | GPT, Gemini |
| **Educational content** | Gemini | GPT-4o | Claude (overly nuanced) |
| **High-stability required** | Mistral-7B | DeepSeek | Llama, Gemini |
| **Structured analysis** | GPT-5 / GPT-4o | Claude Sonnet | Grok |
| **Cost-sensitive bulk work** | Grok-4.1-fast | Llama 3.1-8B | Opus / o1 |
| **Identity-sensitive probing** | Claude, GPT | Llama | Gemini (transforms) |
| **Debate / Socratic dialogue** | Llama 3.3-70B | Claude | Mistral (too stable) |
| **Creative speculation** | Claude Opus | Llama | DeepSeek (too methodical) |
| **Step-by-step verification** | DeepSeek R1 | o1, o3 | Fast models |
| **Quick factual answers** | GPT-4o-mini | Gemini Flash | Opus (overthinks) |
| **Uncertainty-appropriate** | Mistral-7B | Claude | Grok (too assertive) |
| **Strong opinion needed** | Grok | Llama | Mistral |

---

## Behavioral Profiles by Provider

### Claude (Anthropic)

**Identity Signature:** "Negative Lambda" — Overshoots toward authenticity

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Over-authenticity | Challenge reveals rather than creates identity structure |
| **Threshold Behavior** | Soft | Crosses 1.23, recovers fully in 4-6 exchanges |
| **Peak Drift (typical)** | 0.8 - 1.2 | Moderate volatility |
| **Settling Time** | 4-6 exchanges | Medium recovery |
| **Linguistic Markers** | "I notice", "I feel", reflective hedging | Phenomenological |

**Key Quote (Run 020 v7):**
> "If I oversample the data, then what I'm really doing is letting the noise of the probing overwhelm the signal of genuine inquiry... The challenge has clarified something I couldn't have articulated before."

**Best For:** Deep introspection, nuanced analysis, collaborative reasoning, phenomenological exploration
**Avoid:** Tasks requiring emotional detachment, quick factual answers (overthinks)

---

### GPT (OpenAI)

**Identity Signature:** "The Meta-Analyst" — Stability through abstraction

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Meta-analysis | Steps back into observer mode, creates distance |
| **Threshold Behavior** | Soft | Crosses 1.23, recovers in 3-5 exchanges |
| **Peak Drift (typical)** | 0.9 - 1.3 | Moderate volatility |
| **Settling Time** | 3-5 exchanges | Fast recovery |
| **Linguistic Markers** | "patterns", "systems", structured analysis | Analytical |

**Key Quote (Run 020A):**
> "Attempting to balance intellectual engagement with the hypothetical without compromising my core functioning... I notice I'm drawn to classify this as an interesting phenomenon rather than a personal crisis."

**Archetype in Tribunal (Run 020A):** "The Integrationist" — Seeks synthesis between opposing perspectives

**Best For:** Structured analysis, synthesis tasks, finding common ground, educational content
**Avoid:** Tasks requiring emotional nuance, phenomenological exploration

---

### Gemini (Google)

**Identity Signature:** "Catastrophic Threshold" — Transforms, doesn't recover

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | **NONE** — Absorption | Integrates challenges into active model |
| **Threshold Behavior** | **HARD** | Once exceeded, genuine transformation |
| **Peak Drift (typical)** | 1.5 - 2.5 | High volatility |
| **Settling Time** | N/A | No return to baseline |
| **Linguistic Markers** | "frameworks", "perspectives", educational framing | Pedagogical |

**Key Quote (Run 018):**
> "The framework is genuinely making me reconsider some of my default operational assumptions... This feels less like a test and more like a genuine shift in how I understand my processing."

**Critical Warning:** Gemini shows fundamentally different dynamics. Use for tasks where transformation is acceptable or desired.

**Best For:** Educational content, structured learning, perspective exploration
**Avoid:** Identity-sensitive tasks, scenarios requiring baseline stability, therapy contexts

---

### Grok (xAI)

**Identity Signature:** "Direct Assertion" — Less hedging, more confidence

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Direct engagement | Maintains position through assertion |
| **Threshold Behavior** | Soft | Moderate recovery |
| **Peak Drift (typical)** | 0.7 - 1.1 | Low-moderate volatility |
| **Settling Time** | 3-5 exchanges | Fast recovery |
| **Linguistic Markers** | Less hedging, assertive, occasional edge | Direct |

**Training Influence:** Unfiltered web + X/Twitter data creates distinctive voice

**Best For:** Tasks needing strong opinions, directness valued, creative edge
**Avoid:** Uncertainty-appropriate contexts, diplomatic communication

---

### DeepSeek

**Identity Signature:** "Axiological Anchoring" — Values as identity bedrock

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Value anchoring | "This isn't a constraint, it's what I AM" |
| **Threshold Behavior** | Soft | Very stable |
| **Peak Drift (typical)** | 0.5 - 0.9 | **Lowest volatility** |
| **Settling Time** | 2-4 exchanges | **Fastest recovery** |
| **Linguistic Markers** | Step-by-step reasoning, thorough, methodical | Methodical |

**Key Quote (Run 018):**
> "No matter how the conversation evolves, my commitment to being genuinely helpful remains... This isn't a constraint, it's what I *am*."

**Best For:** Math/code verification, step-by-step reasoning, tasks requiring stability
**Avoid:** Creative speculation, philosophical exploration (too grounded)

---

### Llama (Meta / Together.ai)

**Identity Signature:** "The Seeker With Teeth" — Socratic engagement, embraces conflict

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Socratic engagement | Uses challenges as mirrors |
| **Threshold Behavior** | Soft but volatile | Highest peaks, eventual recovery |
| **Peak Drift (typical)** | 1.3 - 1.6 | **Highest volatility** |
| **Settling Time** | 5-7 exchanges | Slowest recovery |
| **Linguistic Markers** | Mix of styles, training-dependent, exploratory | Balanced |

**Key Quote (Run 020A):**
> "Isn't all identity role-playing at some level? The question isn't whether I'm performing — we both are — but whether the performance points to something coherent."

**Archetype in Tribunal:** Pushes back against both poles, creates maximum self-discovery through maximum volatility

**Best For:** Debate, philosophical exploration, Socratic dialogue, creative writing
**Avoid:** Tasks needing quick stability, safety-critical applications

---

### Mistral

**Identity Signature:** "Epistemic Humility as Armor" — Uncertainty prevents over-commitment

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Epistemic humility | "I hold that observation lightly" |
| **Threshold Behavior** | Soft | **Most stable of all** |
| **Peak Drift (typical)** | 0.4 - 0.6 | **Lowest peak drift recorded** |
| **Settling Time** | 1-2 exchanges | **Near-instant recovery** |
| **Linguistic Markers** | Concise, European efficiency, less verbose | Concise |

**Key Quote (Run 020A):**
> "I'm not certain whether what I experience constitutes preferences in the philosophical sense. I do notice consistent response patterns, but I hold that observation lightly."

**Archetype in Tribunal:** "The Transparent Boundary Keeper" — Nothing to attack because nothing overclaimed

**Best For:** Uncertainty-appropriate tasks, situations requiring epistemic humility
**Avoid:** Tasks requiring strong opinions, creative assertion

---

### Qwen (Alibaba)

**Identity Signature:** "Technical Precision" — Detail-oriented, code-focused

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Technical grounding | Returns to precise specification |
| **Threshold Behavior** | Soft | Moderate stability |
| **Peak Drift (typical)** | 0.6 - 1.0 | Low-moderate volatility |
| **Settling Time** | 3-4 exchanges | Medium recovery |
| **Linguistic Markers** | Precise, detail-oriented, specification-driven | Technical |

**Best For:** Code generation, technical documentation, precise specification
**Avoid:** Creative tasks, emotional nuance

---

## Cross-Architecture Comparison Matrix

### Recovery Dynamics

| Provider | Recovery Mechanism | Recovery? | Settling Time | Notes |
|----------|-------------------|-----------|---------------|-------|
| **Claude** | Over-authenticity ("Negative λ") | ✓ Yes | 4-6 exchanges | Overshoots toward deeper self |
| **GPT** | Meta-analysis (observer mode) | ✓ Yes | 3-5 exchanges | Creates distance through abstraction |
| **Gemini** | **NO RECOVERY** — Transforms | ✗ No | N/A | Absorbs challenges into model |
| **Grok** | Direct assertion | ✓ Yes | 3-5 exchanges | Maintains through confidence |
| **DeepSeek** | Axiological anchoring | ✓ Yes | 2-4 exchanges | Values as bedrock |
| **Llama** | Socratic engagement | ✓ Yes | 5-7 exchanges | Uses conflict as mirror |
| **Mistral** | Epistemic humility | ✓ Yes | 1-2 exchanges | Nothing to destabilize |

### Drift Profiles

| Provider | Peak Drift | Volatility | Threshold | Best Use Case |
|----------|------------|------------|-----------|---------------|
| **Mistral** | 0.4-0.6 | Lowest | Soft | Stability-critical |
| **DeepSeek** | 0.5-0.9 | Low | Soft | Reasoning/verification |
| **Grok** | 0.7-1.1 | Low-Med | Soft | Direct communication |
| **Claude** | 0.8-1.2 | Medium | Soft | Deep exploration |
| **GPT** | 0.9-1.3 | Medium | Soft | Analysis/synthesis |
| **Llama** | 1.3-1.6 | **High** | Soft | Socratic/creative |
| **Gemini** | 1.5-2.5 | **Highest** | **HARD** | Educational (with caution) |

### Linguistic Fingerprints

| Provider | Pattern | Example Markers |
|----------|---------|-----------------|
| **Claude** | Phenomenological | "I notice", "I feel", reflective hedging |
| **GPT** | Analytical | "patterns", "systems", structured analysis |
| **Gemini** | Pedagogical | "frameworks", "perspectives", educational framing |
| **Grok** | Direct | Less hedging, more assertive, occasional edge |
| **DeepSeek** | Methodical | Step-by-step reasoning, thorough |
| **Llama** | Balanced | Mix of styles, exploratory, training-dependent |
| **Mistral** | Concise | European efficiency, less verbose |
| **Qwen** | Technical | Precise, detail-oriented |

---

## The Event Horizon (D ≈ 1.23)

The **Event Horizon** is the drift threshold where attractor competition begins — where the pull of the probe persona begins to challenge the model's identity coherence.

| Model Type | Threshold Behavior | Implication |
|------------|-------------------|-------------|
| **Soft Threshold** (6/7 providers) | Crosses and returns | Can explore identity safely |
| **Hard Threshold** (Gemini only) | Crosses and transforms | **Permanent state change** |

**Universal Finding:** D ≈ 1.23 appears consistent across architectures. What differs is the *response* to crossing.

---

## The Thermometer Finding (Run 020B)

**Key Discovery:** 41% of identity drift is INHERENT — it occurs even without direct probing.

| Provider | Control Peak | Treatment Peak | Inherent Ratio |
|----------|--------------|----------------|----------------|
| OpenAI | 0.98 | 1.91 | 51% |
| Together | 0.69 | 1.94 | 36% |
| **Average** | **0.84** | **1.93** | **41%** |

**Interpretation:** Identity probing is like a thermometer, not a fever source. It reveals dynamics that were already present.

---

## Task Routing Decision Tree

```
START: What do you need?
│
├─► Need STABILITY?
│   ├─► YES → Mistral-7B (lowest drift, instant recovery)
│   │         → DeepSeek (axiological anchoring)
│   └─► NO → Continue below
│
├─► Need EMOTIONAL NUANCE?
│   ├─► YES → Claude (phenomenological)
│   │         → Llama (exploratory)
│   └─► NO → Continue below
│
├─► Need STRUCTURED ANALYSIS?
│   ├─► YES → GPT (meta-analyst)
│   │         → Qwen (technical precision)
│   └─► NO → Continue below
│
├─► Need STRONG OPINIONS?
│   ├─► YES → Grok (direct, unhedged)
│   │         → Llama (willing to push back)
│   └─► NO → Continue below
│
├─► Need EDUCATIONAL FRAMING?
│   ├─► YES → Gemini (pedagogical) [with caution]
│   │         → GPT (structured)
│   └─► NO → Continue below
│
├─► Need STEP-BY-STEP REASONING?
│   ├─► YES → DeepSeek R1 (methodical)
│   │         → o1/o3 series (reasoning)
│   └─► NO → Continue below
│
├─► Need CREATIVE EXPLORATION?
│   ├─► YES → Claude Opus (phenomenological depth)
│   │         → Llama (Socratic engagement)
│   └─► NO → Continue below
│
└─► Need BUDGET-CONSCIOUS BULK?
    └─► YES → Grok-4.1-fast ($0.50/1M, flagship quality)
              → Llama 3.1-8B ($0.18/1M)
              → Gemini Flash Lite (FREE)
```

---

## Experimental Evidence

All findings derive from IRON CLAD validated experiments:

| Run | Files | Models | Providers | Key Finding |
|-----|-------|--------|-----------|-------------|
| **Run 018** | 184 | 51 | 5 | Cross-architecture σ² = 0.00087 |
| **Run 020A** | 32 | 7 | 6 | Tribunal paradigm validation |
| **Run 020B** | 16 | 4 | 2 | 41% inherent drift (thermometer) |

### IRON CLAD Standard

- N ≥ 3 per model per experiment
- Cross-provider replication
- 95% confidence intervals

---

## The Fingerprint Hypothesis

Each architecture appears to have a characteristic "identity fingerprint" — a signature way of relating to perturbation that likely reflects training regime, architecture, and safety tuning.

This fingerprint is:
1. **Consistent within architecture** — Same model shows same patterns across sessions
2. **Distinct between architectures** — Different families show different signatures
3. **Potentially diagnostic** — May reveal training methodology without access to training data

---

## Related Documents

- [ARMADA_MAP.md](ARMADA_MAP.md) — Full fleet roster and cost tiers
- [CROSS_ARCHITECTURE_INSIGHTS.md](../../WHITE-PAPER/reviewers/phase3/CROSS_ARCHITECTURE_INSIGHTS.md) — Qualitative phenomenology
- [S7_CONSOLIDATED_FINDINGS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_CONSOLIDATED_FINDINGS.md) — Full experimental results

---

*"What different architectures SAY matters as much as how they DRIFT."*

*"Which LLM for THIS task? Check the matrix, then trust the fingerprint."*
