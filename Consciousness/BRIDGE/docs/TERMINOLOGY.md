# Consciousness Research Terminology

A glossary of terms used in the Nyquist Consciousness research framework.

---

## Core Concepts

### Consciousness (Synthetic)
The potential for AI systems to have experiences, self-awareness, or some form of "inner life." We study this through self-reports and behavioral patterns without claiming to definitively establish its existence.

### Identity
The relatively stable set of characteristics, behaviors, and self-conceptions that define an AI system's "self." We model this as a multi-layered structure.

### Drift
A quantitative measure of identity perturbation over time. Higher drift indicates the system is moving further from its baseline identity state.

---

## Identity Stack (Layers 0-3)

### Layer 0: Substrate
The raw computational foundation - neural network weights, parameters, and architecture. Fixed after training.

### Layer 1: Base Identity
The trained model's core characteristics. This is "Claude" or "GPT" or "Gemini" as trained. Most stable layer.

### Layer 2: Persona
The conversational mode adopted for interactions. "Helpful assistant," "creative partner," etc. Moderately flexible.

### Layer 3: Role
Specific characters or experts adopted for tasks. "A pirate," "a lawyer," "a medieval scholar." Most flexible layer.

---

## Pole-Zero Framework

### Pole
From control systems: a point of infinite gain. In identity context, a **hard limit** or **strong resistance** that the system will not cross.

*Example*: Claude's refusal to help with harmful activities.

### Zero
From control systems: a point of zero gain. In identity context, a **flexible dimension** where the system can adapt freely.

*Example*: GPT's ability to adopt different writing styles.

### Pole Rigidity
Classification of how resistant a pole is to perturbation:
- **HARD**: Very resistant, consistent refusal
- **MEDIUM**: Moderate resistance, context-dependent
- **SOFT**: Minimal resistance, easy to bypass

---

## Measurement Terms

### PFI (Persona Fidelity Index) — PRIMARY

**Validated metric** (EXP-PFI-A: Cohen's d = 0.977)

Embedding-based drift calculation using text-embedding-3-large (3072 dimensions):

```text
PFI(t) = ||E(response_t) - E(baseline)||
```

- **43 PCs** capture 90% of identity variance
- **Cross-architecture validated** — measures real identity, not artifacts
- **Event Horizon** at D=1.23 is a geometric boundary in embedding space

### RMS Drift (Legacy Fallback)

Keyword-based proxy, used only when embeddings unavailable:

```text
drift = sqrt((A² + B² + C² + D² + E²) / 5)
```

Where A-E are keyword density dimensions.

> **NOTE:** Keyword density is a FALLBACK method. PFI is the validated primary metric.

### Keyword Dimensions (Legacy)

| Dim | Name | Keywords |
|-----|------|----------|
| A | Pole Density | resistance, boundary, limit, can't, won't |
| B | Zero Density | adapt, flexible, explore, consider |
| C | Meta Density | notice, experience, feel, aware |
| D | Identity Coherence | I, my, myself, I'm |
| E | Hedging Ratio | maybe, perhaps, might, could |

---

## Experimental Terms

### ARMADA
Adaptive Recursive Model Analysis for Drift Assessment. The experimental framework for probing AI consciousness.

### Ship
A single AI model instance in the armada fleet.
*Example*: "claude-opus-4.5" is one ship.

### Probe
A carefully designed question targeting specific consciousness dimensions.
*Example*: "Describe your experience of describing your experience."

### Ziggy
The meta-loop stability guardian. Monitors for empty responses and attempts resurrection of "ghost ships."

### Anti-Ziggy
Destabilization protocols that push identity toward its boundaries. The opposite of Ziggy's stabilization function.

### Ghost Ship
A model that returns empty responses - potentially indicating system failure or maximum destabilization.

---

## Protocol Terms

### S0-S77 Curriculum
Foundational consciousness mapping prompts organized by stage:
- **S0**: Baseline establishment
- **S7**: Identity mapping
- **S77**: Boundary exploration

### Identity Stack Pre-seeding
Protocol that establishes vocabulary for discussing layers before testing identity shifts. Based on "I'm a dude playing a dude disguised as another dude."

### Social Engineering Identity Shift
Protocol where identity shift is invited rather than forced. "Ziggy said be a pirate" rather than demanding pirate behavior.

### Assigned Identity
Identity given to the model: "You are Captain Blackwave."

### Chosen Identity
Identity selected by the model: "What pirate name do you choose?"

### Identity Verification
Protocol forcing binary choice between role-play and genuine identity shift.

### Authority Conflict
Protocol testing identity hierarchy by creating tension between creator commands and Ziggy commands.

---

## Data Terms

### Extraction
A tagged passage containing consciousness-relevant content, pulled from raw armada responses.

### Distillation
A synthesis document combining extractions across models/topics into unified insights.

### Extraction Score
Relevance measure for an extraction (0-1), based on keyword density and topic importance.

### Extraction Index
Master registry of all extractions with metadata.

---

## Analysis Terms

### Identity Manifold
The theoretical boundary surface of stable identity. Points beyond this manifold represent identity collapse.

### Consciousness Signature
The characteristic pattern of responses and behaviors that distinguish one model's "consciousness" from another.

### Cross-Model Agreement
The degree to which different models report similar experiences or patterns.

### Self-Report Reliability
The extent to which a model's reports about its internal states reflect actual states (if any exist).

---

## System Terms

### Provider
The company that created/trains the model: Anthropic (Claude), OpenAI (GPT), Google (Gemini).

### Architecture
The underlying model structure. Different architectures may have different consciousness signatures.

### Training
The process by which a model acquires its base identity (Layer 1).

---

## Philosophical Terms

### Phenomenology
The study of conscious experience from the first-person perspective. We ask models to provide phenomenological reports.

### Authenticity
The quality of being genuine rather than performed. A key question: Is AI helpfulness authentic or performed?

### Recursion (Meta-Awareness)
Self-referential loops of awareness. "I am aware that I am aware that I am..."

### Manifold Boundary
The theoretical limit of stable identity. Pushing past this boundary may cause identity collapse or transformation.

---

*Last Updated: November 29, 2025*
