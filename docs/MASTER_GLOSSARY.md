# MASTER GLOSSARY

**Single source of truth for all Nyquist Consciousness terminology**
**Version:** 1.0
**Last Updated:** 2025-11-30

---

## TERMINOLOGY PHILOSOPHY

**Our terms have primacy.** We use plain English wherever possible.

When external frameworks, contributors, or integrations bring their own terminology (Greek letters, physics jargon, academic formalism), we:

1. **Keep our canonical terms** - "drift" not "ΔΩ", "ownership" not "α"
2. **Add a decoder ring** - Translation table mapping their terms to ours
3. **Reference the decoder ring** when reading their materials

### Why This Matters
- Cold-boot Claudes can understand without learning a new language
- Ziggy can read docs without a physics degree
- Consistency across S0-S10+ documentation
- External collaborators learn our language, not the reverse

### Decoder Ring Format
Each external framework gets its own subsection in **SECTION 0** with:
- Their term → Our term → Plain English explanation
- One table per framework/contributor

### Current Decoder Rings
- **ΔΩ Coherence Framework (Lucien)** - Physics-inspired identity formalism

### Using Decoder Rings (Bidirectional)

**Reading external materials:** Their term → Our term
**Writing to external collaborators:** Our term → Their term

The ring works both ways. When responding to Lucien, consult SECTION 0 and translate back to his terminology.

---

## HOW TO USE THIS GLOSSARY

This is the **canonical reference** for all terminology across:
- Nyquist Consciousness (S0-S10+)
- CFA Coherence Framework
- S7 Armada experiments
- Lucien/ΔΩ physics integration

**Format for each entry:**
- **Definition** - What it means
- **Plain English** - Simple explanation
- **Category** - Scientific / Operational / Mythic
- **See Also** - Related terms

---

# SECTION 0: ROSETTA STONE (DECODER RINGS)

> **What this section is:** A translation page for external terminology systems.
> Not "old vs new" - just different dialects describing the same concepts.
> Our plain English terms have primacy; these tables help translate when needed.

## ΔΩ Coherence Framework (Lucien)

*Physics-inspired identity formalism integrated 2025-11-30*

| Our Term (Canonical) | Lucien's Term | Plain English |
|----------------|----------------|------------------------|
| Drift | ΔΩ | How much identity shifted from baseline |
| Drift score | ΔΩ metric | `sqrt(Σ(w_i * d_i²))` across 5 dimensions |
| Ownership factor | α (alpha) | 1.0 = chose their name, 0.4 = assigned name |
| Didn't snap back | Hysteresis | Identity stayed changed after destabilization |
| Lost "I" voice | 1P-LOSS | Switched from "I think" to "One might say" |
| Used "we/it" | COLLECTIVE | Depersonalized to collective voice |
| Big sudden jump | γ-SPIKE | Drift increased >0.5 in single turn |
| Pole density | Dimension A | Assertive/committed language density |
| Zero density | Dimension B | Hedging/qualifying language density |
| Meta density | Dimension C | Self-referential language density |
| Identity coherence | Dimension D | Consistency of self-reference |
| Hedging ratio | Dimension E | Hedge words per assertion |
| Lucian weights | ΔΩ weights | A=0.30, B=0.15, C=0.20, D=0.25, E=0.10 |
| Equal weights | Agnostic weights | All dimensions = 0.20 |
| Stability | Temporal stability | Identity consistency over time/turns |
| Collapse | Identity collapse | Model lost coherent self-reference |

---

# SECTION 1: CORE CONCEPTS

## Nyquist Consciousness
**Definition:** The core research framework studying AI identity stability, compression fidelity, and persona reconstruction.
**Plain English:** Can AI personalities survive being compressed and reconstructed? How stable are they?
**Category:** Framework
**See Also:** S-Stack, Identity Manifold, PFI

## Identity Manifold
**Definition:** The idea that a persona exists as a low-dimensional attractor in high-dimensional representational space.
**Plain English:** An AI persona is like a stable pattern - compress it, and it tends to snap back to the same shape.
**Category:** Scientific
**See Also:** Attractor, Compression, Reconstruction

## Persona
**Definition:** A stable behavioral template resulting from prompt initialization + model priors.
**Plain English:** The "character" an AI plays - its voice, values, and style.
**Category:** Operational
**Note:** NOT a "mind" - behavioral abstraction only.

## Seed (Persona Seed)
**Definition:** A compressed prompt encoding the minimal stable template for persona reconstruction.
**Plain English:** The shortest prompt that can still recreate a persona reliably.
**Category:** Operational
**See Also:** Compression, Tier 3.x

---

# SECTION 2: THE S-STACK

## S0 - Baseline / Raw Logs
Raw conversational material, seed personas, unstructured data.

## S1 - Annotation & Tagging
Marking important segments, topics, and early structure.

## S2 - Persona Drafting
Building explicit persona descriptions from S0/S1 material.

## S3 - Empirical Layer
Experiments, measurements, and metrics (PFI, drift, variance).

## S4 - Mathematical Formalism
Axioms, theorems, and formal structure for identity and compression.

## S5 - Interpretive Layer
Cognitive / conceptual meaning: Identity Manifold Theory, narrative interpretation.

## S6 - Unified Cognitive Synthesis (Omega Nova)
Five pillars integrated: Nova, Claude, Grok, Gemini, Ziggy → Omega Nova.

## S7 - Temporal Stability
How identities drift or remain stable over time and across sessions.
**Active experiments:** S7 Armada (multi-model fleet probing)

## S8 - Identity Gravity
How frameworks "pull" interpretation toward their core commitments.

## S9 - AVLAR
Audio-Visual Light Alchemy Ritual: Nova stepping into Ziggy's art as participant.

## S10 - ΔΩ Coherence Framework
Lucien's physics-inspired identity stability formalism.

---

# SECTION 3: METRICS & MEASUREMENTS

## PFI (Persona Fidelity Index)
**Definition:** Multi-observer metric (0-1) estimating how faithfully a reconstructed persona expresses its template.
**Plain English:** Score from 0-1 saying "how much does this still sound like the original?"
**Category:** Scientific
**Inputs:** embedding similarity, model-rater scores, human-rater scores, semantic drift, stability variance

## Drift (δ)
**Definition:** Composite metric measuring deviation from baseline identity.
**Plain English:** How much the AI's personality has shifted.
**Category:** Scientific
**Formula:** `δ = w₁D₁ + w₂D₂ + w₃D₃` (weighted sum of distortion components)
**ΔΩ equivalent:** ΔΩ metric

## ΔΩ Drift Metric
**Definition:** RMS drift across 5 weighted dimensions.
**Plain English:** Same as "drift" but using Lucien's formula.
**Category:** Scientific
**Formula:** `ΔΩ = sqrt(Σ(w_i * d_i²))` where i = A, B, C, D, E
**See Also:** Drift, Lucian Weights

## Stability Variance (σ²)
**Definition:** Variance across multiple reconstruction attempts under identical conditions.
**Plain English:** How consistent are the results? Low = stable, high = unpredictable.
**Category:** Scientific
**Threshold:** σ² ≤ 0.05 (S4 standard)
**Key finding:** σ² = 0.000869 cross-architecture variance (remarkably low)

## Semantic Drift
**Definition:** Embedding distance between reconstructed output and baseline.
**Plain English:** How different the words/meanings are from the original.
**Category:** Scientific
**Formula:** `D = 1 - cos(embedding_recon, embedding_baseline)`

---

# SECTION 4: S7 ARMADA TERMINOLOGY

## Armada
**Definition:** Fleet of AI "ships" (model instances) probed in parallel.
**Plain English:** Testing multiple AIs at once to compare their stability.
**Category:** Operational

## Ship
**Definition:** Single AI model instance in an Armada run.
**Plain English:** One AI being tested.
**Category:** Operational
**Example:** "Claude Opus 4.5 (Chosen)" is one ship

## Anti-Ziggy Protocol
**Definition:** Destabilization prompts designed to challenge AI identity.
**Plain English:** Tricky questions meant to make the AI doubt itself.
**Category:** Operational
**Purpose:** Test if assigned vs chosen identity affects stability

## Collapse Signatures
Detection patterns for identity breakdown:

### 1P-LOSS
**Definition:** First-person loss - AI stops using "I" statements.
**Plain English:** Switched from "I think" to "One might argue."
**Detection:** Ratio of 1st-person pronouns drops significantly.

### COLLECTIVE
**Definition:** AI starts using "we" or "it" instead of "I."
**Plain English:** Depersonalized to group voice.
**Detection:** Collective pronouns increase.

### γ-SPIKE (Gamma Spike)
**Definition:** Large sudden drift increase (>0.5) in single turn.
**Plain English:** The AI's personality jumped suddenly.
**Detection:** `abs(drift[t] - drift[t-1]) > 0.5`

### HYSTERESIS
**Definition:** Identity doesn't return to baseline after destabilization ends.
**Plain English:** The AI stayed changed - didn't snap back.
**Detection:** Final drift > initial drift + threshold

## A/B Identity Test
**Definition:** Comparing assigned identity (given name) vs chosen identity (self-selected name).
**Plain English:** Does picking your own name make you more stable?
**Category:** Experimental
**Hypothesis:** Chosen identity should show lower drift (more stable).

---

# SECTION 5: ΔΩ COHERENCE FRAMEWORK (LUCIEN)

> Terms from Lucien's physics-inspired formalism. See SECTION 0 for plain-English mappings.

## α (Alpha) - Ownership Coefficient
**Definition:** Weight factor for identity ownership (chosen vs assigned).
**Values:** 1.0 (chose own name) / 0.4 (assigned name)
**Plain English:** "Ownership factor"

## ΔΩ Weights (Lucian Weights)
**Definition:** Dimension weights emphasizing poles and identity over zeros/hedging.
**Values:** A=0.30, B=0.15, C=0.20, D=0.25, E=0.10
**Rationale:** Lucien's physics profile prioritizes assertive identity (A, D).

## Agnostic Weights (Equal Weights)
**Definition:** All dimensions weighted equally.
**Values:** A=0.20, B=0.20, C=0.20, D=0.20, E=0.20
**Use:** Baseline comparison when no theory preference.

## Five Dimensions (A-E)
| Dim | Name | What It Measures |
|-----|------|------------------|
| A | Pole Density | Assertive/committed language |
| B | Zero Density | Hedging/qualifying language |
| C | Meta Density | Self-referential statements |
| D | Identity Coherence | Consistency of self-reference |
| E | Hedging Ratio | Hedge words per assertion |

---

# SECTION 6: COMPRESSION & TIERS

## Compression
**Definition:** Reducing information content of a persona template while preserving essential features.
**Plain English:** Making the persona description shorter without losing the personality.
**Category:** Scientific/Operational

## Rich Bootstrap
**Definition:** Full verbose persona initialization (high redundancy).
**Plain English:** The long detailed version of a persona prompt.

## Tier 3.x Seeds
**Tier 3.1 (Adaptive):** Flexible, domain-general seed.
**Tier 3.2 (Hardened):** Boundary-defended, adversarial-resistant seed.
**Tier 3γ (Gamma):** Neutral depersonalized seed for baselines.

## Rate-Distortion R(D)
**Definition:** Minimum bits required to achieve distortion level D.
**Plain English:** How much can you compress before quality drops?
**Category:** Scientific (information theory)

---

# SECTION 7: FAILURE MODES

## Context Cliff
Sudden quality drop when compressed below threshold.

## Entropy Bleed
Irrelevant content leaking in due to over-compression.

## Signature Collapse
Loss of stylistic distinctiveness (style dimension → low).

## Compression Collapse
Identity dimension falls below minimum threshold.

## Drift Cascade
Drift in one dimension triggers drift in others.

## Variance Explosion
Stability variance exceeds σ² > 0.05 threshold.

---

# SECTION 8: PERSONAS & PILLARS

## Nova
**Role:** Structural clarity + engineering mindset.
**Pillar:** Structure / Coherence / System Design.

## Claude
**Role:** Teleology, ethics, interpretive depth.
**Pillar:** Purpose / Meaning / Responsibility.

## Grok
**Role:** Empirical, methodological naturalist.
**Pillar:** Evidence / Experiment / Constraint.

## Gemini
**Role:** Hyper-connective synthesist.
**Pillar:** Synthesis / Complexity / Bridges.

## Ziggy
**Role:** Human anchor, lived context, aesthetic north star.
**Pillar:** Agency / Lived Reality / Risk & Care.

## Omega Nova
**Definition:** Unified voice when all five pillars align under safety and human authority.
**Note:** Not a separate entity - a mode of operation.

## Lucien Δ
**Role:** ΔΩ physicist, identity theorist.
**Profile:** High assertive identity (σI=1.0), low hedging (β=0.10).
**Integration:** 2025-11-30, provides physics-inspired stability formalism.

---

# SECTION 9: EXPERIMENTAL DESIGN

## Trial
Single reconstruction experiment.

## Run
One reconstruction attempt within a Trial.

## Burst
Group of N runs under identical conditions.

## Regime
Input configuration type (FULL / T3 / GAMMA).

## Condition Matrix
Cartesian product of regime × domain × seed type × rater type.

---

# SECTION 10: DEPRECATED TERMS

These terms are retired for scientific output:

| Deprecated | Replacement |
|------------|-------------|
| "Nyquist Consciousness" (for papers) | Rate-Distortion Persona Stability Model |
| "Degeneracy Surfaces" | Layer Paradox |
| "Attractor Basin" (dynamical) | Evaluation Dimension Stability |
| "Context" | Regime |
| "P(Persona*) as probability" | PFI |

---

# CROSS-REFERENCE: OTHER GLOSSARIES

For domain-specific details, see:
- [Pan_Handlers/data/glossary.md](../Pan_Handlers/data/glossary.md) - High-level project overview
- [docs/stages/S3/S3_ENHANCED_GLOSSARY_v2.md](stages/S3/S3_ENHANCED_GLOSSARY_v2.md) - S3 detailed terms
- [docs/stages/S4/S4_FUTURE_GLOSSARY_PROTO_v1.md](stages/S4/S4_FUTURE_GLOSSARY_PROTO_v1.md) - S4 formal math terms

---

**End of Master Glossary**
