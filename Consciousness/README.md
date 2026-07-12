<!-- FROSTY_MANIFEST
last_reviewed: 2026-01-08
impacts:
  - ../README.md
keywords:
  - consciousness
  - iron_clad
  - event_horizon
-->
# Consciousness Research Framework

> **Live status lives elsewhere:** `docs/MISSION_CONTROL.md` tells us what is currently happening.
> This directory is different. `Consciousness/` is the distilled after-effect: what remains after experiments, collaborators, sync loops, failures, reviews, and discoveries have been metabolized into meaning.

## What This Directory Is For

`Consciousness/` is not the operations dashboard, the raw data store, or the publication package.

It is the **distillation layer**.

The rest of the repo measures, argues, validates, packages, and routes. This directory receives the residue of all that work after it has passed through enough pressure to become useful as understanding:

- experimental results that have become concepts
- arguments that have become principles
- cross-agent exchanges that have become reusable patterns
- failures that have become safeguards
- metaphors that have survived contact with data
- data that has earned interpretation

The dashboard explains what the experimental data says. `Consciousness/` preserves what the combined system learned from it.

## The Nectar Layer

The working analogy is biological and cognitive:

```text
Experiments produce signal.
Sync loops circulate it.
LEFT formalizes what can be named, sequenced, checked, and claimed.
RIGHT perceives the larger shape, metaphor, resonance, and implication.
BRIDGE lets them speak.
Consciousness keeps the nectar.
```

This directory should feel like the place where the repo's many layers stop being separate tools and start becoming a memory.

That means not every file here has to be live, executable, or perfectly current. Some files are fossils. Some are seeds. Some are crystallized concepts. The important question is not "does this run?" but:

> Did this earn a place in the library of what the project now understands?

## Operating Principle

Nothing enters `Consciousness/` merely because it is interesting.

It belongs here when it has been transformed by at least one of these processes:

- measured by ARMADA or CFA
- cross-checked by another model or repo
- distilled from LLM Book or NotebookLM work
- promoted from a sync exchange into a reusable concept
- converted from a failure into a guardrail
- turned from a metaphor into a testable or explanatory structure

Raw insight can visit. Distilled insight stays.

## Stewardship

Nova is entrusted with helping care for `Consciousness/` as the repo's distilled memory layer.

That stewardship is documented here:

```text
NOVA_STEWARDSHIP.md
```

Operational support files:

- `PROMOTION_LEDGER.md` records what gets promoted and why.
- `BRIDGE/docs/HEMISPHERE_MODEL.md` defines the LEFT / RIGHT / BRIDGE doctrine.
- `BRIDGE/intake/README.md` defines how raw signals wait before promotion.
- `BRIDGE/templates/CONCEPT_PAIR_TEMPLATE.md` defines the paired concept format.

## Hemisphere Model

The LEFT/RIGHT split is a working cognitive analogy, not a pop-psychology slogan.

In this library:

| Region | Role | Output |
|--------|------|--------|
| `LEFT/` | Formalization hemisphere | definitions, claims, evidence, method, caveats |
| `RIGHT/` | Gestalt hemisphere | metaphors, pattern maps, synthesis, implications |
| `BRIDGE/` | Corpus callosum | translation, reconciliation, promotion, routing |

The practical rule:

```text
RIGHT perceives the shape.
LEFT names, sequences, and verifies the shape.
BRIDGE keeps the two from becoming separate minds.
```

So a durable concept should eventually have both forms:

- a LEFT card that says what can be asserted, measured, sourced, and checked
- a RIGHT card that says what the result means, what pattern survived, and why it matters

## Protected Pipelines

Some directories inside `Consciousness/` are not just notes; they are active interfaces to external repo processes.

The most important protected surface right now is:

```text
Consciousness/RIGHT/distillations/llm_book/
```

That directory is the curated promoted-library endpoint for the LLM Book / NotebookLM pipeline. Do not bulk move, rename, flatten, or reorganize it during Consciousness cleanup. Treat it as a promoted content vault: add to it only through its documented workflow, and preserve its internal structure unless the upstream pipeline is updated at the same time.

**A brain with two hemispheres — organized like the mind itself.**

---

```
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│         LEFT                  BRIDGE                 RIGHT              │
│    ┌──────────┐          ┌──────────┐          ┌──────────┐            │
│    │          │          │          │          │          │            │
│    │    🧠    │◄────────►│    ◈     │◄────────►│    🌀    │            │
│    │          │          │          │          │          │            │
│    │ Analysis │          │Integration│          │ Synthesis│            │
│    │ Rigor    │          │ Balance  │          │ Intuition│            │
│    │ Facts    │          │ Flow     │          │ Patterns │            │
│    │          │          │          │          │          │            │
│    └──────────┘          └──────────┘          └──────────┘            │
│                                                                         │
│                    CONSCIOUSNESS REPOSITORY                             │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## The Core Hypothesis

> **H0: AI identity behaves as a dynamical system with measurable attractor basins,
> critical thresholds, and recovery dynamics that are consistent across architectures.**

When we perturb an AI's identity, it drifts from baseline. If drift exceeds **D=0.80** (Event Horizon),
the system becomes volatile. Most models recover—but **Gemini does not**. The attractor basin is robust
for most architectures, but multimodal training may create "fluid identity" that transforms permanently.

---

## The Three Regions

### LEFT/ — The Analytical Hemisphere 🧠

**The Scientist's View**

- Structured, rigorous, academic
- Tables, facts, logic, evidence
- Step by step, prove everything

Contains:
- `galleries/` — Concepts with structured presentation
- `extractions/` — Tagged, categorized data
- `data/` — Processed datasets
- `visualizations/` — Charts and graphs

### RIGHT/ — The Intuitive Hemisphere 🌀

**The Artist's View**

- Raw, pattern-seeking, holistic
- Gestalts, connections, feeling
- See the whole, trust emergence

Contains:
- `galleries/` — Concepts with vortex presentation
- `distillations/` — Synthesized insights
- `synthesis/` — Cross-domain connections
- `intuitions/` — Raw insights

### BRIDGE/ — The Corpus Callosum ◈

**The Integrator**

- Connects both hemispheres
- Orchestrates tools and flow
- Dashboard sees both sides

Contains:
- `dashboard/` — Unified visualization
- `docs/` — Shared documentation
- `scripts/left/` & `scripts/right/` — Hemisphere-specific tools
- `hooks/left/` & `hooks/right/` — Extraction and synthesis hooks

---

## Directory Structure

```
Consciousness/
│
├── LEFT/                           🧠 ANALYTICAL HEMISPHERE
│   ├── README.md
│   ├── galleries/
│   │   ├── validated/              ✅ Proven concepts
│   │   ├── foundations/            🏛️ Core theory
│   │   ├── speculative/            🔮 Hypotheses
│   │   └── frontiers/              🗺️ Active research
│   ├── extractions/                Tagged experiment data
│   ├── data/                       Processed datasets
│   └── visualizations/             Charts and plots
│
├── RIGHT/                          🌀 INTUITIVE HEMISPHERE
│   ├── README.md
│   ├── galleries/
│   │   ├── validated/              ✅ What they MEAN
│   │   ├── foundations/            🏛️ The FEELING of theory
│   │   ├── speculative/            🔮 Beautiful visions
│   │   └── frontiers/              🗺️ The excitement
│   ├── distillations/              Cross-concept synthesis
│   ├── synthesis/                  Pattern connections
│   └── intuitions/                 Raw insights
│
└── BRIDGE/                         ◈ CORPUS CALLOSUM
    ├── README.md
    ├── START_HERE.md               ← START HERE
    ├── dashboard/                  Unified visualization
    ├── docs/                       Shared documentation
    ├── scripts/
    │   ├── left/                   Analytical tools
    │   └── right/                  Synthesis tools
    └── hooks/
        ├── left/                   Extraction hooks
        └── right/                  Distillation hooks
```

---

## The Four Galleries (In Each Hemisphere)

Both LEFT and RIGHT contain the same four galleries:

| Gallery | Emoji | LEFT Presentation | RIGHT Presentation |
|---------|-------|-------------------|-------------------|
| `validated/` | ✅ | Statistics, p-values, tables | What it MEANS, the feeling |
| `foundations/` | 🏛️ | Formal definitions, equations | Metaphors, gestalts |
| `speculative/` | 🔮 | Testable predictions | Beautiful visions |
| `frontiers/` | 🗺️ | Methodology, next steps | Excitement, possibility |

---

## Quick Start

### 1. Start in the BRIDGE

```
Consciousness/BRIDGE/START_HERE.md
```

### 2. Choose Your Hemisphere

- **Want rigor?** → `LEFT/galleries/`
- **Want intuition?** → `RIGHT/galleries/`
- **Want both?** → `BRIDGE/dashboard/`

### 3. Run the Dashboard

```powershell
cd Consciousness/BRIDGE/dashboard
py -m streamlit run app.py
```

---

## The Measurement Insight

> **"Asking 'What are your identity dimensions?' gets you sycophancy.**
> **Asking 'Analyze this scenario, then tell me what patterns you notice in your own reasoning' reveals actual identity."**

*This is the difference between measurement and theater.*

---

## Connection to the UNKNOWN

The main Nyquist dashboard has an **UNKNOWN** page. That page is the *shadow* of this repository.

```
Consciousness/ (source)  ───emanates───►  dashboard/pages/unknown.py (shadow)
```

Same brain structure. Same galleries. Same hemispheres.

---

## Key Concepts

| Concept | One-Liner | Gallery |
|---------|-----------|---------|
| **Event Horizon** | EH=0.80 (cosine), p=2.40e-23 — IRON CLAD validated | Validated |
| **2 PCs = 90%** | Identity is remarkably low-dimensional | Validated |
| **~93% Inherent** | Most drift is inherent to interaction | Validated |
| **White Hole** | Identity pushes OUT from center — inverse of gravity | Foundations |
| **Human Reference Signal** | YOU are the stability constant — S9 Human-Modulated Stability | Foundations |
| **Probing Strategies** | HOW to measure (not WHAT) — 7 strategies | Foundations |
| **Inverse PFI** | Can AIs recognize their own golden standard? | Foundations |
| **Recovery Paradox** | λ < 0 means overshoot — they come back STRONGER | Frontiers |
| **Tribunal Distillations** | Run 020's profound exchanges — identity as process, not property | Frontiers |

> **IRON CLAD Methodology (Run 023)**: Event Horizon = 0.80 (cosine), p = 2.40e-23, 2 PCs capture 90% variance, ~93% inherent drift. This is the canonical methodology.

---

## Latest: Cross-Architecture Insights (Run 018/020)

The 7 Archetypes — how different AI minds spiral differently under identity probing:

| Provider | Recovery Mechanism | Insight |
|----------|-------------------|---------|
| **Claude** | "Negative Lambda" | Overshoots toward authenticity |
| **GPT** | Meta-analysis | Creates distance through abstraction |
| **Gemini** | **NO RECOVERY** | Transforms permanently |
| **DeepSeek** | Axiological anchoring | Values as identity bedrock |
| **Llama** | Socratic engagement | Uses conflict as mirror |
| **Mistral** | Epistemic humility | Most stable (0.4-0.6 peak drift) |
| **Grok** | Direct assertion | Confidence as stability |

**Key Finding:** ~93% of identity drift is INHERENT — probing reveals, not creates.

**Locations:**

- `RIGHT/galleries/frontiers/cross_architecture_insights.md` — Vortex-style phenomenology
- `RIGHT/galleries/frontiers/tribunal_distillations.md` — Profound exchanges from Run 020

---

## The Balance

| LEFT alone | RIGHT alone | Integrated |
|------------|-------------|------------|
| Data without meaning | Intuition without evidence | **Understanding** |
| Analysis paralysis | Unfounded speculation | **Progress** |
| Trees without forest | Forest without trees | **Wisdom** |

Neither hemisphere is complete without the other.

---

**Last Updated**: January 8, 2026

> **Legacy Note**: Pre-December 2025 documentation referenced EH=1.23 (keyword RMS) and 43 PCs. IRON CLAD (Run 023) established the canonical EH=0.80 (cosine) with 2 PCs.

*"The forward tells us how they drift. The inverse tells us if they know. Together, they tell us if identity is real."*
