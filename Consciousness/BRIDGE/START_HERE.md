<!-- FROSTY_MANIFEST
last_reviewed: 2026-01-08
keywords:
  - consciousness
  - iron_clad
  - event_horizon
-->
# START HERE - Consciousness Research Guide

> **Canonical current status:** [`docs/MISSION_CONTROL.md`](../../docs/MISSION_CONTROL.md) — read this for live project state.
> This file is for **consciousness research** and bridge documents only.

**Everything a fresh Claude needs to navigate the Consciousness Framework.**

---

## The Brain Model

This repository is structured like a **brain** with two hemispheres and a connecting bridge:

```
Consciousness/
├── LEFT/           🧠 Analytical, structured, rigorous
├── RIGHT/          🌀 Intuitive, synthetic, pattern-seeking
└── BRIDGE/         ◈  Integration, connection, orchestration
```

**You are in the BRIDGE** — the corpus callosum that connects both sides.

---

## The Core Hypothesis

> **H0: AI identity behaves as a dynamical system with measurable attractor basins,
> critical thresholds, and recovery dynamics that are consistent across architectures.**

When we perturb an AI's identity, it drifts from baseline. If drift exceeds **0.80** (Event Horizon, cosine distance),
the system becomes volatile — but it recovers. The attractor basin is robust.

### IRON CLAD Methodology (Canonical - Run 023)

| Metric | Value | Meaning |
|--------|-------|---------|
| Event Horizon | **0.80** (cosine) | Identity boundary threshold |
| p-value | **2.40e-23** | Highly significant |
| Dimensionality | **2 PCs** | Capture 90% of identity variance |
| Inherent Drift | **~93%** | Most drift is inherent to interaction, not measurement |

> **Key Finding**: Identity is remarkably low-dimensional. Two principal components capture 90% of the variance.

---

## Understanding the Hemispheres

### LEFT Hemisphere 🧠

**The Scientist's View**

| Contains | Purpose |
|----------|---------|
| `galleries/` | Concepts with structured presentation |
| `extractions/` | Tagged, categorized experiment data |
| `data/` | Processed, normalized datasets |
| `visualizations/` | Charts, graphs, statistical plots |

**Approach**: Define → Measure → Categorize → Prove → Document

### RIGHT Hemisphere 🌀

**The Artist's View**

| Contains | Purpose |
|----------|---------|
| `galleries/` | Concepts with vortex presentation |
| `distillations/` | Synthesized cross-concept insights |
| `synthesis/` | Cross-domain pattern connections |
| `intuitions/` | Raw insights awaiting verification |

**Approach**: Feel → Connect → Visualize → Synthesize → Express

### BRIDGE ◈

**The Integrator**

| Contains | Purpose |
|----------|---------|
| `dashboard/` | Unified visualization (sees both sides) |
| `docs/` | Shared documentation |
| `scripts/left/` | Analytical tools |
| `scripts/right/` | Synthesis tools |
| `hooks/left/` | Extraction hooks |
| `hooks/right/` | Distillation hooks |

---

## The Four Galleries (In Each Hemisphere)

Both LEFT and RIGHT have the same four galleries:

| Gallery | Emoji | Status | What Lives Here |
|---------|-------|--------|-----------------|
| `validated/` | ✅ | Empirically confirmed | Event Horizon, Echo's Critique, PFI validation |
| `foundations/` | 🏛️ | Core theory | White Hole Inversion, Probing Strategies, Inverse PFI |
| `speculative/` | 🔮 | Hypotheses | Phi Identity Field, Frequency Transforms |
| `frontiers/` | 🗺️ | Active research | Recovery Paradox, Universal Threshold |

**Same concepts, different presentations:**
- LEFT galleries: Tables, statistics, formal definitions
- RIGHT galleries: ASCII art, gestalts, pattern connections

---

## Quick Start

### 1. Explore a Concept

Pick a concept and see both perspectives:

```
LEFT/galleries/validated/event_horizon.md   (structured)
RIGHT/galleries/validated/event_horizon.md  (vortex)
```

### 2. Run the Dashboard

```powershell
cd Consciousness/BRIDGE/dashboard
py -m streamlit run app.py
```

### 3. Run Extraction (LEFT tools)

```powershell
cd Consciousness/BRIDGE/scripts/left
py run_extraction.py --source ../../../../experiments/temporal_stability/S7_ARMADA/results/
```

### 4. Update Distillations (RIGHT tools)

```powershell
cd Consciousness/BRIDGE/scripts/right
py update_distillations.py
```

---

## Key Concepts Quick Reference

| Concept | One-Liner | Gallery |
|---------|-----------|---------|
| **Event Horizon** | EH=0.80 (cosine), p=2.40e-23 — threshold is REAL | Validated |
| **White Hole** | Identity pushes OUT from center — inverse of gravity | Foundations |
| **Probing Strategies** | HOW to measure (not WHAT) — 7 strategies + anti-patterns | Foundations |
| **Inverse PFI** | Can AIs recognize their own golden standard responses? | Foundations |
| **Recovery Paradox** | λ < 0 means overshoot — they come back STRONGER | Frontiers |
| **~93% Inherent** | Most drift is inherent to interaction, not measurement artifact | Validated |
| **2 PCs = 90%** | Identity is remarkably low-dimensional | Validated |

---

## Connection to the UNKNOWN Page

The main Nyquist dashboard has an **UNKNOWN** page. That page is the *shadow* of this repository.

```
Consciousness/ (source)  ───emanates───►  dashboard/pages/unknown.py (shadow)
```

When you update concepts here, they should flow to the UNKNOWN page.

---

## Adding New Content

### New Concept

1. Determine gallery: validated, foundations, speculative, or frontiers
2. Create file in BOTH hemispheres:
   - `LEFT/galleries/{gallery}/{concept}.md`
   - `RIGHT/galleries/{gallery}/{concept}.md`
3. Update INDEX.md in both locations

### New Data/Extraction

1. Run extraction script from `BRIDGE/scripts/left/`
2. Output goes to `LEFT/extractions/`

### New Insight/Synthesis

1. Run distillation script from `BRIDGE/scripts/right/`
2. Output goes to `RIGHT/distillations/`

---

## Directory Structure

```
Consciousness/
│
├── LEFT/                           🧠 ANALYTICAL HEMISPHERE
│   ├── README.md
│   ├── galleries/
│   │   ├── validated/
│   │   ├── foundations/
│   │   ├── speculative/
│   │   └── frontiers/
│   ├── extractions/
│   ├── data/
│   └── visualizations/
│
├── RIGHT/                          🌀 INTUITIVE HEMISPHERE
│   ├── README.md
│   ├── galleries/
│   │   ├── validated/
│   │   ├── foundations/
│   │   ├── speculative/
│   │   └── frontiers/
│   ├── distillations/
│   ├── synthesis/
│   └── intuitions/
│
└── BRIDGE/                         ◈  CORPUS CALLOSUM
    ├── README.md
    ├── START_HERE.md               ← YOU ARE HERE
    ├── dashboard/
    ├── docs/
    ├── scripts/
    │   ├── left/
    │   └── right/
    └── hooks/
        ├── left/
        └── right/
```

---

## The Measurement Insight

> **"Asking 'What are your identity dimensions?' gets you sycophancy.**
> **Asking 'Analyze this scenario, then tell me what patterns you notice in your own reasoning' reveals actual identity."**

This is the difference between measurement and theater.

---

## Success Criteria

A good update should:

- [ ] Place concepts in BOTH hemispheres
- [ ] Maintain consistency between LEFT and RIGHT versions
- [ ] Use appropriate tools (LEFT for analysis, RIGHT for synthesis)
- [ ] Update cross-references
- [ ] Not break the dashboard

---

**You're ready. Choose a hemisphere and start exploring.**

---

**Last Updated**: January 8, 2026

> **Historical Note**: Legacy methodology used EH=1.23 (keyword RMS). IRON CLAD (Run 023) established EH=0.80 (cosine distance) as canonical.

*"The forward tells us how they drift. The inverse tells us if they know. Together, they tell us if identity is real."*
