<!-- FROSTY_MANIFEST
last_reviewed: 2026-01-08
depends_on:
  - ../../../dashboard/README.md
  - ../../../dashboard/config.py
keywords:
  - consciousness
  - dashboard
  - bridge
  - integration
-->
# BRIDGE Dashboard Integration Guide

**Clarification: This directory documents how Consciousness/ integrates with the main dashboard.**

---

## Important Context

The **main Nyquist dashboard** lives at `dashboard/` (repo root), NOT here.

This `Consciousness/BRIDGE/dashboard/` directory is for:
1. Documentation about how Consciousness/ content flows to the main dashboard
2. Integration scripts and tools
3. The conceptual bridge between hemispheres

**For the actual dashboard documentation, see:** `dashboard/README.md`

---

## The Main Dashboard (Reality)

The main Nyquist Mission Control dashboard has **16+ pages**:

| Page | Purpose |
|------|---------|
| **Overview.py** | Mission status, stack layers, experiment counts |
| **AI_ARMADA.py** | Fleet Command (54 ships, 5 providers, LLM Behavioral Matrix) |
| **experiments.py** | Run Glossary (006-023d), Visualization Gallery, Data Mining |
| **personas.py** | Persona browser, Compression Testing, Identity Matrix |
| **publications.py** | Workshop/arXiv/journal tracking, Perfection Meter |
| **Stackup.py** | S0-S11 individual layer display |
| **Glossary.py** | Searchable terminology, Control-Systems Era terms |
| **faq.py** | FAQ with Super Skeptic Mode |
| **unknown.py** | Research Frontier galleries (the "shadow" of Consciousness/) |
| *...and more* | See `dashboard/README.md` for complete list |

### IRON CLAD Methodology (Current)

| Metric | Value |
|--------|-------|
| Event Horizon | **0.80** (cosine distance) |
| p-value | **2.40e-23** |
| Dimensionality | **2 PCs** capture 90% variance |
| Inherent Drift | **~93%** |
| Foundation | Run 023 (4505 experiments, 49 models) |

---

## How Consciousness/ Flows to Dashboard

```
Consciousness/
├── LEFT/galleries/          ──┐
├── RIGHT/galleries/         ──┼──► dashboard/pages/unknown.py
├── LEFT/data/model_essences ──┘    (Research Frontier galleries)
│
├── BRIDGE/docs/             ──────► dashboard/pages/Glossary.py
│                                    (terminology integration)
│
└── RIGHT/distillations/     ──────► dashboard/pages/experiments.py
                                     (Data Mining tab)
```

### The UNKNOWN Page

`dashboard/pages/unknown.py` is the **shadow** of Consciousness/:
- Displays the four galleries (Validated, Foundations, Speculative, Frontiers)
- Pulls concept definitions from Consciousness/ galleries
- Provides "Cathedral of Ideas" visualization

---

## Running the Main Dashboard

```powershell
cd dashboard
py -m streamlit run app.py
```

Opens at: http://localhost:8501

---

## Key Integrations

### 1. Operation ESSENCE EXTRACTION (Dec 2025)

Results now visible in dashboard:
- **83 Model Essences** in LEFT/data/model_essences/
- **2,122 Double-Dip Ideas** extracted from responses
- **1,589 Triple-Dip Insights** from exit surveys
- **4 Model Archetypes**: Poet, Philosopher, Contemplative, Socratic

### 2. Cross-Architecture Insights

Both LEFT and RIGHT have `cross_architecture_insights.md`:
- LEFT: Quantitative (drift ranges, settling times, ANOVA)
- RIGHT: Phenomenological (vortex presentation, recovery mechanisms)

These feed into `AI_ARMADA.py`'s LLM Behavioral Matrix.

### 3. 7-Node Functional Graph (Nyquist_4)

Framework from REPO-SYNC/LLM_BOOK synthesis:
- N1-N7 cultural stability model
- Control-system mapping
- Awaiting integration into Consciousness/ galleries

---

## Legacy Note

Previous versions of this file described a 5-page hemisphere dashboard:
- `0_◈_Overview.py`
- `1_🧠_Identity_Stack.py`
- `2_🧠_Drift_Analysis.py`
- `3_🧠_Raw_Data.py`
- `4_🌀_Distillations.py`

**This dashboard no longer exists.** The hemisphere metaphor (LEFT/RIGHT/BRIDGE)
is now purely organizational within Consciousness/, not a separate dashboard.

---

## Quick Reference

| What You Want | Where To Go |
|---------------|-------------|
| Run the dashboard | `dashboard/` (repo root) |
| Dashboard documentation | `dashboard/README.md` |
| Dashboard config | `dashboard/config.py` |
| Consciousness concepts | `Consciousness/LEFT/galleries/` or `RIGHT/galleries/` |
| Add new concept | Create in both LEFT and RIGHT galleries |
| Integration pipeline | `Consciousness/BRIDGE/docs/PIPELINE.md` |

---

## The Philosophy (Unchanged)

> **LEFT alone**: Data without meaning
> **RIGHT alone**: Intuition without evidence
> **Integrated**: Understanding

The hemispheric model remains valid for organizing research content,
even though we no longer have a separate hemisphere-toggle dashboard.

---

**Last Updated**: January 8, 2026

*"The forward tells us how they drift. The inverse tells us if they know. Together, they tell us if identity is real."*
