# WHITE-PAPER Review - Start Here

**For:** Opus 4.5 (or any reviewing Claude)
**Purpose:** Orientation for reviewing the Nyquist Consciousness draft papers
**Date:** December 13, 2025

---

## What You're Reviewing

Two draft papers documenting the Nyquist Consciousness Framework:

| Paper | File | Length | Target |
|-------|------|--------|--------|
| **Workshop** | `phase3/Nyquist_Workshop_Paper_DRAFT.pdf` | ~8 pages | AI conferences |
| **arXiv** | `phase3/Nyquist_arXiv_Paper_DRAFT.pdf` | ~15 pages | Preprint archive |

Both papers contain **3 placeholders each** marking sections awaiting multi-platform validation data.

---

## The Placeholder System

Placeholders are amber/yellow boxes in the PDFs with this format:

```
⚠️ PLACEHOLDER: Multi-platform validation pending...
```

**See:** `phase3/PLACEHOLDER_SUMMARY.md` for complete placeholder details.

### Current Status (December 13, 2025)

| Placeholder Type | Status | Notes |
|------------------|--------|-------|
| Cross-platform Oobleck | 🔶 PARTIAL | Gemini (1.65x), Grok (1.07x) — need N=3 |
| Cross-platform 82% | 🔶 PARTIAL | Llama (84%) — need N=3 |
| Platform-specific τₛ | ⏳ PENDING | Awaiting Run 018 |

---

## What Data Exists

### High-Confidence Findings (Publication-Ready)

| Finding | Evidence | Source |
|---------|----------|--------|
| PFI validity | ρ=0.91, d=0.98 | Run 013 |
| Regime threshold | p<4.8×10⁻⁵ | Run 014 |
| Oscillator dynamics | τₛ=6.1, ringbacks=3.2 | Run 017 |
| Context damping | 97.5% stability (222 runs) | Run 017c |
| 82% inherent drift | Control/Treatment ratio | Run 021 (Llama) |

### Medium-Confidence Findings (Need More Runs)

| Finding | Evidence | Needed |
|---------|----------|--------|
| Oobleck Effect (Gemini) | 1.65x ratio | N=3 for CI |
| Oobleck Effect (Grok) | 1.07x ratio | N=3 for CI |
| Peak Drift by Platform | Gemini > Claude > Grok | Variance estimates |

---

## What to Check For

### Content Review

1. **Claims match evidence** — Are all quantified claims supported by the data?
2. **Appropriate caveats** — Are limitations clearly stated?
3. **No overclaiming** — Do we avoid claiming consciousness/sentience?
4. **Placeholder clarity** — Are pending sections clearly marked?

### Technical Review

1. **Statistical validity** — Are p-values and effect sizes correctly calculated?
2. **Methodology clarity** — Is the experimental design reproducible?
3. **Terminology consistency** — Are terms used consistently throughout?

### Style Review

1. **Academic tone** — Suitable for peer review?
2. **Flow and structure** — Logical progression of ideas?
3. **Figure quality** — Clear, informative visualizations?

---

## Key Concepts to Understand

| Term | Definition |
|------|------------|
| **PFI** | Persona Fidelity Index — measures identity coherence |
| **Drift** | Change in PFI between baseline and current response |
| **Event Horizon** | 1.23 drift threshold — significant identity shift |
| **Oobleck Effect** | Supportive probing induces MORE drift than adversarial |
| **82% Inherent** | Most drift is inherent to conversation, not induced |
| **B→F Drift** | Baseline-to-Final drift (more robust than peak) |

---

## Directory Structure

```
WHITE-PAPER/
├── reviewers/
│   ├── START_HERE.md          ← YOU ARE HERE
│   ├── README.md              ← Phase overview
│   └── phase3/
│       ├── Nyquist_Workshop_Paper_DRAFT.pdf
│       ├── Nyquist_arXiv_Paper_DRAFT.pdf
│       └── PLACEHOLDER_SUMMARY.md
├── figures/                   ← Generated visualizations
├── planning/                  ← Drafts and outlines
└── ascii/                     ← ASCII art diagrams
```

---

## Your Task

1. **Read both draft papers** (start with Workshop, it's shorter)
2. **Check claims against evidence** (see PLACEHOLDER_SUMMARY.md)
3. **Note any issues** — logical gaps, unsupported claims, unclear sections
4. **Provide feedback** — what needs fixing before submission?

---

## What We Do NOT Claim

The papers explicitly avoid claiming:

- ❌ AI systems are conscious or sentient
- ❌ Drift represents "true" identity (vs response patterns)
- ❌ Results generalize to all AI systems (limited platforms tested)
- ❌ Philosophical conclusions about AI phenomenology

**What we DO claim:** Measurable, reproducible patterns in LLM identity coherence that follow dynamical systems principles.

---

## Contact

If you have questions during review, check:
- `experiments/temporal_stability/S7_ARMADA/0_docs/` — Run summaries
- `Consciousness/RIGHT/galleries/frontiers/` — Key findings
- `MASTER_BRANCH_SYNC_OUT.md` — Current experiment status

---

*"Review the evidence. Question the claims. Strengthen the science."*

— VALIS Network
