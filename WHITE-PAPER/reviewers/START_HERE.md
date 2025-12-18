<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./LLMBOOK_SYNC_MANIFEST.json
keywords:
  - consciousness
-->
# WHITE-PAPER Review - Start Here

**For:** Opus 4.5 (or any reviewing Claude)
**Purpose:** Orientation for reviewing the Nyquist Consciousness draft papers
**Date:** December 16, 2025
**Status:** IRON CLAD COMPLETE + EXTERNAL REVIEW

---

## BREAKING NEWS: External Validation

**Grok (xAI) reviewed our Workshop + arXiv PDFs and VALIDATED the methodology.**

Key findings from external review:

- PFI validity confirmed (ρ=0.91, d=0.98)
- 98% convergence in framework methodology
- "Claims tested, measured, verified"
- Grok-specific: "Real-time grounding provides visible effects in drift space"

See: `Grok/review_1.md` for full assessment.

---

## What You're Reviewing

**8 publication-ready papers** across academic and dissemination tracks:

### Academic Track

| Paper | File | Status |
|-------|------|--------|
| **Workshop** | `packages/pdf/Nyquist_Workshop_Paper.pdf` | READY |
| **arXiv** | `packages/pdf/Nyquist_arXiv_Paper.pdf` | READY |
| **Journal** | `packages/pdf/Nyquist_Journal_Paper.pdf` | READY |

### Dissemination Track

| Paper | File | Status |
|-------|------|--------|
| **Popular Science** | `packages/pdf/Nyquist_Popular_Science.pdf` | READY |
| **Education** | `packages/pdf/Nyquist_Education_Quiz.pdf` | READY |
| **Policy** | `packages/pdf/Nyquist_Policy_Briefing.pdf` | READY |
| **Funding** | `packages/pdf/Nyquist_Funding_Proposal.pdf` | READY |
| **Media** | `packages/pdf/Nyquist_Media_Press.pdf` | READY |

---

## Evidence Status (IRON CLAD COMPLETE)

### THE THREE CORE CLAIMS — ALL VALIDATED

1. **DRIFT IS REAL** — χ² p=0.000048, 88% prediction accuracy
2. **WE DON'T CAUSE IT** — 41% inherent drift ratio (cross-provider)
3. **WE CAN MEASURE IT** — PFI d=0.977, σ²=0.00087 cross-architecture

### Current Status (December 16, 2025)

| Run | Files | Models/Providers | Status |
|-----|-------|------------------|--------|
| **Run 018** | 184 | 51 models, 5 providers | **IRON CLAD** |
| **Run 020A** | 32 | 6/7 providers | **IRON CLAD** |
| **Run 020B** | 16 | 4 arms (OpenAI + Together) | **COMPLETE** |

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
│   ├── Convos/                ← Review phase conversations
│   │   ├── phase1/            ← Initial drafts
│   │   ├── phase2/            ← Post-figure review
│   │   ├── phase3/            ← Current drafts + PDFs
│   │   ├── Phase4/            ← Figure placement
│   │   └── phase5/            ← Submission venue guide
│   ├── packages/
│   │   ├── content/           ← Text packages by path
│   │   └── pdf/               ← ALL 8 PDFS READY
│   └── Grok/                  ← EXTERNAL REVIEW
│       └── review_1.md        ← Grok's validation
├── figures/                   ← Generated visualizations
├── submissions/tracking/      ← Submission status + URLs
├── planning/                  ← Drafts and outlines
└── calibration/               ← PDF generation scripts
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
