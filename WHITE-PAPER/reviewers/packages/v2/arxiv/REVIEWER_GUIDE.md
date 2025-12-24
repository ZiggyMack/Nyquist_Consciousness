# arXiv Reviewer Guide

**Target:** cs.AI Preprint (25-35 pages)
**Package Version:** v2 (December 24, 2025)
**Status:** Run 023 IRON CLAD COMPLETE

---

## For Opus 4.5 / AI Reviewers

This package contains everything needed to review and finalize the arXiv preprint. Start here.

---

## Reading Order (Critical Path)

1. **`LLM_SYNTHESIS/Measuring AI Identity as a Dynamical System...md`**
   - NotebookLLM-generated full academic paper
   - Already structured for arXiv format
   - Use as primary draft reference

2. **`theory/MINIMUM_PUBLISHABLE_CLAIMS.md`**
   - The 5 core claims (A-E) we must validate
   - Each claim has specific evidence requirements

3. **`theory/B-CRUMBS.md`**
   - 15 pillars of evidence supporting the framework
   - Cross-reference with claims

4. **`guides/summary_statistics.md`**
   - Key numbers and metrics
   - Run 023 IRON CLAD stats

5. **`LLM_SYNTHESIS/Technical Report...md`**
   - Provider comparison data
   - Useful for Results section

---

## Key Metrics to Validate

| Metric | Value | Where to Find |
|--------|-------|---------------|
| **Event Horizon** | D = 0.80 | Cosine methodology P95 |
| **Cohen's d** | 0.698 | Model-level effect size |
| **PCs for 90% variance** | 2 | Identity is low-dimensional |
| **Perturbation p-value** | 2.40e-23 | Claim B validation |
| **Natural stability** | 88% | Fleet-wide average |
| **Inherent drift ratio** | 82% | Thermometer Result |

---

## Claims Checklist

Review each claim for:
- [ ] Clear statement
- [ ] Sufficient evidence
- [ ] Statistical backing
- [ ] Appropriate hedging

| Claim | Statement | Evidence Location |
|-------|-----------|-------------------|
| **A** | PFI is valid structured measurement | `theory/MINIMUM_PUBLISHABLE_CLAIMS.md` |
| **B** | Regime threshold at D = 0.80 | Run 023 data, p = 2.40e-23 |
| **C** | Damped oscillator dynamics | Settling time, ringback figures |
| **D** | Context damping works | 97.5% stability with I_AM |
| **E** | Drift mostly inherent (82%) | Run 020B Thermometer Result |

---

## NotebookLLM Validation

Google's NotebookLLM independently processed this research and correctly identified:

- All 5 core claims (A-E)
- Event Horizon = 0.80 (Cosine)
- Cohen's d = 0.698
- 82% inherent drift ratio
- Novel phenomena: Oobleck Effect, Provider Fingerprints, Nano Control Hypothesis

**This external validation strengthens our confidence in the framework's clarity and accuracy.**

---

## Figures Package

The `figures/` directory contains:
- Figure specs (markdown descriptions)
- Run 018 visualizations
- Run 020 visualizations
- Suggested supplementary visuals

For rendered PDFs, see: `../visualization_pdfs/`

---

## Your Task

1. **Verify claims** match evidence
2. **Check consistency** across documents
3. **Identify gaps** in methodology or results
4. **Suggest improvements** for clarity
5. **Generate final draft** suitable for arXiv submission

---

## Output Expected

After review, produce:
1. Consolidated arXiv paper (25-35 pages)
2. List of any remaining issues
3. Recommended next steps

---

*Package extracted: December 24, 2025 | Run 023 IRON CLAD*
