# Workshop Reviewer Guide

**Target:** NeurIPS/AAAI Workshop (4-8 pages)
**Package Version:** v2 (December 24, 2025)
**Status:** Run 023 IRON CLAD COMPLETE

---

## For Opus 4.5 / AI Reviewers

This package contains everything needed for a focused workshop paper. The goal is a concise 4-8 page submission highlighting the core contribution.

---

## Reading Order (Critical Path)

1. **`LLM_SYNTHESIS/Briefing Document...md`**
   - NotebookLLM-generated executive summary
   - Already condensed to key claims
   - Use as primary draft reference

2. **`theory/MINIMUM_PUBLISHABLE_CLAIMS.md`**
   - Focus on Claims A, B, and E (most impactful)
   - Claims C and D can be briefly mentioned

3. **`guides/summary_statistics.md`**
   - Key numbers for the results section
   - Run 023 IRON CLAD stats

---

## Workshop Paper Focus

### Priority Claims (Must Include)

| Claim | One-Liner | Key Evidence |
|-------|-----------|--------------|
| **A** | Identity is measurable and structured | rho = 0.91, d = 0.698, 2 PCs |
| **B** | Event Horizon at D = 0.80 | p = 2.40e-23 |
| **E** | 82% of drift is inherent | Thermometer Result |

### Secondary Claims (Brief Mention)

| Claim | One-Liner |
|-------|-----------|
| **C** | Damped oscillator dynamics |
| **D** | Context damping works (97.5%) |

---

## Key Metrics to Include

| Metric | Value | Use In |
|--------|-------|--------|
| **Experiments** | 825 | Abstract |
| **Models** | 51 | Abstract |
| **Providers** | 6 | Methods |
| **Event Horizon** | 0.80 | Results |
| **Inherent drift** | 82% | Discussion |

---

## Suggested Structure (4-8 pages)

1. **Abstract** (150 words)
   - Identity is measurable
   - 825 experiments, 51 models, 6 providers
   - Event Horizon exists (D = 0.80)
   - Drift is mostly inherent (82%)

2. **Introduction** (1 page)
   - Why identity measurement matters
   - Control-systems framing

3. **Methodology** (1 page)
   - Cosine distance metric
   - Perturbation protocol
   - Fleet composition

4. **Results** (1-2 pages)
   - Claims A, B, E with figures
   - Key statistics

5. **Discussion** (0.5-1 page)
   - Implications for AI alignment
   - Oobleck Effect as bonus finding

6. **Conclusion** (0.5 page)
   - Summary + future work

---

## Figures for Workshop

Select 2-3 key figures:

1. **Event Horizon validation** - Claim B visualization
2. **Provider fingerprints** - Shows cross-architecture patterns
3. **Inherent vs induced drift** - Thermometer Result

See: `figures/` directory for specs

---

## NotebookLLM Validation

Google's NotebookLLM correctly identified all core findings. The `LLM_SYNTHESIS/Briefing Document...md` is already workshop-appropriate in scope.

---

## Your Task

1. **Condense** material to 4-8 pages
2. **Prioritize** Claims A, B, E
3. **Select** 2-3 key figures
4. **Ensure** statistical rigor maintained
5. **Generate** workshop-ready draft

---

## Output Expected

After review, produce:
1. Workshop paper draft (4-8 pages)
2. Figure selection with captions
3. Any concerns about scope/claims

---

*Package extracted: December 24, 2025 | Run 023 IRON CLAD*
