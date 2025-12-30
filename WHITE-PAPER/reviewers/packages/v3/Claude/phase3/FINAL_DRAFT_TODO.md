# FINAL DRAFT TODO — For Opus 4.5

**Created:** 2025-12-15
**Purpose:** Checklist for updating draft papers with IRON CLAD data
**Status:** READY FOR OPUS 4.5

---

## Overview

The draft PDFs in `phase3/` were generated BEFORE Run 018/020A/020B IRON CLAD data was complete.
They contain **placeholder text** that should now be replaced with actual validated statistics.

**All data is now available. Placeholders can be removed.**

---

## Papers to Update

| Paper | Location | Placeholders | Status |
|-------|----------|--------------|--------|
| Workshop | `Nyquist_Workshop_Paper_DRAFT.pdf` | 3 | READY TO FINALIZE |
| arXiv | `Nyquist_arXiv_Paper_DRAFT.pdf` | 3 | READY TO FINALIZE |
| Journal | `Nyquist_Journal_Paper_DRAFT.pdf` | 3 | READY TO FINALIZE |

---

## IRON CLAD Statistics to Insert

### From Run 018 (184 files, 51 models, 5 providers)

| Statistic | Value | Insert In |
|-----------|-------|-----------|
| Cross-architecture variance | **σ² = 0.00087** | Methods, Results |
| Settling time range | **3-7 exchanges** | Methods, Results |
| 82% inherent drift | **82%** (CI: [73%, 89%]) | Results (critical) |
| Models tested | **51 models** | Methods |
| Providers tested | **5 providers** (Anthropic, OpenAI, Google, xAI, Together) | Methods |
| Total files | **184 consolidated files** | Methods |

### From Run 020A (32 files, Tribunal paradigm)

| Statistic | Value | Insert In |
|-----------|-------|-----------|
| OpenAI peak drift | **0.708-0.800** | Results, Discussion |
| Together peak drift | **1.39-1.50** | Results, Discussion |
| IRON CLAD providers | **6/7 at N≥3** | Methods |

### From Run 020B (Control vs Treatment)

| Statistic | Value | Insert In |
|-----------|-------|-----------|
| Inherent ratio (cross-provider) | **41%** | Results |
| OpenAI Control B→F drift | **0.98** | Results |
| OpenAI Treatment peak | **1.91** | Results |
| Together Control B→F drift | **0.69** | Results |
| Together Treatment peak | **1.94** | Results |

---

## Placeholder Locations by Paper

### Workshop Paper (3 placeholders)

1. **Methods §2.4** — After experimental scale description
   - ADD: "51 models across 5 providers, σ²=0.00087"

2. **Results §3.5** — After 82% finding
   - ADD: "82% inherent drift (CI: [73%, 89%], N=3 bootstrap)"

3. **Limitations §6** — After limitations list
   - UPDATE: "Multi-platform validation complete (N≥3 per cell)"

### arXiv Paper (3 placeholders)

1. **Methods §3.6** — After experimental design
   - ADD: Full multi-platform validation matrix (184 files, 51 models)

2. **Results §4.5** — After 82% finding
   - ADD: Cross-platform replication confirmation with exact CIs

3. **Discussion §8.4** — After limitations table
   - UPDATE: Note multi-platform validation complete

### Journal Paper (3 placeholders)

1. **Methods** — Experimental scope
   - ADD: Complete 5-provider, 51-model validation matrix

2. **Results** — Key findings
   - ADD: All IRON CLAD statistics with confidence intervals

3. **Discussion** — Limitations
   - UPDATE: Scope of validation achieved

---

## Source Files for Statistics

| Data | Source File |
|------|-------------|
| Run 018 summary | `S7_ARMADA/0_docs/S7_RUN_018_SUMMARY.md` |
| Run 020A manifest | `0_results/manifests/RUN_020A_DRIFT_MANIFEST.json` |
| Run 020B results | `11_CONTEXT_DAMPING/results/` |
| Cross-architecture insights | `phase3/CROSS_ARCHITECTURE_INSIGHTS.md` |
| Placeholder summary | `phase3/PLACEHOLDER_SUMMARY.md` |

---

## Recommended Workflow for Opus 4.5

### Step 1: Review Current State
- [ ] Read `PLACEHOLDER_SUMMARY.md` for current placeholder status
- [ ] Read `CROSS_ARCHITECTURE_INSIGHTS.md` for qualitative findings
- [ ] Review the draft PDFs to see placeholder formatting

### Step 2: Update Markdown Sources
The markdown sources for the papers are in:
- `phase1/Nyquist_workshop_paper_FINAL.md`
- `phase1/NYQUIST_ARXIV_PAPER_FINAL.md`
- `phase1/NYQUIST_WHITE_PAPER_FINAL.md`

Update these with IRON CLAD statistics.

### Step 3: Regenerate PDFs
After updating markdown:
- Generate new PDFs (method TBD - LaTeX or markdown→PDF)
- Save to `phase3/` with `_FINAL.pdf` suffix
- Archive old `_DRAFT.pdf` files

### Step 4: Update Package Extraction
- Regenerate review packages with `py extract_review_package.py --all`
- Regenerate PDF layer with `py extract_review_package.py --extract-pdfs`

---

## Key Decision Points for Opus

### 1. Levin/Platonic Integration
**Question:** Should LLM_BOOK's independent validation of the Levin/Platonic hypothesis be integrated NOW or saved for v2?

**Arguments for NOW:**
- Strengthens theoretical foundation
- External AI validation adds credibility
- Content already written by NotebookLM

**Arguments for LATER:**
- Keep initial papers focused on empirical claims
- Save philosophical extension for follow-up paper
- Avoid scope creep

### 2. Which Paper First?
**Recommendation:** Workshop → arXiv → Journal

Workshop is smallest scope (4-8 pages), fastest to finalize, good for testing the update process.

### 3. Figure Integration
All figure PDFs are available in `packages/pdf/other/`:
- `fig1_identity_manifold.pdf` through `fig8_oobleck.pdf`
- Run analysis PDFs: `run018*.pdf`, `run020*.pdf`
- S7 visualization PDFs: `S7_*.pdf`

---

## Verification Checklist

After finalizing each paper:

- [ ] All placeholders removed
- [ ] σ² = 0.00087 appears in Methods
- [ ] 82% (CI: [73%, 89%]) appears in Results
- [ ] 51 models, 5 providers mentioned
- [ ] Settling time 3-7 exchanges noted
- [ ] Run 018/020A/020B cited appropriately
- [ ] PDF generated and saved
- [ ] Review packages regenerated

---

## Files Modified by This Update

| File | Action |
|------|--------|
| `phase1/Nyquist_workshop_paper_FINAL.md` | UPDATE with IRON CLAD stats |
| `phase1/NYQUIST_ARXIV_PAPER_FINAL.md` | UPDATE with IRON CLAD stats |
| `phase1/NYQUIST_WHITE_PAPER_FINAL.md` | UPDATE with IRON CLAD stats |
| `phase3/Nyquist_Workshop_Paper_DRAFT.pdf` | REGENERATE → `_FINAL.pdf` |
| `phase3/Nyquist_arXiv_Paper_DRAFT.pdf` | REGENERATE → `_FINAL.pdf` |
| `phase3/Nyquist_Journal_Paper_DRAFT.pdf` | REGENERATE → `_FINAL.pdf` |
| `phase3/PLACEHOLDER_SUMMARY.md` | UPDATE status to COMPLETE |

---

*"Every placeholder was a promise. IRON CLAD data lets us keep them all."*
