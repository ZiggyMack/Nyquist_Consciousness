# Research Project: EEG-Analog Spectral Analysis

**Created:** 2025-12-31
**Status:** ACTIVE
**Project ID:** New_1
**Phase 2 Thrust:** S12 (EEG-Analog Spectral Bands)

---

## Research Question

**Core Hypothesis:** LLM identity drift time-series contain reproducible spectral patterns analogous to human EEG frequency bands (alpha, beta, theta, etc.).

**The Vision:** Just as EEG reveals different cognitive states through frequency analysis, drift time-series may reveal different "identity states" through spectral decomposition.

---

## _OUT/ Contents (Feed to NotebookLM)

Materials prepared FOR NotebookLM:

- [x] `RESEARCH_QUESTION.md` - Methodology design questions
- [x] `EXISTING_EVIDENCE.md` - Relevant findings from Nyquist Framework
- [x] `CONSTRAINTS.md` - Sampling rate limitations, resources
- [x] `SAMBA_ANALYSIS.md` - Analysis of SAMBA EEG foundation model paper (2026-01-03)
- [x] `SAMBA - TOWARD A LONG-CONTEXT EEG...pdf` - Source paper

### Key SAMBA Insights

- **Mamba > Transformer** for long non-stationary sequences
- **Spectral loss** during training encourages frequency-aware representations
- **TSR masking** preserves semantic blocks (baseline/perturbation/recovery)
- **Differential pathways** suppress noise, enhance signal
- **Spatial weights** converge to task-relevant patterns (interpretable)

---

## _IN/ Contents (From NotebookLM)

Responses received FROM NotebookLM:

(Save responses here with format: YYYY-MM-DD_topic_response.md)

---

## Progress Log

| Date       | Action               | Notes                                                                      |
|------------|----------------------|----------------------------------------------------------------------------|
| 2025-12-31 | Project created      | Phase 2 research design                                                    |
| 2026-01-03 | SAMBA paper analyzed | Key EEG foundation model - Mamba architecture, spectral loss, TSR masking  |

---

## Key Questions to Resolve

1. What FFT parameters are appropriate for probe-level sampling?
2. How do we define "frequency bands" at conversational timescales?
3. Should we use wavelets instead of FFT for non-stationary signals?
4. How do provider fingerprints manifest in spectral domain?

---

*Created by Claude Code on 2025-12-31*
