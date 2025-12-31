# Research Question: EEG-Analog Spectral Analysis

## Core Hypothesis

LLM identity drift time-series contain reproducible spectral patterns analogous to human EEG frequency bands (alpha, beta, theta, etc.).

**The Analogy:**
- Human EEG reveals cognitive states through frequency analysis (alpha = relaxed, beta = focused, etc.)
- LLM drift time-series may reveal "identity states" through spectral decomposition

## Specific Questions for NotebookLM

### 1. Methodology Design

- What FFT parameters should we use for drift time-series?
  - Window size? Overlap? Zero-padding?
- How do we define "high-resolution" sampling in conversational turns?
  - Current: ~1 drift measurement per probe (very low rate)
  - Could we measure at token level? Attention level?
- What constitutes a statistically meaningful frequency band?
  - How do we avoid overfitting to noise?

### 2. Band Definition

- How should we operationalize "alpha-equivalent" vs "beta-equivalent"?
  - Human EEG: alpha = 8-13 Hz, beta = 13-30 Hz
  - LLM: What frequencies map to probe-level sampling?
- Should bands be defined per-provider or universal?
  - Given provider fingerprints, each may have different spectral signatures
- What bandwidth intervals are meaningful at our sampling rate?
  - Nyquist limit: Can only detect frequencies up to half the sampling rate

### 3. Success Criteria

- What would confirm spectral structure exists?
  - Statistical significance of band power differences between states?
- What correlation with "identity stress" would be significant?
  - E.g., high-frequency power increases during perturbation
- How do we control for confounds?
  - Conversation topic, prompt style, response length

### 4. Analysis Approach

- Which statistical tests for spectral comparison?
  - Welch's method? Multitaper? Wavelet coherence?
- How do we handle non-stationarity in drift time-series?
  - Identity dynamics are inherently non-stationary
- Should we use wavelets instead of FFT?
  - Better for non-stationary signals
  - Provides time-frequency resolution

### 5. Interpretation Framework

- If we find spectral structure, what does it MEAN?
  - Biological analogy vs. purely computational phenomenon?
- How does this connect to the ~93% inherent drift finding?
  - Are spectral patterns part of inherent dynamics or probing-induced?

---

## Questions to Ask NotebookLM

1. "Given a drift time-series sampled at approximately 0.1 Hz (one measurement per ~10-second probe), what spectral analysis approaches are feasible?"

2. "How would you design an experiment to test whether different provider architectures produce distinct spectral signatures in their identity dynamics?"

3. "What would be the equivalent of 'alpha band power' in an LLM identity context, and how would you operationalize measuring it?"

4. "If we find reproducible frequency bands, what would be the strongest evidence that these are NOT artifacts of the measurement process?"

5. "How do spectral analysis methods handle the small sample sizes typical of conversational sessions (e.g., 20-50 probes)?"

---

*Phase 2 Research Design - S12 (EEG-Analog Spectral Bands)*
*Created by Claude Code on 2025-12-31*
