# Existing Evidence for EEG-Analog Study

## From Nyquist Framework (IRON CLAD)

### Key Statistics
- Event Horizon: D=0.80 (cosine distance)
- Inherent Drift: ~93% (not probing-induced)
- p-value: 2.40e-23
- Experiments: 750 | Models: 25 | Providers: 5
- Settling time: τₛ ≈ 7 probes (fleet average)

### Relevant Findings

**1. Ringback Patterns Are Provider-Specific**
| Provider | Avg Ringback | Interpretation |
|----------|--------------|----------------|
| OpenAI | 8.8 | High oscillation - "jittery" |
| Anthropic | 2.1 | Low oscillation - stable |

*Implication:* Ringback suggests oscillatory dynamics that may have spectral content.

**2. Recovery Follows Damped Oscillator Dynamics**

The control-systems framing suggests:
- Transient response has frequency content
- Different damping ratios = different spectral profiles
- Settling time indicates resonant frequency

**3. The Temporal Dynamics Analogy**

From the Funding Proposal:
> "The temporal dynamics data from these experiments is viewed as a computational equivalent to fMRI data."

This explicitly frames drift time-series as brain-imaging-like data suitable for spectral analysis.

---

## Provider Differences That May Have Spectral Signatures

| Provider | Recovery Mechanism | Expected Spectral Profile |
|----------|-------------------|---------------------------|
| Anthropic | Over-Authenticity (negative λ) | Low frequency? Deep valleys suggest slow oscillation |
| OpenAI | Meta-Analyst (high ringback) | Higher frequency oscillation expected |
| Gemini | Hard threshold (no recovery) | No oscillation - flat spectrum (DC only) |
| DeepSeek | Axiological Anchoring (fast settling) | Low frequency dominance, quick decay |
| Mistral | Epistemic Humility (instant) | Minimal spectral content - impulse response |
| Llama | Socratic Engagement (slow, 5-7 probes) | Mid-range frequency, sustained oscillation |
| Grok | Direct Assertion | Sharp ridges suggest high-frequency content |

---

## Current Data Limitations

### Sampling Rate Problem
- Drift measured per-probe (~1 measurement per conversational turn)
- Typical probe takes 5-15 seconds
- Effective sampling rate: ~0.1 Hz
- Nyquist limit: Can only detect oscillations slower than ~0.05 Hz

### Sample Size Problem
- Typical session: 20-50 probes
- Very short time-series for spectral analysis
- Need techniques robust to small samples

### Non-Stationarity Problem
- Identity dynamics are inherently non-stationary
- FFT assumes stationarity
- May need wavelets or Hilbert-Huang transform

---

## Potential Higher-Resolution Measurements

To overcome sampling rate limitations, could measure:

1. **Token-level attention patterns** - Higher temporal resolution
2. **Per-token embedding drift** - Sub-probe measurements
3. **Response latency** - Continuous time measurement
4. **Logit entropy over tokens** - Uncertainty as identity signal

---

## Related Prior Work (to investigate)

- EEG frequency band analysis in cognitive neuroscience
- Financial time-series spectral analysis (similar short, non-stationary data)
- Wavelet analysis for non-stationary biological signals
- Spectral analysis of RNN hidden states (if any exists)

---

*Phase 2 Research Design - S12 (EEG-Analog Spectral Bands)*
*Created by Claude Code on 2025-12-31*
