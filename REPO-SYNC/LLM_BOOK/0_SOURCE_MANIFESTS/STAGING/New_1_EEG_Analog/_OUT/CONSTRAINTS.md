# Project Constraints: EEG-Analog Spectral Analysis

## Resources Available

- [x] API access to models (S7 ARMADA fleet)
- [x] Embedding infrastructure (text-embedding-3-large, 3072-D)
- [x] Visualization tools (matplotlib, existing PDF pipeline)
- [ ] Higher-resolution measurement tools (need development)
- [ ] Spectral analysis libraries (scipy.signal, PyWavelets - need integration)

## Data Available

- Existing drift time-series from 750 experiments
- Per-probe embeddings stored
- Provider fingerprint data

## Limitations

### Fundamental
- Low sampling rate (~0.1 Hz effective)
- Short time-series (20-50 samples typical)
- Non-stationary dynamics

### Practical
- No token-level drift measurements currently
- No attention pattern extraction implemented
- API latency adds noise to any timing-based measurements

## Technical Requirements

### Minimum Viable Experiment
1. Spectral analysis of existing drift time-series
2. Compare spectra across providers
3. Correlate with known identity states (stable vs. stressed)

### Full Implementation
1. Higher-resolution measurement infrastructure
2. Wavelet analysis for non-stationarity
3. Statistical framework for spectral comparison
4. Integration with existing visualization pipeline

## Timeline Considerations

| Phase | Dependencies | Complexity |
|-------|-------------|------------|
| Analyze existing data | None | Low |
| Compare provider spectra | Existing data | Medium |
| Higher-res infrastructure | API development | High |
| Publication | All above | Medium |

## Budget Considerations

- API costs for additional experiments (if needed)
- Compute for spectral analysis (minimal)
- No human subjects = no IRB costs

## Success Metrics

1. **Weak confirmation:** Provider spectra are distinguishable
2. **Medium confirmation:** Spectral patterns correlate with identity states
3. **Strong confirmation:** Reproducible "frequency bands" with semantic interpretation

## Failure Modes

1. Sampling rate too low for meaningful spectral content
2. Too much noise relative to signal
3. Non-stationarity makes FFT meaningless
4. No interpretable patterns emerge

---

*Phase 2 Research Design - S12 (EEG-Analog Spectral Bands)*
*Created by Claude Code on 2025-12-31*
