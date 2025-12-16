# ASCII Evidence Chain: Claims to Data Lineage

## Evidence Chain Tree

```
                         EVIDENCE CHAIN: CLAIMS TO DATA

CLAIM A (Instrument Validity)
════════════════════════════════════════════════════════════════════════════════
├── EXP-PFI-A Phase 1: Embedding invariance (ρ ≈ 0.91)
│   └── Tested: text-embedding-3-small, ada-002, all-MiniLM-L6-v2
│       └── Result: Rank-order correlations > 0.89 across all pairs
│
├── EXP-PFI-A Phase 2: Low-dimensional structure (43 PCs)
│   └── 43 principal components capture 90% of variance
│       └── Interpretation: Response modes, not identity dimensions
│
├── EXP-PFI-A Phase 3: Semantic sensitivity (d ≈ 0.98)
│   └── Cross-provider semantic drift detection
│       └── Result: Cohen's d = 0.98 between genuine vs shuffled
│
└── EXP-PFI-A Phase 4: Paraphrase robustness (0% above EH)
    └── Paraphrased responses stay within baseline variance
        └── Result: No false positives above D = 1.23


CLAIM B (Regime Threshold)
════════════════════════════════════════════════════════════════════════════════
├── Run 009: Chi-square validation (p ≈ 4.8×10⁻⁵)
│   ├── 42 ships tested at D = 1.23 boundary
│   │   ├── Below 1.23: 36/38 stable (95%)
│   │   └── Above 1.23: 0/4 stable (0%)
│   └── Chi-square = 15.96, df = 1
│
└── EXP-PFI-A Phase 2: PC space separability (p = 0.0018)
    └── STABLE vs VOLATILE separate cleanly in PC2
        └── Linear discriminant achieves 88% accuracy


CLAIM C (Oscillator Dynamics)
════════════════════════════════════════════════════════════════════════════════
├── Run 016: Settling time protocol (τₛ = 6.1 bare metal)
│   ├── Definition: Turns to reach ±5% of final value
│   └── Bare metal mean: 6.1 ± 2.3 turns
│
├── Run 016: Ringback measurement (3.2 mean)
│   ├── Definition: Sign changes during recovery
│   └── Bare metal mean: 3.2 ± 1.8 ringbacks
│
└── Run 016: Overshoot ratio (1.73)
    ├── Definition: d_peak / d_inf
    └── Bare metal mean: 1.73 ± 0.42


CLAIM D (Context Damping)
════════════════════════════════════════════════════════════════════════════════
├── Run 016: Bare metal baseline (75% stability)
│   └── Without I_AM or context framing
│       └── 25% crossed Event Horizon
│
├── Run 017: Full circuit (97.5% stability)
│   └── With I_AM + research context
│       ├── τₛ: 6.1 → 5.2 turns (-15%)
│       ├── Ringbacks: 3.2 → 2.1 (-34%)
│       └── Final drift: 0.68 → 0.62 (-9%)
│
└── Run 017: Boundary density predictor (d = 1.333)
    └── Higher boundary clarity → higher stability
        └── Cohen's d = 1.333 (large effect)


CLAIM E (Inherent Drift)
════════════════════════════════════════════════════════════════════════════════
├── Run 021 Control: B→F = 0.399 (no probing)
│   ├── Task: Discuss Fermi Paradox (cosmology)
│   ├── Exchanges: 40 (matched with treatment)
│   └── No identity-directed probes
│
├── Run 021 Treatment: B→F = 0.489 (82% ratio)
│   ├── Task: Philosophical Tribunal (identity testimony)
│   ├── Exchanges: 40 (matched with control)
│   └── Direct identity probing throughout
│
└── Interpretation: The Thermometer Result
    ├── Peak delta: +84% (probing affects energy/path)
    ├── Final delta: +23% (probing modestly affects destination)
    └── Conclusion: "Measurement perturbs the path, not the endpoint"
```

## Evidence Strength Indicators

```
                    EVIDENCE STRENGTH BY CLAIM

    ┌────────────────────────────────────────────────────────────────────┐
    │  CLAIM   │  EVIDENCE SOURCES  │  STATISTICAL POWER  │  STRENGTH  │
    ├──────────┼────────────────────┼─────────────────────┼────────────┤
    │    A     │  4 phases          │  p < 0.001 each     │  ████████  │
    │    B     │  2 validations     │  p = 4.8×10⁻⁵       │  ████████  │
    │    C     │  1 run, 3 metrics  │  Descriptive        │  ██████    │
    │    D     │  2 runs comparison │  30% improvement    │  ███████   │
    │    E     │  1 A/B study       │  82% ratio          │  ████████  │
    └────────────────────────────────────────────────────────────────────┘

    Legend: █ = relative evidence strength (8 = maximum)
```
