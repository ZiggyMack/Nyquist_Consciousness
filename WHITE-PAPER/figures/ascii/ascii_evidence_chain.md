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
├── EXP-PFI-A Phase 2: Low-dimensional structure (2 PCs)
│   └── 2 principal components capture 90% of variance
│       └── Interpretation: Remarkably low-dimensional identity space
│
├── EXP-PFI-A Phase 3: Semantic sensitivity (d ≈ 1.123)
│   └── Cross-provider semantic drift detection
│       └── Result: Cohen's d = 1.123 between genuine vs shuffled
│
└── EXP-PFI-A Phase 4: Paraphrase robustness (0% above EH)
    └── Paraphrased responses stay within baseline variance
        └── Result: No false positives above D = 0.80


CLAIM B (Regime Threshold)
════════════════════════════════════════════════════════════════════════════════
├── Run 023: Chi-square validation (p ≈ 4.8×10⁻⁵)
│   ├── 750 experiments tested at D = 0.80 boundary
│   │   ├── Below 0.80: Stable zone
│   │   └── Above 0.80: Volatile zone
│   └── Perturbation validation: p = 2.40×10⁻²³
│
└── EXP-PFI-A Phase 2: PC space separability (p = 0.0018)
    └── STABLE vs VOLATILE separate cleanly in PC2
        └── Linear discriminant achieves 88% accuracy


CLAIM C (Oscillator Dynamics)
════════════════════════════════════════════════════════════════════════════════
├── Run 023: Settling time protocol (τₛ ≈ 9.9-10.2)
│   ├── Definition: Turns to reach ±5% of final value
│   └── Full circuit mean: τₛ ≈ 9.9-10.2 turns
│
├── Run 023: Ringback measurement
│   ├── Definition: Sign changes during recovery
│   └── Measured across 5 providers, 25 models
│
└── Run 023: Recovery dynamics
    ├── Definition: Time-series settling behavior
    └── Waterfall visualization confirms convergence


CLAIM D (Context Damping)
════════════════════════════════════════════════════════════════════════════════
├── Run 023: Context damping validation
│   └── With I_AM + research context
│       └── 97.5% stability achieved
│
├── Run 023: Full circuit metrics
│   └── With I_AM + research context
│       ├── τₛ ≈ 9.9-10.2 turns (settling time)
│       └── Consistent across 5 providers
│
└── Run 023: Event Horizon validation
    └── D = 0.80 cosine distance threshold
        └── p = 2.40×10⁻²³ perturbation validation


CLAIM E (Inherent Drift - The 92% Finding)
════════════════════════════════════════════════════════════════════════════════
├── Run 023: Control vs Treatment analysis
│   ├── Control: Neutral task (no identity probing)
│   ├── Treatment: Identity-directed probes
│   └── Matched across 5 providers, 25 models
│
├── Run 023: The Thermometer Result (92% inherent)
│   ├── 92% of drift is INHERENT (happens without probing)
│   ├── Only 8% attributable to measurement
│   └── 750 experiments validate finding
│
└── Interpretation: The Thermometer Analogy
    ├── Measurement reveals drift, doesn't create it
    ├── Like a thermometer measuring temperature
    └── Conclusion: "Measurement perturbs the path, not the endpoint"
```

## Evidence Strength Indicators

```
                    EVIDENCE STRENGTH BY CLAIM (COSINE METHODOLOGY)

    ┌────────────────────────────────────────────────────────────────────┐
    │  CLAIM   │  EVIDENCE SOURCES  │  STATISTICAL POWER  │  STRENGTH  │
    ├──────────┼────────────────────┼─────────────────────┼────────────┤
    │    A     │  4 phases          │  p < 0.001 each     │  ████████  │
    │    B     │  750 experiments   │  p = 2.40×10⁻²³     │  ████████  │
    │    C     │  5 providers       │  τₛ ≈ 9.9-10.2      │  ███████   │
    │    D     │  25 models         │  97.5% stability    │  ████████  │
    │    E     │  Control/Treatment │  92% inherent       │  ████████  │
    └────────────────────────────────────────────────────────────────────┘

    Legend: █ = relative evidence strength (8 = maximum)
    Note: All values use COSINE distance methodology (D = 0.80 Event Horizon)
```
