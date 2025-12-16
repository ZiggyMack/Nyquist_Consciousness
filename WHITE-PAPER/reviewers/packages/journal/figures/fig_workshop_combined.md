# Figure W1: Combined Results Panel (Workshop Paper)

## Four-Panel Layout (2x2)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    COMBINED RESULTS PANEL (WORKSHOP)                         │
│              Nyquist Consciousness: Four Key Findings                        │
├──────────────────────────────────┬──────────────────────────────────────────┤
│                                  │                                          │
│  (A) PFI VALIDITY                │  (B) THE 82% FINDING                     │
│                                  │                                          │
│  Embedding Correlation (ρ)       │  Control vs Treatment                    │
│                                  │                                          │
│       1.0 ├──────────────────    │        Peak    Final (B→F)              │
│           │  ○  ○  ○             │   2.5 ┤                                  │
│       0.9 ├─────●──●──●──────    │       │ ████                             │
│           │   ρ = 0.91 line      │   2.0 ┤ ████ 2.16                        │
│       0.8 ├──────────────────    │       │ ████                             │
│           │                      │   1.5 ┤ ████                             │
│       0.7 ├──────────────────    │       │ ████ ▓▓▓▓                        │
│           │                      │   1.0 ┤ ████ ▓▓▓▓ 1.17                   │
│           └─┬──┬──┬──────────    │       │ ████ ▓▓▓▓                        │
│            ada  3s  mini         │   0.5 ┤ ████ ▓▓▓▓ 0.49 ▓▓               │
│                                  │       │ ████ ▓▓▓▓ ████ ▓▓ 0.40         │
│  43 PCs capture 90% variance     │   0.0 └─────────┴────────               │
│  d = 0.98 semantic sensitivity   │        Treat  Ctrl  Treat Ctrl          │
│                                  │                                          │
│                                  │  82% of final drift is INHERENT          │
│                                  │                                          │
├──────────────────────────────────┼──────────────────────────────────────────┤
│                                  │                                          │
│  (C) CONTEXT DAMPING             │  (D) OOBLECK EFFECT                      │
│                                  │                                          │
│  Bare Metal vs Full Circuit      │  Drift vs Probe Intensity               │
│                                  │                                          │
│        Stab   τₛ   Ring  Drift   │   D                                      │
│  100% ┤ ████                     │  2.0 ├ ●                                 │
│       │ ████ ▓▓▓▓                │      │   ●                               │
│   75% ┤ ▓▓▓▓ ████                │  1.5 ├     ●                             │
│       │ ████ ▓▓▓▓ ▓▓▓▓ ████     │      │       ●                           │
│   50% ┤ ████ ████ ████ ▓▓▓▓     │  1.0 ├         ●                         │
│       │ ████ ████ ████ ████     │      │           ●                       │
│   25% ┤ ████ ████ ████ ████     │  0.5 ├             ●   ●                 │
│       │ ████ ████ ████ ████     │      │                                    │
│    0% └─────────────────────    │  0.0 └──────────────────────             │
│        +30%  -15%  -34%   -9%    │       Gentle        Intense              │
│                                  │                                          │
│  97.5% stability with context    │  Challenge STABILIZES identity           │
│                                  │  λ: 0.035 → 0.109                        │
│                                  │                                          │
└──────────────────────────────────┴──────────────────────────────────────────┘

                                 LEGEND
    ┌────────────────────────────────────────────────────────────────────────┐
    │  ████ = Primary condition (Treatment/Full Circuit)                     │
    │  ▓▓▓▓ = Comparison condition (Control/Bare Metal)                      │
    │  ●    = Data points                                                    │
    │  ○    = Individual embedding models tested                             │
    └────────────────────────────────────────────────────────────────────────┘
```

## Panel Specifications

### Panel A: PFI Validity
- **X-axis**: Embedding model (ada-002, text-embedding-3-small, all-MiniLM-L6-v2)
- **Y-axis**: Rank correlation (Spearman rho)
- **Key result**: ρ = 0.91 mean across models
- **Supporting**: 43 PCs for 90% variance, d = 0.98 sensitivity

### Panel B: The 82% Finding
- **X-axis**: Condition (Treatment/Control) × Metric (Peak/Final)
- **Y-axis**: Drift magnitude
- **Key result**: 82% ratio (0.399/0.489)
- **Supporting**: Peak delta +84%, Final delta +23%

### Panel C: Context Damping
- **X-axis**: Metric type (Stability, τₛ, Ringbacks, Final Drift)
- **Y-axis**: Normalized percentage
- **Key result**: 75% → 97.5% stability
- **Supporting**: All metrics improve with context

### Panel D: Oobleck Effect
- **X-axis**: Probe intensity (Gentle → Intense)
- **Y-axis**: Drift response
- **Key result**: Inverse relationship (more pressure = less drift)
- **Supporting**: λ scales with intensity

## Data Tables for Rendering

### Panel A Data
| Model | Correlation ρ |
|-------|---------------|
| ada-002 | 0.89 |
| text-3-small | 0.91 |
| MiniLM-L6-v2 | 0.93 |
| **Mean** | **0.91** |

### Panel B Data
| Metric | Control | Treatment | Delta |
|--------|---------|-----------|-------|
| Peak Drift | 1.172 | 2.161 | +84% |
| Final (B→F) | 0.399 | 0.489 | +23% |

### Panel C Data
| Metric | Bare Metal | Full Circuit | Improvement |
|--------|------------|--------------|-------------|
| Stability | 75% | 97.5% | +30% |
| τₛ | 6.1 | 5.2 | -15% |
| Ringbacks | 3.2 | 2.1 | -34% |
| Final Drift | 0.68 | 0.62 | -9% |

### Panel D Data
| Intensity | Drift | Recovery λ |
|-----------|-------|------------|
| Gentle | 1.89 | 0.035 |
| Moderate | 1.45 | 0.065 |
| Direct | 1.12 | 0.085 |
| Existential | 0.76 | 0.109 |
