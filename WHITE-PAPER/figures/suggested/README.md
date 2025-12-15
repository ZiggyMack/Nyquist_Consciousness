# Suggested Supplementary Visualizations

These visualizations from the S7 ARMADA experimental runs provide empirical evidence supporting the main publication figures. They are **not required** for the core paper but offer valuable supplementary material.

## Directory Structure

```text
suggested/
├── README.md           # This file
├── png/                # PNG format (300 DPI, ready for web/preview)
│   ├── S7_recovery_trajectories.png
│   ├── S7_pillar_effectiveness.png
│   ├── S7_context_damping_effect.png
│   ├── S7_summary_dashboard.png
│   ├── S7_settling_time_distribution.png
│   ├── S7_ringback_vs_settling.png
│   ├── S7_discriminant_analysis.png
│   └── S7_stability_scatter.png
└── pdf/                # PDF format (vector-quality for print)
    └── [same 8 files as .pdf]
```

## Overview

| File | Source Run | Supports Claim | Description |
|------|------------|----------------|-------------|
| `S7_recovery_trajectories` | Run 017 | D (Context Damping) | Individual trajectory curves showing drift-then-recover patterns |
| `S7_pillar_effectiveness` | Run 017 | D (Context Damping) | Ranking of stabilization techniques (I_AM most effective) |
| `S7_context_damping_effect` | Run 017 | D (Context Damping) | Before/after comparison of context damping intervention |
| `S7_summary_dashboard` | Run 017 | All | Comprehensive dashboard with multiple metrics |
| `S7_settling_time_distribution` | Run 016 | C (Oscillator) | Distribution of settling times across experiments |
| `S7_ringback_vs_settling` | Run 016 | C (Oscillator) | Relationship between ringback count and settling time |
| `S7_discriminant_analysis` | Run 015 | B (Threshold) | Linear discriminant analysis separating stable/unstable states |
| `S7_stability_scatter` | Run 015 | B (Threshold) | 2D scatter showing drift vs stability relationship |

## Publication Use

### Workshop Paper (4-8 pages)

- Consider: `S7_summary_dashboard` as a single supplementary figure
- Use `pdf/` for print, `png/` for digital

### arXiv Preprint (25-35 pages)

- Include all in supplementary materials
- Reference in main text as "See Supplementary Figure S1-S8"
- Use `pdf/` versions for LaTeX inclusion

### Journal Submission (~10k words)

- Full integration with extended figure captions
- Link to S7 ARMADA methodology section
- Use `pdf/` for production-quality figures

## Source Data

All visualizations generated from:

- `experiments/temporal_stability/S7_ARMADA/`
- Runs 015-017 (Stability Criteria, Settling Time, Context Damping)
