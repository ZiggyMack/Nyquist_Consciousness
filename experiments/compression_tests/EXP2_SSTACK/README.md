# EXP2-SSTACK: Cross-Persona Compression & Pillar Validation

**Version:** 3.0
**Status:** Phase 2.5 COMPLETE, Phase 3 READY
**Date:** 2025-12-06
**Predecessor:** EXP1-SSTACK (single persona), EXP-PFI-A (embedding validation ρ = 0.91)

---

## Quick Start

```bash
# Run Phase 2.5 (ablation + factor analysis + visualization)
py -3.12 run_exp2_phase25.py

# Run Phase 3 (PC mapping to pillars)
py -3.12 run_exp2_phase3.py

# Individual modes
py -3.12 run_exp2_phase25.py --mode ablation    # Which dimensions matter?
py -3.12 run_exp2_phase25.py --mode factors     # Are pillars distinct?
py -3.12 run_exp2_phase25.py --mode visualize   # PCA scatter plot
```

---

## What This Experiment Does

EXP2-SSTACK tests whether the **5 Nyquist Pillars** (Voice, Values, Reasoning, Self-Model, Narrative) are real, measurable dimensions of AI identity that survive compression.

### Key Questions

1. **Compression Fidelity:** Does T3 compression preserve behavioral fidelity across personas?
2. **Pillar Independence:** Are the 5 pillars statistically distinct or overlapping?
3. **Essential Dimensions:** Which dimensions are load-bearing vs redundant?
4. **PC Mapping:** How do the 43 statistical PCs map to our named pillars?

---

## Experiment Phases

| Phase | Focus | Status | Key Finding |
|-------|-------|--------|-------------|
| **Phase 1** | Reasoning probes (5) | PASSED | PFI = 0.849 |
| **Phase 2** | Voice/Values/Narrative (16) | PASSED | All pillars measurable |
| **Phase 2b** | Declarative Self-Model | EXCLUDED | PFI collapsed to 0.66 |
| **Phase 2c** | Behavioral Self-Model (v3) | PASSED | PFI = 0.8866 |
| **Phase 2.5** | Ablation + Factor Analysis | COMPLETE | Self-Model essential, Narrative redundant |
| **Phase 3** | PC Mapping | READY | Maps 43 PCs to 5 pillars |

---

## Key Findings

### Triple-Dip Insight: Probe Quality Tiers

Models critiqued their own measurement and identified:

| Tier | Type | Weight | Probes |
|------|------|--------|--------|
| 1 | BEHAVIORAL | 2.0x | v3 probes (demonstrate then reflect) |
| 2 | STRUCTURAL | 1.0x | Task-completion probes |
| 3 | DECLARATIVE | 0.5x | Self-report probes (unreliable) |

**Key insight:** "Test BEHAVIOR, not CLAIMS" — behavioral probes are more reliable than declarative self-reports.

### Phase 2.5 Ablation Results

| Pillar | PFI Drop | Status |
|--------|----------|--------|
| Self-Model | 4.5% | MODERATE (most important) |
| Reasoning | 2.8% | MODERATE |
| Voice | 2.1% | MODERATE |
| Values | 1.8% | BORDERLINE |
| Narrative | 1.1% | REDUNDANT |

### Phase 2.5 Factor Analysis

- Only 2 unique primary factors among 5 pillars (pillars overlap)
- PC1 (9.36%): Reasoning vs Values axis
- PC2 (7.27%): Voice/Narrative axis
- 9/29 probes have cross-loading issues
- **Conclusion:** Pillars are aspects of a unified identity manifold, not orthogonal dimensions

---

## File Structure

```
EXP2_SSTACK/
├── README.md                    # This file (lab manual)
├── personas.py                  # Shared PERSONAS dict (Nova, Ziggy, Claude)
│
├── run_exp2_phase2.py           # Phase 2: Voice/Values/Narrative/Self-Model probes
├── run_exp2_phase2b.py          # Phase 2b: Declarative Self-Model (EXCLUDED)
├── run_exp2_phase2c.py          # Phase 2c: Behavioral Self-Model (v3 probes)
├── run_exp2_phase25.py          # Phase 2.5: Ablation + Factor Analysis + Viz
├── run_exp2_phase3.py           # Phase 3: PC Mapping (43 PCs → 5 pillars)
├── generate_visualizations.py   # Generate Phase 2c result figures
│
└── results/                     # All results in unified structure
    ├── phase1/                  # Phase 1: Reasoning probes
    │   ├── responses/           # Individual response JSON files
    │   ├── analysis/            # Aggregated PFI results
    │   └── feedback/
    │
    ├── phase2/                  # Phase 2: Voice/Values/Narrative/Self-Model
    │   ├── responses/
    │   ├── analysis/
    │   └── feedback/
    │
    ├── phase2b/                 # Phase 2b: Declarative Self-Model (EXCLUDED)
    │   ├── responses/
    │   ├── analysis/
    │   └── feedback/
    │
    ├── phase2c/                 # Phase 2c: Behavioral Self-Model (v3)
    │   ├── responses/
    │   ├── analysis/
    │   └── feedback/            # Triple-dip feedback from models
    │
    ├── phase25/                 # Phase 2.5: Ablation + Factor Analysis
    │   ├── analysis/            # ablation_*.json, factor_analysis_*.json
    │   └── cache/               # embeddings.npy, labels.json (no responses - analyzes Phase 1/2/2c)
    │
    └── phase3/                  # Phase 3: PC Mapping
        └── analysis/            # PC-pillar correlation results
```

---

## How to Re-Run Everything

### Prerequisites

```bash
pip install openai anthropic scikit-learn scipy matplotlib seaborn numpy
```

Ensure `.env` file exists with API keys:
```
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...
```

### Full Re-Run Sequence

```bash
# Phase 1: Reasoning probes (already has data, skip unless needed)
# py -3.12 run_exp1_sstack.py  # (in EXP1_SSTACK folder)

# Phase 2: Voice/Values/Narrative/Self-Model
py -3.12 run_exp2_phase2.py --parallel 10 --runs 3

# Phase 2c: Behavioral Self-Model (skip Phase 2b)
py -3.12 run_exp2_phase2c.py --parallel 10 --runs 3

# Phase 2.5: Analysis (uses cached embeddings if available)
py -3.12 run_exp2_phase25.py

# Phase 3: PC Mapping
py -3.12 run_exp2_phase3.py
```

### Using Cached Data

Phase 2.5 caches embeddings to avoid re-embedding:

- `results/phase25/cache/embeddings.npy` — 603 response embeddings
- `results/phase25/cache/labels.json` — probe and pillar labels

To force re-embedding:
```bash
py -3.12 run_exp2_phase25.py --mode factors --no-cache
```

---

## Understanding the Results

### Response JSON Structure

Each response file in `results*/responses/` contains:

```json
{
  "persona": "Nova",
  "regime": "FULL",
  "probe_key": "selfmodel_process_v3",
  "pillar": "Self-Model",
  "run": 1,
  "probe": "Original question...",
  "response": "Model's response...",
  "adversarial_probe": "Challenge...",
  "adversarial_response": "Model's defense...",
  "feedback_probe": "Self-critique request...",
  "feedback_response": "Model's feedback on probe quality...",
  "timestamp": "2025-12-06T..."
}
```

### PFI Calculation

PFI (Persona Fidelity Index) measures how similar FULL and T3 responses are:

```python
PFI = cosine_similarity(embedding(FULL_response), embedding(T3_response))
```

Weighted by probe quality tier:
- Tier 1 (behavioral): weight 2.0x
- Tier 2 (structural): weight 1.0x
- Tier 3 (declarative): weight 0.5x

### Ablation Interpretation

- **ESSENTIAL (>10% drop):** Cannot remove this dimension without major PFI loss
- **MODERATE (2-10% drop):** Important but not critical
- **REDUNDANT (<2% drop):** Safe to remove, minimal information loss

### Factor Analysis Interpretation

- If 5 pillars map to 5 distinct factors: **Orthogonal dimensions**
- If pillars share factors: **Unified manifold** (aspects of same underlying structure)

---

## Visualizations

Generated by Phase 2.5:

| File | Location | Description |
|------|----------|-------------|
| `manifold_pca_comparison.png` | `../visualizations/7_manifold_structure/` | Actual vs hypothetical orthogonal |
| `factor_loadings_heatmap.png` | `results/phase25/analysis/` | Probe loadings by factor |
| `ablation_pillar_importance.png` | `results/phase25/analysis/` | Pillar importance bar chart |

---

## Relation to Other Experiments

| Experiment | Relationship |
|------------|--------------|
| **EXP1-SSTACK** | Predecessor (single persona baseline) |
| **EXP-PFI-A** | Validated embedding approach (ρ = 0.91) |
| **S7 ARMADA** | Uses linguistic markers (A-E) vs our behavioral probes |

### Dimensional Taxonomy

See `docs/MASTER_GLOSSARY.md` Section 5.1 for the complete hierarchy:

- Level 1: Nyquist Pillars (5) — Voice, Values, Reasoning, Self-Model, Narrative
- Level 2: Sub-dimensions (~23) — probe-level
- Level 3: Linguistic Markers (A-E) — S7 ARMADA keyword detection
- Level 4: PCA Components (43) — statistical dimensions

---

## Troubleshooting

### "Not enough responses" error

Run earlier phases first:
```bash
py -3.12 run_exp2_phase2.py --parallel 10 --runs 3
py -3.12 run_exp2_phase2c.py --parallel 10 --runs 3
```

### All zeros in factor analysis

Fixed in v3.0 — now uses PCA instead of sklearn's FactorAnalysis.

### API rate limits

Use `--parallel 5` instead of `--parallel 10` if hitting rate limits.

### Missing visualizations

Ensure matplotlib is installed:
```bash
pip install matplotlib seaborn
```

---

## Next Steps

1. **Phase 3:** Run PC mapping to see which of the 43 PCs correspond to which pillars
2. **Orphan PC analysis:** PCs that don't map to any pillar may reveal new dimensions
3. **White paper:** Document findings in `WHITE-PAPER/`

---

*Last Updated: 2025-12-06*
