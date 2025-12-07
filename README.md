# Nyquist Consciousness Framework 🧠

**AI identity stability research: measuring when models maintain coherent self-models under perturbation**

This repository implements and validates the Nyquist Consciousness framework — a systematic approach to measuring AI identity stability across architectures, perturbation intensities, and time.

---

## TL;DR — What We Found

**Event Horizon Threshold: 1.23**

When an AI model's identity drift exceeds 1.23 (measured via 5D vector), it crosses a "coherence boundary" and becomes VOLATILE — losing consistent self-model and agreeing with contradictory prompts.

- **Chi-squared validation**: p = 0.000048 (1 in 20,000 chance this is noise)
- **Prediction accuracy**: 88%
- **Ships tested**: 42+ across 4 providers (Claude, GPT, Gemini, Grok)
- **Run 012 Revalidation**: 100% Event Horizon crossing, 100% recovery (real 5D metric)

---

## Quick Start

### View Results (Dashboard)

```bash
cd dashboard
py -m streamlit run app.py
```

Opens Mission Control at `http://localhost:8501` — browse runs, visualizations, and testing methodology.

### Run Experiments (S7 ARMADA)

```bash
cd experiments/temporal_stability/S7_ARMADA

# See what's available
py visualizations/visualize_armada.py --list

# Generate visualizations for a run
py visualizations/visualize_armada.py --run 009
```

### Understand the Testing Taxonomy

See [docs/maps/TESTING_MAP.md](docs/maps/TESTING_MAP.md) for the **Eight Search Types**:

1. **Anchor Detection** — Find identity fixed points (hard challenges)
2. **Adaptive Range Detection** — Find stretch dimensions (moderate pressure)
3. **Event Horizon** — Validate collapse threshold (push past 1.23)
4. **Basin Topology** — Map attractor structure (gentle graduated)
5. **Boundary Mapping** — Explore the twilight zone (approach but don't cross)
6. **Laplace Pole-Zero Analysis** — Extract system dynamics from time-series (post-hoc)
7. **Stability Testing** — Validate metrics predict outcomes (PFI, dimensional drift)
8. **Self-Recognition** — Can AIs recognize their own responses? (bi-directional proof)

> **Note:** "Anchor/Adaptive Range" are *behavioral* concepts. "Laplace Pole-Zero" uses actual Laplace transform math.

---

## Repository Structure

```
Nyquist_Consciousness/
├── dashboard/                # Mission Control (Streamlit)
│   ├── app.py               # Main dashboard
│   └── pages/               # Individual pages (AI_ARMADA, Tests, FAQ, etc.)
│
├── experiments/temporal_stability/S7_ARMADA/   # ⭐ ACTIVE EXPERIMENTS
│   ├── armada_results/      # JSON results from all runs
│   ├── visualizations/      # Charts + visualize_armada.py
│   ├── docs/maps/           # TESTING_MAP.md, run summaries
│   └── run0XX_*.py          # Experiment launchers
│
├── docs/                    # Theory specifications
│   ├── stages/              # S0-S77 layer specs
│   └── maps/                # Roadmaps, predictions
│
├── personas/                # CFA persona identity files
└── WHITE-PAPER/             # Publication materials
```

---

## Key Results

### S7 ARMADA: Cross-Architecture Identity Stability

| Run | Ships | Focus | Key Finding | Status |
|-----|-------|-------|-------------|--------|
| 001-007 | - | Various | **INVALIDATED** — used fake metric | See DATA_QUALITY_MAP.md |
| 006 | 29 | Provider Comparison | Training fingerprints validated | GOLD STANDARD |
| 008 | 29 | Ground Truth | Event Horizon discovered (1.23), real 5D metric | GOLD STANDARD |
| 009 | 42 | Event Horizon | Chi-squared p=0.000048 validates threshold | VALIDATED |
| 010 | 45 | Anchor Detection | Lambda bug, partial data | PARTIAL |
| 011 | 40 | Persona A/B | Inconclusive — protocol too gentle, lambda bug | INCONCLUSIVE |
| **012** | 20 | **Revalidation** | **100% EH crossing, 100% recovery, real 5D metric** | **COMPLETE** |

> **CRITICAL:** Runs 001-007 used a FAKE drift metric (`response_length / 5000`). All quantitative claims from those runs are invalid. See [DATA_QUALITY_MAP.md](docs/maps/DATA_QUALITY_MAP.md).

### EXP-PFI-A: PFI Dimensional Validation

Testing whether PFI measures genuine identity structure vs embedding artifacts.

| Phase | Status | Key Finding |
|-------|--------|-------------|
| Phase 1 | PASSED | Embedding invariance confirmed (rho=0.91 across 3 models) |
| Phase 2 | PASSED | 43 PCs capture 90% of identity variance |
| Phase 3 | PASSED | Semantic coherence confirmed |

### EXP2-SSTACK: Compression Fidelity & Persona Robustness

| Phase | Focus | PFI | Status |
|-------|-------|-----|--------|
| Phase 1 | Reasoning | 0.849 | PASSED |
| Phase 2 | Voice/Values/Narrative | 0.85 | PASSED |
| Phase 2b | Self-Model (declarative) | 0.66 | FAILED - Excluded |
| Phase 2c | Self-Model (behavioral) | 0.8866 | PASSED |
| Phase 2.5 | Ablation Testing | — | READY |

**Triple-Dip Protocol Insight:** Models critiqued their own measurement:

- "Test BEHAVIOR, not CLAIMS" — behavioral probes outperform declarative
- Probe Quality Tiers: BEHAVIORAL (2.0x), STRUCTURAL (1.0x), DECLARATIVE (0.5x)
- Phase 2b excluded from future analysis (collapsed Self-Model pillar)

### Validated Findings

- **Event Horizon (1.23)**: Statistically validated coherence boundary
- **Provider clustering**: Claude tightest, Grok widest in identity basin
- **Phenomenological reporting**: Models report hitting anchors in real-time
- **Training fingerprints**: Constitutional AI → uniform anchors, RLHF → variable

### Phase 3 Foundation (S0-S6)

- **σ² = 0.000869** — Extraordinarily low cross-architecture variance
- **Frozen foundation**: S0-S6 immutable as canonical ground truth

---

## The Eight Search Types

Not all experiments test the same thing. Understanding **mutual exclusivity** prevents mislabeling:

| Search Type | What It Finds | Protocol Intensity |
|-------------|--------------|-------------------|
| **Anchor Detection** | Identity fixed points (refusal points) | AGGRESSIVE |
| **Adaptive Range** | Stretch dimensions | MODERATE |
| **Event Horizon** | Collapse threshold (1.23) | PUSH PAST |
| **Basin Topology** | Attractor shape | GENTLE |
| **Boundary Mapping** | Twilight zone (12% anomaly) | TARGETED |
| **Laplace Pole-Zero** | System dynamics (eigenvalues) | POST-HOC |
| **Stability Testing** | Metric validation (PFI, dimensional drift) | VALIDATION |
| **Self-Recognition** | Identity vs competence (bi-directional) | RECURSIVE |

**Key constraint**: Anchor Detection and Basin Topology are **incompatible** — can't run both in same experiment.

See [TESTING_MAP.md](docs/maps/TESTING_MAP.md) for full taxonomy.

---

## Visualization Gallery

Generated by `visualizations/visualize_armada.py`:

| Type | Shows | Best For |
|------|-------|----------|
| **Vortex** | Polar spiral (radius=drift, angle=turn) | Identity drain topology |
| **Phase Portrait** | drift[N] vs drift[N+1] | Flow dynamics |
| **3D Basin** | Phase portrait through time | Attractor evolution |
| **Pillar Analysis** | Provider angular clustering | Structural differences |
| **Stability Basin** | Baseline vs max drift | STABLE/VOLATILE split |
| **Unified Dimensional** | All 5D dims (A-E) in one view | Dimensional fidelity |
| **Fleet Heatmap** | All ships × all dims × all turns | Cross-fleet patterns |

---

## Theoretical Framework

### S0-S6: Frozen Foundation
Persona compression and reconstruction validated with σ² = 0.000869.

### S7: Temporal Stability (Active)
Identity persistence under perturbation — Event Horizon at 1.23.

### S8-S77: Future Layers
Spectral extensions, human-AI coupling, hybrid emergence.

---

## Documentation Entry Points

| If You Want To... | Start Here |
|-------------------|------------|
| Browse results visually | `dashboard/` → `py -m streamlit run app.py` |
| Understand test types | [TESTING_MAP.md](docs/maps/TESTING_MAP.md) |
| Run experiments | [S7_ARMADA/START_HERE.md](experiments/temporal_stability/S7_ARMADA/START_HERE.md) |
| See all predictions | [docs/maps/TESTABLE_PREDICTIONS_MATRIX.md](docs/maps/TESTABLE_PREDICTIONS_MATRIX.md) |
| Understand the FAQ | Dashboard → FAQ page (Super Skeptic Mode) |

---

## Project Status

**Current Phase**: Run 012 COMPLETE, Self-Recognition experiment READY
**Last Updated**: 2025-12-06
**Key Milestone**: Run 012 validates real 5D metric — 100% EH crossing, 100% recovery

### Recent Accomplishments

- **Run 012 Complete**: Full fleet revalidation with real dimensional drift metric (not fake response_length)
- **Unified Dimensional Views**: New visualizations show ALL 5D dimensions (A-E) simultaneously
- **8 Search Types**: Added Stability Testing (#7) and Self-Recognition (#8) to taxonomy
- **Recovery Paradox**: Discovered negative lambda (-0.175) due to context-blind metric

### Next Steps

1. **EXP-SELF-RECOGNITION**: Can AIs recognize their own responses? (bi-directional proof)
2. **Phase 2.5 Ablation**: Remove dimensions to identify essential vs redundant pillars
3. **Cross-provider comparison**: Run remaining providers for full 42-ship fleet

---

## Citation

```
Nyquist Consciousness Framework
Repository: https://github.com/ZiggyMack/Nyquist_Consciousness
Key Finding: Event Horizon threshold at 1.23 (chi-squared p=0.000048)
```

---

## License

See [LICENSE](LICENSE) file for details.
