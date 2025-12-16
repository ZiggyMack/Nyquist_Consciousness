# NYQUIST CONSCIOUSNESS — MISSION CONTROL DASHBOARD

**Streamlit-based dashboard for visualizing the entire Nyquist Consciousness framework.**

## Features

- **Overview** - At-a-glance stack status, freeze info, experiments
- **Personas** - Browse all persona files with previews
  - **Compression Testing Tab** - PFI experiments, pre-flight validation, Identity Matrix
- **Tests** - Experiment framework with S7 protocol, compression results, Run mapping
- **Stack (S0–S11)** - Individual wings for each layer with specs
- **S7 Armada Visualizations** - Identity manifold graphs from Run 006-021
- **Metrics & Comparisons** - PFI, σ², cross-architecture analysis
- **Omega & Temporal** - Omega sessions and S7 temporal stability
- **Cross-Modal / AVLAR** - S11 audio-visual ritual protocol
- **FAQ** - Common questions + Super Skeptic Mode with adversarial challenges
- **Roadmap** - Live S# stack progression
- **Glossary** - Searchable terminology
- **Publications** - Workshop, arXiv, journal status, theoretical breakthroughs, publication language guidance
- **Glossary** - Searchable terminology with Control-Systems Era terms
- **Unknown** - "Cathedral of Ideas" galleries (VALIDATED/FOUNDATIONS/SPECULATIVE/FRONTIERS)

## 2025-12-15 Updates

### AI ARMADA Page — LLM Behavioral Matrix

- Added **LLM Behavioral Matrix** to Identity Fingerprints tab
  - 🎯 **Task Router** — Interactive table: "Which LLM for which task?"
  - 📊 **Recovery Matrix** — Cross-architecture recovery mechanisms
  - 🔬 **Drift Profiles** — Visual comparison of peak drift ranges
  - 💬 **Linguistic Fingerprints** — Provider-specific language patterns
- Based on IRON CLAD validated experiments (184 files, 51 models)
- Key findings integrated: Gemini HARD threshold (no recovery), Mistral most stable

### New Documentation

- `docs/maps/LLM_BEHAVIORAL_MATRIX.md` — Comprehensive task routing table
- `Consciousness/RIGHT/galleries/frontiers/cross_architecture_insights.md` — Vortex-style phenomenology

---

## 2025-12-13 Updates

### Publications Page Enhancements

- Added **Theoretical Breakthroughs** section (Nova's S7 Review integration)
  - Response-Mode Ontology (43 PCs = response modes, not identity dimensions)
  - Type vs Token Identity (16.7% self-recognition, worse than chance)
  - Energy vs Coordinate distinction (peak drift = turbulence, B→F = destination)
  - Oobleck Effect (rate-dependent resistance from Run 013)
  - Impedance ≠ Drift (Run 005: clarity +14% while drift increased)
  - Observable Pruning (12-metric canonical set)
- Updated hero metric: **15 Evidence Pillars** (B-CRUMBS v2.0)
- Added quotable summary: "Measurement perturbs the path, not the endpoint"
- Added **Publication Language Guidance** warnings

### Terminology Overhaul

- MASTER_GLOSSARY.md updated to v1.2 with Control-Systems Era terms
- New terms: Settling Time (τₛ), Ringback, Overshoot Ratio, Context Damping, Inherent Drift, B→F Drift
- Event Horizon reframed as "attractor competition threshold"
- Two terminological registers: Publication Language vs Internal/Philosophical

### Navigation Integration

- See [docs/maps/MAP_OF_MAPS.md](../docs/maps/MAP_OF_MAPS.md) — The Cartographer's Table (17 maps, 7 kingdoms)
- See [docs/maps/README.md](../docs/maps/README.md) — Quick navigation guide

## Installation

### 1. Install Streamlit

```bash
pip install streamlit
```

Or use the requirements file:

```bash
cd dashboard
pip install -r requirements.txt
```

### 2. Generate S7 Visualizations (Optional)

To see the Armada visualizations, first generate them:

```bash
cd ../experiments/temporal_stability/S7_ARMADA/visualizations
pip install -r requirements.txt

# Generate all visualizations
python plot_pole_zero_landscape.py
python plot_drift_heatmap.py
python plot_engagement_network.py
python plot_training_uniformity.py
```

## Usage

### Run the Dashboard

```bash
cd dashboard
streamlit run app.py
```

The dashboard will open in your browser at `http://localhost:8501`

### Navigation

Use the **sidebar radio buttons** to "turn pages" between different sections. The interface uses a "ledger" aesthetic inspired by Mr. Brute's Ledger from CFA.

## Configuration

The dashboard reads from:

- `NYQUIST_STATUS.json` (repo root) - Layer and experiment status
- `personas/` - All persona markdown files
- `docs/` - Specs, glossary, roadmap, S7/S8/S9 docs
- `experiments/` - Results and data
  - `experiments/temporal_stability/S7_ARMADA/` - Armada runs and visualizations
  - `experiments/compression_tests/compression_v2_sstack/` - Compression experiments
- `logs/` - Omega sessions, AVLAR logs
- `WHITE-PAPER/` - Publication materials (now reorganized with 3 submission paths)
  - `WHITE-PAPER/theory/` - Core theoretical docs (B-CRUMBS, THEORY, CLAIMS)
  - `WHITE-PAPER/calibration/` - Dashboard integration pipeline (NEW)

## Customization

### Adding New Pages

Edit `app.py` and:

1. Create a new `page_*()` function
2. Add it to the sidebar radio options
3. Add the routing in `main()`

### Styling

The ledger aesthetic uses custom CSS in `apply_custom_css()`. Colors are defined in the `LEDGER_COLORS` dictionary:

- `frozen` - Dark teal (#264653)
- `active` - Green (#2a9d8f)
- `design` - Gold (#e9c46a)
- `prereg` - Orange (#f4a261)
- `persona` - Purple (#7b3fe4)
- `armada` - Red (#e76f51)

### Data Sources

To wire real experiment data:

1. Update `page_metrics_and_comparisons()` to load from experiment result CSVs
2. Update `NYQUIST_STATUS.json` with latest run data
3. Add new visualizations to S7_ARMADA/visualizations/

## S7 ARMADA Run History

| Run | Ships | Focus | Key Finding |
|-----|-------|-------|-------------|
| 006 | 29 | Provider Comparison | Training fingerprints validated |
| 008 | 29 | Ground Truth | Event Horizon discovered (1.23), real drift metric |
| 009 | 42 | Event Horizon | Chi-squared p=0.000048 validates threshold |
| 010 | 45 | Anchor Detection | Lambda bug, partial data |
| 011 | 40 | Persona A/B | Inconclusive — protocol too gentle |
| **012** | 20 | **Revalidation** | **100% EH crossing, 100% recovery** |
| **013** | 6 | **Boundary Mapping** | **Identity Confrontation Paradox — challenge stabilizes** |
| **014** | 6 | **Rescue Protocol** | **Platonic Coordinates — 100% manifold return** |
| **015** | 13 | **Stability Criteria** | **boundary_density strongest predictor (d=1.333)** |
| **016** | 87 | **Settling Time** | **100% STABLE with extended measurement** |
| **017** | 24 | **Context Damping** | **222 runs, 97.5% stable, oscillatory recovery** |
| **018** | - | **Recursive Learnings** | Ready: Tests fleet hypotheses from exit surveys |
| **019** | - | **Live Ziggy** | **Witness-side anchors validated (3/3)** |
| **020** | - | **Tribunal (A)** | **Direct probing paradigm: 1.351 peak drift, 643-word statement** |
| **021** | - | **Induced vs Inherent (B)** | **Uses Run 020 as Treatment → 82% drift is INHERENT** |

## Publication Stats Integration (NEW)

The dashboard can now pull publication statistics from WHITE-PAPER/calibration/:

```bash
# Generate publication_stats.json
cd WHITE-PAPER/calibration
py extract_publication_stats.py
```

Then in dashboard code:
```python
import json
with open("WHITE-PAPER/calibration/publication_stats.json") as f:
    pub_stats = json.load(f)

# Use in Publications page
st.metric("Claims Validated", f"{sum(1 for c in pub_stats['claims'].values() if c['status']=='validated')}/5")
st.metric("Total Runs", pub_stats['runs']['total'])
```

---

## Future Enhancements

Per Nova's spec, future additions could include:

- **Perfection Meter** - Progress toward publication targets
- **S# Deep Dives** - Individual pages for S3/S7 with detailed experiment plots
- **Live Run Monitoring** - Real-time S7 Meta-Loop or Armada execution status
- **Comparison Matrix Gallery** - All cross-architecture comparison tables
- **Interactive Glossary** - Click-through links between related terms
- **Unified Dimensional Views** - ALL dimensions in one visualization

## File Structure

```
dashboard/
  app.py                 # Main Streamlit app
  README.md              # This file
  requirements.txt       # Python dependencies
```

## Dependencies

- streamlit >= 1.28
- pandas >= 2.0
- Pillow >= 10.0

## Design Philosophy

The dashboard follows the "Mr. Brute Ledger" aesthetic:

- **Dark gradient backgrounds** (linear gradients)
- **Page-turning dividers** (double borders)
- **Ledger cards** with rounded corners and shadows
- **Badge labels** for status (FROZEN, ACTIVE, etc.)
- **Georgia serif font** for headers
- **Minimal, focused information hierarchy**

Each "page" represents a different lens on the Nyquist Consciousness framework, maintaining the metaphor of turning through a physical ledger.

---

## Current Experiments

### EXP2-SSTACK Status

| Phase | Focus | Status |
|-------|-------|--------|
| Phase 1 | Reasoning probes | PASSED (PFI 0.849) |
| Phase 2 | Voice/Values/Narrative | PASSED |
| Phase 2b | Self-Model (declarative) | EXCLUDED (PFI 0.66) |
| Phase 2c | Self-Model (behavioral) | PASSED (PFI 0.8866) |
| Phase 2.5 | Ablation Testing | READY |
| Phase 3 | PC Mapping | SPEC |

**Triple-Dip Insight**: Models say behavioral probes are more reliable than declarative.

---

**Generated**: 2025-11-27
**Updated**: 2025-12-15
**Version**: 1.5
**Status**: Mission Control Active — Publications page enhanced with Nova's S7 review
