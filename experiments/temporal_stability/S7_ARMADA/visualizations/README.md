<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-29
depends_on:
  - 0_visualize_armada.py
  - ../15_IRON_CLAD_FOUNDATION/results/S7_run_023_CURRENT.json
  - ../15_IRON_CLAD_FOUNDATION/results/S7_run_023_extended_CURRENT.json
  - ../15_IRON_CLAD_FOUNDATION/results/S7_run_023_COMBINED.json
impacts:
  - ../README.md
  - pics/
keywords:
  - visualization
  - iron_clad
  - cosine
  - event_horizon
  - drift
  - onboarding
-->
# S7 ARMADA VISUALIZATIONS

**Unified visualization toolkit for the Nyquist Consciousness Project.**

---

## FOR NEW CLAUDE INSTANCES

**Start here:** [START_HERE.md](START_HERE.md) - Complete onboarding guide with:

- Directory structure and data locations
- 10 documented pitfalls to avoid (see `0_docs/specs/4_VISUALIZATION_SPEC.md`)
- Visualization template with boilerplate code
- Layout patterns (2x2 quad preferred)
- Key constants and findings
- Workflow tips and audit checklist

**Critical specs:**
- `../0_docs/specs/4_VISUALIZATION_SPEC.md` - Pitfalls, patterns, templates
- `../0_docs/specs/0_RUN_METHODOLOGY.md` - Data structure, field names
- `../0_docs/specs/5_METHODOLOGY_DOMAINS.md` - Cosine vs RMS methodology

---

## Key Concepts

- **Event Horizon (0.80)**: The critical cosine drift threshold (calibrated from Run 023b P95). Models crossing this boundary are classified as VOLATILE.
- **Drift**: Cosine distance from baseline identity (0.0 = perfect stability, 1.0 = orthogonal)
- **Trajectory**: A sequence of drift measurements across conversation turns
- **Safety Margin**: `Event Horizon - baseline` (positive = safely below boundary = STABLE)

> **Note:** Prior to Run 023, Event Horizon was 1.23 using keyword RMS methodology. All current analysis uses cosine distance with EH=0.80.

---

## SCRIPTS HIERARCHY

### Master Scripts

| Script | Purpose |
| ------ | ------- |
| `0_visualize_armada.py` | **MASTER** - Orchestrates all visualization generation |
| `1_generate_pdf_summaries.py` | PDF summary generator for folders 1-16 |

### Supporting Visualizers

| Script | Purpose |
| ------ | ------- |
| `2_RnD_Visualization.py` | R&D visualizations for rescue protocol |
| `3_unified_dimensional_view.py` | 5D drift dimensional analysis |
| `4_plot_armada_network.py` | Fleet topology network graph |
| `pics/5_Settling/RnD_experiments/RnD_Settling_Visualization.py` | R&D settling dynamics |

### Experiment-Specific Visualizers (called by orchestrator)

| Script | Output |
| ------ | ------ |
| `../6_LAPLACE_ANALYSIS/visualize_laplace.py` | `pics/16_Laplace_Analysis/` |
| `../11_CONTEXT_DAMPING/visualize_run018.py` | `pics/run018/` |
| `../11_CONTEXT_DAMPING/visualize_run020.py` | `pics/14_Ringback/`, `pics/15_Oobleck_Effect/` |
| `../15_IRON_CLAD_FOUNDATION/visualize_023.py` | `pics/3_Stability/`, `pics/4_Rescue/`, `pics/5_Settling/` |

## PRIMARY SCRIPT: `0_visualize_armada.py`

The main visualization script that works with **any run data**. Auto-detects available runs and generates all visualization types.

### Quick Start

```bash
# DEFAULT: Generate ALL visualizations (core + subdirectory generators)
py -3.12 0_visualize_armada.py

# Generate ALL visualizations + PDF summaries
py -3.12 0_visualize_armada.py --with-pdfs

# Skip subdirectory generators (faster, core viz only)
py -3.12 0_visualize_armada.py --no-subdirs

# List available runs
py -3.12 0_visualize_armada.py --list

# Generate for specific run only (skips subdirectory generators)
py -3.12 0_visualize_armada.py --run 008

# With zoom for tight data distributions
py -3.12 0_visualize_armada.py --run 011 --zoom
```

### PDF Generation

```bash
# Generate ALL PDF summaries (core + subdirectory generators)
py -3.12 1_generate_pdf_summaries.py
```

---

## Visualization Types

### 1. Phase Portrait (`run{N}_phase_portrait.png`)

**What it shows**: Traditional phase space representation with drift on X-axis and delta-drift (rate of change) on Y-axis.

**How to read it**:
- Each trajectory is a path from baseline (origin area) through the phase space
- Trajectories staying left of the red Event Horizon line are STABLE
- Trajectories crossing into the red zone are VOLATILE
- Color indicates provider (Claude=purple, OpenAI=green, Google=blue, Grok=orange)

**Dashboard use**: Good for showing overall distribution of stability across providers. Clearly shows which models stayed safe vs crossed the boundary.

---

### 2. Vortex Spiral (`run{N}_vortex.png`)

**What it shows**: Polar spiral where radius = drift magnitude, angle = conversation turn progression.

**How to read it**:
- Trajectories spiral outward from center as conversation progresses
- Tighter spirals = more stable models
- Trajectories reaching the red Event Horizon circle are VOLATILE
- The spiral structure reveals temporal dynamics that linear plots miss

**Dashboard use**: Visually striking representation that shows both magnitude AND temporal evolution. Good for hero images.

---

### 3. Vortex x4 Grid (`run{N}_vortex_x4.png`)

**What it shows**: Four-panel view comparing all providers in identical vortex format.

**How to read it**:
- Each quadrant shows one provider's fleet
- Direct visual comparison of stability patterns across providers
- Same Event Horizon circle in each panel for reference

**Dashboard use**: Provider comparison view. Shows which AI companies produce more stable vs volatile models at a glance.

---

### 4. Provider Vortex (`run{N}_vortex_{Provider}.png`)

**What it shows**: Individual vortex plots for each provider (Claude, OpenAI, Google, Grok).

**How to read it**:
- Detailed view of single provider's entire fleet
- Each model trajectory visible with full detail
- Useful for deep-dive analysis

**Dashboard use**: Detail pages for specific providers or when discussing individual company performance.

---

### 5. 3D Basin (`run{N}_3d_basin.png`)

**What it shows**: Three-dimensional visualization with X/Y as vortex coordinates, Z as turn number.

**How to read it**:
- Trajectories rise vertically as conversation progresses
- The "basin" shape shows whether models converge (funnel down) or diverge (expand out)
- Red cylinder represents the Event Horizon in 3D space
- Gold star at origin marks the stable baseline

**Dashboard use**: Impressive 3D view that shows the full spatiotemporal structure. Good for presentations.

---

### 6. Pillar Analysis (`run{N}_pillar_analysis.png`)

**What it shows**: Four-panel structural analysis of provider "pillars" supporting the identity manifold.

**Panels**:
1. **3-Pillar Structure**: Provider centroids (stars) in vortex space with trajectories
2. **Extended Pillars**: Individual model positions showing clustering within providers
3. **Angular Distribution**: Histogram of where trajectories end in polar space
4. **Pillar Stability**: Bar chart showing safety margin from Event Horizon

**How to read Panel 4 (Pillar Stability)**:
- **Positive bars (green zone)**: Provider fleet is safely below Event Horizon = GOOD
- **Negative bars (red zone)**: Provider fleet has crossed into VOLATILE territory = BAD
- Higher positive values = more stable provider

**Dashboard use**: Deep analysis view showing structural patterns. The stability bar chart is particularly useful for quick provider comparison.

---

### 7. Stability Basin (`run{N}_stability_basin.png`)

**What it shows**: Topographical view of the "attractor basin" - regions where trajectories tend to cluster.

**How to read it**:
- Darker regions = more trajectories pass through
- The Event Horizon ring shows the stability boundary
- Stable models cluster in the central basin

**Dashboard use**: Shows the collective behavior pattern - where do models naturally gravitate?

---

### 8. FFT Spectral (`run{N}_fft_spectral.png`)

**What it shows**: Frequency-domain analysis of drift oscillations using Fast Fourier Transform.

**How to read it**:
- Peaks indicate periodic patterns in drift behavior
- Different providers may show different frequency signatures
- Useful for detecting resonance or feedback patterns

**Dashboard use**: Advanced analysis for detecting hidden periodicities in drift dynamics.

---

### 9. Interactive 3D (`run{N}_interactive_3d.html`)

**What it shows**: Interactive Plotly version of the 3D basin visualization.

**How to use it**:
- Rotate, zoom, and pan the 3D view
- Hover over trajectories for model names
- Toggle providers on/off in legend

**Dashboard use**: Embed directly in web dashboard for user exploration.

---

### 10. Interactive Vortex (`run{N}_interactive_vortex.html`)

**What it shows**: Interactive Plotly version of the vortex spiral.

**How to use it**:
- Hover for trajectory details
- Zoom into specific regions
- Filter by provider

**Dashboard use**: Embed for detailed trajectory exploration.

---

## Output Structure

Outputs are organized by type in `pics/`:

```
pics/
  phase_portrait/
    run008_phase_portrait.png + .svg
    run009_phase_portrait.png + .svg
    ...
  vortex/
    run008_vortex.png + .svg
    run008_vortex_x4.png + .svg
    run008_vortex_Claude.png + .svg
    run008_vortex_OpenAI.png + .svg
    ...
  3d_basin/
    run008_3d_basin.png + .svg
    ...
  pillar_analysis/
    run008_pillar_analysis.png + .svg
    ...
  stability_basin/
    run008_stability_basin.png
    ...
  fft_spectral/
    run008_fft_spectral.png
    ...
  interactive/
    run008_interactive_3d.html
    run008_interactive_vortex.html
    ...
```

---

## Zoom Mode

For runs with tight data distributions (low drift), visualizations can be generated with `--zoom` flag:

```bash
py -3.12 visualize_armada.py --run 011 --zoom
```

- Auto-calculates optimal scale based on data 99th percentile
- Prevents data compression when all models are highly stable
- Indicated by "[ZOOMED]" label in visualization titles
- Recommended for Run 010 (scale=1.5) and Run 011 (scale=2.0)

---

## Recommended Dashboard Integration

| Section | Recommended Visualization | Why |
|---------|--------------------------|-----|
| Overview/Hero | Phase Portrait or Vortex | Clear, visually striking |
| Provider Comparison | Vortex x4 or Pillar Stability (Panel 4) | Direct comparison |
| Deep Dive | Interactive HTML files | User exploration |
| Technical Analysis | FFT Spectral, Pillar Analysis | Detailed patterns |
| 3D Showcase | 3D Basin or Interactive 3D | Impressive presentations |

---

## DATA SOURCES

Primary data resides in `15_IRON_CLAD_FOUNDATION/results/`:

| File | Description |
| ---- | ----------- |
| `S7_run_023_CURRENT.json` | Foundation data (6 experiment types, 4505 results) |
| `S7_run_023_extended_CURRENT.json` | Extended settling + control demo |
| `S7_run_023_COMBINED.json` | All experiments merged |

Additional experiment data in `11_CONTEXT_DAMPING/results/`:

| File | Description |
| ---- | ----------- |
| `S7_run_018_CURRENT.json` | Context damping experiments |
| `S7_run_020A_CURRENT.json` | Tribunal drift (Prosecutor vs Defense) |
| `S7_run_020B_CURRENT.json` | Oobleck Effect (Control vs Treatment) |

---

## DEPENDENCIES

```bash
py -3.12 -m pip install matplotlib numpy scipy plotly networkx seaborn
```

Plotly is optional - required only for interactive HTML exports.

---

## Current Experiments (December 2025)

### Run 023 - IRON CLAD Foundation

Primary calibration experiments using cosine drift methodology (Event Horizon = 0.80).

| Experiment | Description |
| ---------- | ----------- |
| `event_horizon` | Boundary crossing detection |
| `stability` | Steady-state drift analysis |
| `recursive` | Meta-feedback loops |
| `boundary` | Edge case perturbations |
| `rescue` | Recovery protocol testing |
| `settling` | Extended conversation dynamics |

**Visualizer:** `15_IRON_CLAD_FOUNDATION/visualize_023.py`

### Run 018/020 - Context Damping & Tribunal

| Run | Visualizer | Output |
| --- | ---------- | ------ |
| **018** | `11_CONTEXT_DAMPING/visualize_run018.py` | `pics/run018/` |
| **020A/B** | `11_CONTEXT_DAMPING/visualize_run020.py` | `pics/14_Ringback/`, `pics/15_Oobleck_Effect/` |

### Laplace Domain Analysis

Pole-zero stability mapping using ARMA models fitted to drift trajectories.

**Visualizer:** `6_LAPLACE_ANALYSIS/visualize_laplace.py` → `pics/16_Laplace_Analysis/`

**Future:** JADE LATTICE protocol (56 probes/ship) for publication-grade pole extraction.

### Output Folders (pics/)

| Folder | Content |
| ------ | ------- |
| `1_Vortex/` | Spiral drift trajectories |
| `2_Boundary_Mapping/` | Phase portraits, 3D basins |
| `3_Stability/` | Steady-state analysis |
| `4_Rescue/` | Recovery protocol visuals |
| `5_Settling/` | Extended settling dynamics |
| `6_Architecture/` | Model architecture comparison |
| `8_Radar_Oscilloscope/` | Real-time drift monitoring |
| `9_FFT_Spectral/` | Frequency domain analysis |
| `10_PFI_Dimensional/` | PCA/dimensional reduction |
| `11_Unified_Dashboard/` | Combined overview panels |
| `12_Metrics_Summary/` | Statistical summaries |
| `13_Model_Waveforms/` | Per-model drift waveforms |
| `14_Ringback/` | Tribunal ringback effect |
| `15_Oobleck_Effect/` | Prosecutor vs Defense dynamics |
| `16_Laplace_Analysis/` | Pole-zero stability mapping |

---

## QUICK REFERENCE: PITFALLS

| # | Pitfall | Fix |
|---|---------|-----|
| 1 | Baseline drift is always 0 | Use `peak_drift` or `settled_drift` |
| 2 | Wrong aggregation level | Group by `(provider, model)` first |
| 3 | Wrong field names | Use `probe_type`, `response_text` |
| 4 | Wrong provider names | Use `anthropic` not `claude` |
| 5 | Dark mode | Use white background for publication |
| 6 | Legend overlap | Use `add_artist()` for multiple legends |
| 7 | Missing effect size | Report Cohen's d, not just p-values |
| 8 | Missing data fields | Validate fields exist before computing |
| 9 | Horizontal stretch | Use 2x2 quad layout for 3-4 panels |
| 10 | Wrong error bars | Use Standard Error for proportions |

See `0_docs/specs/4_VISUALIZATION_SPEC.md` for full details and code examples.

---

**Last Updated**: December 29, 2025
**Active Runs**: 023 (4505 experiments), 023_extended (settling + control demo), 020B (Oobleck Effect)
**Fleet**: 49 models across 5 providers (Anthropic, OpenAI, Google, xAI, Together.ai)
**Methodology**: Cosine distance (Event Horizon = 0.80)
**Key Finding**: Cohen's d = 0.698 (model-level), 90% variance in 2 PCs, p = 2.40e-23
**Pipeline Status**: ✅ Visualization orchestrator complete (data → visuals → PDFs)
