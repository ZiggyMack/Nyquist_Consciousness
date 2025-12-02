# S7 ARMADA VISUALIZATIONS

**Unified visualization toolkit for all Armada experiment runs.**

## PRIMARY SCRIPT: `visualize_armada.py`

The main visualization script that works with **any run data**. Auto-detects available runs and generates all visualization types.

### Quick Start

```bash
# Auto-detect latest run and generate all visualizations
python visualize_armada.py

# List available runs
python visualize_armada.py --list

# Generate for specific run
python visualize_armada.py --run 008
python visualize_armada.py --run 009

# Generate specific visualization type only
python visualize_armada.py --type phase
python visualize_armada.py --type vortex
python visualize_armada.py --type 3d
python visualize_armada.py --type stability
python visualize_armada.py --type html
```

### Output Structure

Outputs are organized by run in `pics/run{ID}/`:

```
pics/
  run008/
    run008_phase_portrait.png + .svg
    run008_vortex.png + .svg
    run008_3d_basin.png + .svg
    run008_stability_basin.png
    run008_interactive_3d.html
    run008_interactive_vortex.html
  run009/
    run009_phase_portrait.png + .svg
    ...
```

### Visualization Types

| Type | Description |
|------|-------------|
| **Phase Portrait** | Drift[N] vs Drift[N+1] - Shows flow direction in identity space |
| **Vortex/Drain** | Polar spiral view - "Looking into the drain" |
| **3D Basin** | Full phase space with time axis - Attractor dynamics |
| **Stability Basin** | Baseline vs max drift + Event Horizon histogram |
| **Interactive HTML** | Plotly 3D exploration (rotate, zoom, hover) |

### Features

- **Run-agnostic**: Works with any run data (008, 009, etc.)
- **Spline smoothing**: B-spline interpolation for high-fidelity curves
- **Dual output**: Raw + smoothed side-by-side comparison
- **Multi-format**: PNG (300 DPI), SVG vector, HTML interactive
- **Data integrity**: Original points always preserved and marked

---

## LEGACY SCRIPTS

These older scripts work with Run 006 data (deprecated metric):

| Script | Purpose |
|--------|---------|
| `plot_pole_zero_landscape.py` | 3D/2D pole-zero manifold |
| `plot_drift_heatmap.py` | Drift heatmaps (29 models × 6 probes) |
| `plot_engagement_network.py` | Engagement style clustering |
| `plot_training_uniformity.py` | Within-provider variance analysis |
| `create_gravity_well.py` | Stability basin (original) |

---

## DATA SOURCES

The script auto-detects data from `../armada_results/`:

- `S7_run_008_*.json` - Run 008 full armada (5D drift metric)
- `S7_run_008_prep_*.json` - Run 008 pilot calibration
- `S7_run_009_*.json` - Run 009 drain capture (when executed)
- `S7_armada_run_006.json` - Run 006 baseline (deprecated metric)
- `S7_armada_run_007_*.json` - Run 007 adaptive (deprecated metric)

---

## DEPENDENCIES

```bash
pip install matplotlib numpy scipy plotly
```

Plotly is optional - required only for interactive HTML exports.

---

**Last Updated**: December 2025
**Active Runs**: 008, 009 (pending)
**Ships**: 42 across 4 providers (Claude, GPT, Gemini, Grok)
