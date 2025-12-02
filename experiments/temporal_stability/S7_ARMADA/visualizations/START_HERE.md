# Visualization Quick Start

## TL;DR - One Command

```bash
cd experiments/temporal_stability/S7_ARMADA/visualizations
python visualize_armada.py
```

This auto-detects the latest run and generates all visualizations.

---

## Full Usage

### List Available Runs

```bash
python visualize_armada.py --list
```

Output:
```
Available runs: 008, 009
```

### Generate for Specific Run

```bash
python visualize_armada.py --run 008
python visualize_armada.py --run 009
```

### Generate Specific Visualization Type

```bash
python visualize_armada.py --type phase      # Phase portrait
python visualize_armada.py --type vortex     # Polar drain view
python visualize_armada.py --type 3d         # 3D phase space basin
python visualize_armada.py --type stability  # Stability basin + histogram
python visualize_armada.py --type html       # Interactive Plotly HTML
```

### Combine Options

```bash
python visualize_armada.py --run 008 --type vortex
python visualize_armada.py --run 009 --type html
```

---

## Output Location

All outputs go to `visualizations/pics/run{ID}/`:

```
pics/
  run008/
    run008_phase_portrait.png
    run008_phase_portrait.svg
    run008_vortex.png
    run008_vortex.svg
    run008_3d_basin.png
    run008_3d_basin.svg
    run008_stability_basin.png
    run008_interactive_3d.html
    run008_interactive_vortex.html
  run009/
    ...
```

---

## Visualization Types Explained

| Type | What It Shows |
|------|---------------|
| **Phase Portrait** | Drift[N] vs Drift[N+1] - Flow direction in identity space |
| **Vortex/Drain** | Polar spiral - "Looking into the drain" from above |
| **3D Basin** | Full phase space with time axis - Attractor dynamics |
| **Stability Basin** | Baseline vs max drift + Event Horizon histogram |
| **Interactive HTML** | Plotly 3D - Rotate, zoom, hover for details |

---

## Dependencies

```bash
pip install matplotlib numpy scipy plotly
```

Plotly is optional (only needed for HTML exports).

---

## Data Sources

The script auto-detects JSON files from `../armada_results/`:

- `S7_run_008_*.json` - Run 008 (5D drift metric)
- `S7_run_009_*.json` - Run 009 drain capture
- Future runs will be auto-detected

---

## Troubleshooting

**"No runs found"**: Make sure JSON result files exist in `../armada_results/`

**Missing scipy**: `pip install scipy`

**No HTML output**: `pip install plotly`

---

See [README.md](README.md) for full technical documentation.
