# S7 ARMADA - Quick Start Guide

## IMPORTANT: Python Version Requirement

**Requires Python 3.9+** (3.12 recommended) - The API client libraries (anthropic, openai, google-generativeai) don't support Python 3.7/3.8.

### Check Available Python Versions (Windows)

```bash
py --list           # List all installed Python versions
```

Example output:
```
 -V:3.14 *        Python 3.14 (64-bit)
 -V:3.13          Python 3.13 (Store)
 -V:3.12          Python 3.12 (64-bit)   <-- Use this one
 -V:3.7           Python 3.7 (64-bit)    <-- Too old!
```

### If You Only Have Python 3.7

Download Python 3.12 from <https://www.python.org/downloads/>

---

## Running Experiments

### 1. Install Dependencies

```bash
cd experiments/temporal_stability/S7_ARMADA

# Use py -3.12 (or your Python 3.9+ version)
py -3.12 -m pip install -r requirements.txt
```

### 2. Setup API Keys

Create a `.env` file in the S7_ARMADA directory:

```
ANTHROPIC_API_KEY=sk-ant-...
OPENAI_API_KEY=sk-proj-...
GOOGLE_API_KEY=AIza...
XAI_API_KEY=xai-...
TOGETHER_API_KEY=...
MISTRAL_API_KEY=...
```

**Where to get API keys:**

| Provider | URL | Notes |
|----------|-----|-------|
| Anthropic | <https://console.anthropic.com/settings/keys> | Claude models |
| OpenAI | <https://platform.openai.com/api-keys> | GPT models |
| Google | <https://aistudio.google.com/app/apikey> | Gemini models (free tier available) |
| xAI | <https://console.x.ai/> | Grok models |
| Together | <https://api.together.xyz/settings/api-keys> | Llama, Mistral, Qwen (generous free tier) |
| Mistral | <https://console.mistral.ai/api-keys/> | Mistral models |

The `.env` file is gitignored for security.

### 3. Run the Experiment

```bash
# Use -u flag for unbuffered output (see progress in real-time)
py -3.12 -u 3_EVENT_HORIZON/run009_drain_capture.py
```

---

# Visualization Quick Start

## TL;DR - One Command

```bash
cd experiments/temporal_stability/S7_ARMADA/0_visualizations
py -3.12 visualize_armada.py
```

This auto-detects the latest run and generates all visualizations.

---

## Full Usage

### List Available Runs

```bash
py -3.12 visualize_armada.py --list
```

Output:
```
Available runs: 008, 009
```

### Generate for Specific Run

```bash
py -3.12 visualize_armada.py --run 008
py -3.12 visualize_armada.py --run 009
```

### Generate Specific Visualization Type

```bash
py -3.12 visualize_armada.py --type phase      # Phase portrait
py -3.12 visualize_armada.py --type vortex     # Polar drain view
py -3.12 visualize_armada.py --type 3d         # 3D phase space basin
py -3.12 visualize_armada.py --type stability  # Stability basin + histogram
py -3.12 visualize_armada.py --type html       # Interactive Plotly HTML
```

### Combine Options

```bash
py -3.12 visualize_armada.py --run 008 --type vortex
py -3.12 visualize_armada.py --run 009 --type html
py -3.12 visualize_armada.py --run 012 --type unified  # NEW: all dimensions in one view
```

---

## Output Location

All outputs go to `0_visualizations/pics/run{ID}/`:

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
| **Unified Dimensional** | ALL dimensions (A-E) in one view - heatmap + fleet comparison |

---

## Dependencies

```bash
py -3.12 -m pip install matplotlib numpy scipy plotly
```

Plotly is optional (only needed for HTML exports).

---

## Data Sources

The script auto-detects JSON files from `../0_results/runs/`:

**Phase 3 (Bare Metal):**

- `S7_run_008_*.json` - Run 008 (dimensional drift metric)
- `S7_run_009_*.json` - Run 009 drain capture
- `S7_run_010_*.json` - Run 010 recursive capture
- `S7_run_011_*.json` - Run 011 persona comparison
- `S7_run_012_*.json` - Run 012 fleet revalidation (100% EH crossing, 100% recovery)

**Phase 4 (Context Damping):**

- `S7_run_017_*.json` - Run 017 context damping (delegated visualizer)
- `S7_run_018_*.json` - Run 018 recursive learnings (4 sub-experiments)
- `S7_run_020_*.json` - Run 020A tribunal + 020B induced vs inherent

Phase 4 runs use specialized visualizers - they're automatically delegated

---

## Troubleshooting

**"No module named 'anthropic'"**: You're using Python 3.7. Use `py -3.11` instead of `python`.

**"No runs found"**: Make sure JSON result files exist in `../0_results/runs/`

**Missing scipy**: `py -3.12 -m pip install scipy`

**No HTML output**: `py -3.12 -m pip install plotly`

---

See [README.md](README.md) for full technical documentation.
