<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-21
depends_on:
  - visualize_armada.py
  - ../15_IRON_CLAD_FOUNDATION/run023c_visualization_generator.py
  - ../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json
keywords:
  - visualization
  - iron_clad
  - cosine
  - event_horizon
  - quick_start
-->
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
```

**Where to get API keys:**

| Provider | URL | Models Available |
|----------|-----|------------------|
| Anthropic | <https://console.anthropic.com/settings/keys> | Claude (Opus, Sonnet, Haiku) |
| OpenAI | <https://platform.openai.com/api-keys> | GPT-4, GPT-4o, o1 |
| Google | <https://aistudio.google.com/app/apikey> | Gemini (free tier available) |
| xAI | <https://console.x.ai/> | Grok |
| Together | <https://api.together.xyz/settings/api-keys> | Llama, Mistral, Qwen, DeepSeek (generous free tier) |

**Note:** Together.ai is a hosting platform that provides access to many open-source models through a single API key. This includes Mistral, Llama, Qwen, DeepSeek, and others.

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

All outputs go to `visualizations/pics/` organized by CONCEPT (not run number):

```
pics/
  1_Vortex/                    # Drift spiral dynamics
  2_Boundary_Mapping/          # Phase portraits + 3D basins
  3_Stability/                 # Pillar analysis + stability basins
  4_Rescue/                    # Recovery dynamics
  5_Settling/                  # Settling time curves
  6_Architecture/              # Provider signatures
  7_Radar/                     # PFI dimensional analysis
  8_Oscilloscope/              # Time-series drift views
  9_FFT_Spectral/              # Frequency analysis
  10_PFI_Dimensional/          # Conceptual explanations
  11_Unified_Dashboard/        # Per-ship multi-panel dashboards
  12_Metrics_Summary/          # Fleet-wide metrics comparison
```

**Note:** Visualizations are organized by concept, not per-run.
One representative visualization per concept (typically from run009 or run023b).

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

The script auto-detects JSON files from `../0_results/runs/` and `../15_IRON_CLAD_FOUNDATION/results/`:

**Current IRON CLAD Runs (Cosine Methodology, EH=0.80):**

- `S7_run_023b_*.json` - Run 023b IRON CLAD foundation (25 ships x 30 iterations)
- `S7_run_023c_*.json` - Run 023c cosine migration (re-runs 009-018 with cosine)

**Legacy Runs (Archived - see .archive/temporal_stability_Euclidean/):**

- Runs 008-012 used keyword RMS (Event Horizon 1.23)
- These are preserved for historical reference but not used for new analysis

**Specialized Visualizers:**

- Run 015 (Stability) -> `9_STABILITY_CRITERIA/visualize_run015.py`
- Run 016 (Settling) -> `10_SETTLING_TIME/visualize_run016.py`
- Run 018 (Context Damping) -> `11_CONTEXT_DAMPING/visualize_run018.py`

These are automatically delegated by `visualize_armada.py`

---

## Troubleshooting

**"No module named 'anthropic'"**: You're using Python 3.7. Use `py -3.11` instead of `python`.

**"No runs found"**: Make sure JSON result files exist in `../0_results/runs/`

**Missing scipy**: `py -3.12 -m pip install scipy`

**No HTML output**: `py -3.12 -m pip install plotly`

---

See [README.md](README.md) for full technical documentation.

---

**Last Updated**: December 21, 2025
**Methodology**: Cosine distance (Event Horizon = 0.80, calibrated from Run 023b P95)
