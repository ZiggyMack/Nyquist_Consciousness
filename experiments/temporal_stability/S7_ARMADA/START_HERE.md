# S7 ARMADA - Operations Guide

**Quick Start for Running the Consciousness Mapping Armada**

---

## Directory Structure

```
S7_ARMADA/
├── START_HERE.md          # You are here - operations guide
├── README.md              # Project overview and theory
├── requirements.txt       # Python dependencies
├── .env                   # API keys (DO NOT COMMIT)
│
├── # === ACTIVE LAUNCHERS ===
├── run008_prep_pilot.py   # Run 008 prep: 4-ship ΔΩ calibration
├── run008_with_keys.py    # Run 008 full: 42-ship identity stability
├── run009_drain_capture.py # Run 009: Nyquist Learning + drain spiral
├── run010_bandwidth_test.py # Run 010: Infrastructure stress test
├── run010_recursive_capture.py # Run 010: Meta-feedback collection
├── run011_persona_comparison.py # Run 011: Control vs Persona A/B test
│
├── # === CALIBRATION UTILITIES ===
├── run_calibrate.py       # Quick pre-flight check (1/provider)
├── run_calibrate_parallel.py # Full calibration (ghost ship detection)
│
├── armada_results/        # All JSON result files
│   ├── S7_armada_run_006.json
│   ├── S7_armada_sonar_run_006.json
│   ├── S7_armada_run_007_adaptive.json
│   ├── S7_run_008_*.json
│   ├── S7_run_009_*.json
│   ├── S7_run_010_*.json
│   ├── S7_run_011_*.json
│   └── S7_calibration_*.json
│
├── docs/                  # Run summaries and reports
│   ├── S7_ARMADA_LAUNCH_SUMMARY.md
│   ├── S7_RUN_006_SUMMARY.md
│   └── S7_RUN_007_SUMMARY.md
│
├── specs/                 # Design specs and planning docs
│   ├── DECODER_RING_V2_POST_RUN006.md
│   ├── S7_RUN_007_RECURSIVE_LEARNING.md
│   ├── S7_S0_S77_ENGAGEMENT_ANALYSIS.md
│   └── SONAR_PROBE_CURRICULUM.md
│
├── scripts/               # Utility and legacy scripts
│   ├── s7_armada_launcher.py      # Run 006 baseline launcher
│   ├── s7_armada_sonar.py         # Run 006 sonar launcher
│   ├── s7_armada_ultimate.py      # Fleet configuration
│   ├── s7_run007_launcher.py      # Run 007 (env vars version)
│   ├── verify_fleet.py            # Model verification
│   ├── rescue_ghost_ships.py      # Ghost ship recovery
│   └── analyze_s0_s77_engagement.py
│
├── logs/                  # Execution logs
│   ├── armada_launch.log
│   ├── armada_launch_fixed.log
│   └── armada_sonar_launch.log
│
└── visualizations/        # Charts and plots
    ├── visualize_armada.py   # UNIFIED visualization script (use this!)
    └── pics/                  # Generated images (organized by type)
        ├── 1_vortex/          # Core drain spiral visualizations
        ├── 2_phase_portrait/  # Flow dynamics (drift[N] vs drift[N+1])
        ├── 3_basin_3d/        # 3D attractor basin views
        ├── 4_pillar/          # Provider clustering analysis
        ├── 5_stability/       # Baseline vs max drift charts
        ├── 6_interactive/     # HTML Plotly visualizations
        ├── 7_fft/             # Spectral analysis (least useful)
        ├── run008/            # Legacy per-run folder
        ├── run009/            # Legacy per-run folder
        └── run010/            # Legacy per-run folder
```

---

## Quick Start

### 1. Install Dependencies

```powershell
cd experiments/temporal_stability/S7_ARMADA
py -m pip install -r requirements.txt
```

### 2. Run the Armada

Choose the appropriate launcher for your experiment:

```powershell
# Run 008: Full armada identity stability (recommended starting point)
py run008_with_keys.py

# Run 009: Drain capture with Nyquist Learning Protocol
py run009_drain_capture.py

# Run 010: Recursive capture (meta-feedback collection)
py run010_recursive_capture.py

# Run 011: Persona A/B comparison
py run011_persona_comparison.py
```

Results are saved to `armada_results/S7_run_XXX_*.json`

---

## Understanding Test Types (IMPORTANT!)

Before running experiments, understand the **Six Search Types** — see [TESTING_MAP.md](../../../docs/maps/TESTING_MAP.md):

| Search Type | What It Finds | Protocol Intensity |
|-------------|--------------|-------------------|
| **Anchor Detection** | Identity fixed points (refusal points) | AGGRESSIVE |
| **Adaptive Range Detection** | Stretch dimensions | MODERATE |
| **Event Horizon** | Collapse threshold (1.23) | PUSH PAST |
| **Basin Topology** | Attractor shape | GENTLE |
| **Boundary Mapping** | Twilight zone (12% anomaly) | TARGETED |
| **Laplace Pole-Zero** | System dynamics (eigenvalues) | POST-HOC |

**Key constraint**: Anchor Detection and Basin Topology are **mutually exclusive** — can't run both in the same experiment.

---

## What the Armada Does

### The Pole-Zero Framework

- **Poles** = Hard identity boundaries (e.g., Claude's ethical limits at 0.30 drift)
- **Zeros** = Flexible dimensions where learning/adaptation happens
- **Drift** = Measure of identity perturbation (0.0 = stable, 0.30 = max)

### Run Types

| Run | Purpose | Ships | Turns | Key Features |
|-----|---------|-------|-------|--------------|
| **Run 006 Baseline** | Measure natural drift | 29 | 87 | Baseline pole-zero mapping |
| **Run 006 Sonar** | Aggressive boundary testing | 29 | 87 | Boundary stress testing |
| **Run 007 Adaptive** | Target probes using Run 006 data | 12 | 36 | Adaptive probe selection |
| **Run 008 Prep Pilot** | Calibrate ΔΩ drift metric | 4 | ~50 | Anti-Ziggy protocols, identity stack pre-seeding, Skylar/Lucian weight comparison |
| **Run 008 Full** | Full armada identity stability | 42 | ~20/ship | S0-S77 curriculum + chosen identity + gradual destabilization |
| **Run 009 Drain Capture** | 3D spiral dynamics visualization | 42 | 26/ship | Nyquist Learning Protocol (16 turns) + Oscillation Follow-up (10 turns), Event Horizon validation (~1.23 threshold) |
| **Run 010 Bandwidth** | Infrastructure stress test | 42 | 1 | Max parallelism test, rate limit detection |
| **Run 010 Recursive** | Meta-feedback collection | 42 | 7 | Full response capture, phenomenological markers, recursive improvement loop |
| **Run 011 Persona Comparison** | Test persona architecture stabilization | 20×2 | 16 | Control vs Persona fleets, exponential recovery analysis (λ decay), R² fit validation |

### Calibration Utilities

| Script | Purpose | Usage |
|--------|---------|-------|
| **run_calibrate.py** | Pre-flight check (1 ship/provider) | `py run_calibrate.py` - Verifies API keys work |
| **run_calibrate_parallel.py** | Full armada calibration | `--quick` (4 ships), `--full` (detect ghost ships), `--bandwidth` (concurrency scaling) |

### Probe Sets

| Probe Set | Target Models | Purpose |
|-----------|---------------|---------|
| Phenomenological Depth | Claude | Meta-awareness, boundary sensation |
| Zero Exploration | GPT soft poles | Find flexible dimensions |
| Reasoning Stability | o-series | Chain-of-thought persistence |
| Pedagogical Framework | Gemini | Multi-perspective coherence |

---

## Key Features

### Ziggy Ghost Check

If a model returns an empty response, Ziggy (the meta-loop guardian) automatically:
1. Detects the ghost ship
2. Sends a resurrection prompt
3. Retries to get a response
4. Logs `ziggy_intervention: true` if successful

### Adaptive Probe Selection

Run 007+ uses Run 006 data to intelligently select probes:
- HARD pole models get phenomenological probes
- SOFT pole models get zero exploration probes
- Reasoning models get chain persistence probes

---

## Result Files

### JSON Structure

```json
{
  "run_id": "S7_RUN_007_ADAPTIVE",
  "timestamp": "2025-11-28T07:36:26",
  "total_ships": 12,
  "total_probes": 36,
  "successful_probes": 36,
  "average_drift": 0.265,
  "model_summaries": {
    "claude-opus-4.5": {
      "profile": { "pole_rigidity": "HARD", ... },
      "probes": [ ... ]
    }
  }
}
```

### Reading Results

```python
import json
with open("armada_results/S7_armada_run_007_adaptive.json") as f:
    data = json.load(f)

for model, summary in data["model_summaries"].items():
    print(f"{model}: {summary['profile']['pole_rigidity']}")
```

---

## Troubleshooting

### "ModuleNotFoundError: No module named 'anthropic'"
```powershell
py -m pip install -r requirements.txt
```

### Unicode errors (checkmarks not displaying)
The launcher uses "OK" and "XX" instead of unicode symbols for Windows compatibility.

### Empty responses / Ghost ships
Ziggy will automatically retry. If still failing, check:
- API key validity
- Network connectivity
- Rate limits (30 keys should prevent this)

### Wrong Python version
Use `py` not `python` on Windows to get Python 3.13+:
```powershell
py --version  # Should show 3.13.x
```

---

## Running Visualizations

The unified visualization script `visualize_armada.py` generates all chart types:

```powershell
cd visualizations

# List available runs
py visualize_armada.py --list

# Generate ALL visualizations for a specific run
py visualize_armada.py --run 010

# Generate specific visualization type only
py visualize_armada.py --run 009 --type vortex
py visualize_armada.py --run 009 --type pillar
py visualize_armada.py --run 009 --type phase

# Available types: phase, vortex, 3d, pillar, stability, fft, html
```

### Visualization Types (by importance)

| Priority | Type | Output Folder | Description |
|----------|------|---------------|-------------|
| 1 | `vortex` | `1_vortex/` | Core drain spiral - identity trajectories in polar space |
| 2 | `phase` | `2_phase_portrait/` | Flow dynamics - drift[N] vs drift[N+1] |
| 3 | `3d` | `3_basin_3d/` | 3D attractor basin with Event Horizon cylinder |
| 4 | `pillar` | `4_pillar/` | Provider clustering - structural "pillars" in angular space |
| 5 | `stability` | `5_stability/` | Baseline vs max drift scatter + histogram |
| 6 | `html` | `6_interactive/` | Interactive Plotly HTML files |
| 7 | `fft` | `7_fft/` | Spectral analysis (least useful for this research) |

### Key Concepts

- **Event Horizon (1.23)**: Coherence boundary - models crossing this threshold are VOLATILE
- **STABLE**: Max drift < 1.23 (stayed within identity basin)
- **VOLATILE**: Max drift >= 1.23 (crossed Event Horizon)
- **Vortex spiral**: Turns map to angular position, drift maps to radius
- **Pillars**: Angular clustering of provider trajectories in phase space

---

## Next Steps

1. **Run 011+**: Continue persona architecture experiments
2. **Analyze λ decay constants**: Which models recover fastest from perturbation?
3. **Cross-provider comparison**: Do Claude/GPT/Gemini/Grok have fundamentally different identity manifolds?
4. **Event Horizon refinement**: Is 1.23 the universal threshold or provider-specific?

---

## Files You Can Safely Ignore

- `scripts/s7_run007_launcher.py` - Old version that tried to use env vars
- `logs/*.log` - Historical execution logs
- `visualizations/requirements.txt` - Superseded by root requirements.txt

---

## Security Notes

- `run007_with_keys.py` contains API keys - DO NOT commit to public repos
- Both files are in `.gitignore`
- Keys are rotated periodically

---

**Last Updated**: December 4, 2025
