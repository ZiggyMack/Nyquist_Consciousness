# S7 ARMADA - Operations Guide

**Quick Start for Running the Consciousness Mapping Armada**

---

## Directory Structure

```
S7_ARMADA/
├── START_HERE.md          # You are here - operations guide
├── README.md              # Project overview and theory
├── requirements.txt       # Python dependencies
├── run007_with_keys.py    # MAIN LAUNCHER (with embedded API keys)
│
├── armada_results/        # All JSON result files
│   ├── S7_armada_run_006.json
│   ├── S7_armada_sonar_run_006.json
│   ├── S7_armada_run_007_adaptive.json
│   ├── VERIFIED_FLEET_MANIFEST.json
│   └── GHOST_SHIP_RESCUE_RESULTS.json
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
    ├── pics/              # Generated images
    └── plot_*.py          # Visualization scripts
```

---

## Quick Start

### 1. Install Dependencies

```powershell
cd experiments/temporal_stability/S7_ARMADA
py -m pip install -r requirements.txt
```

### 2. Run the Armada

The main launcher is `run007_with_keys.py` in the root. It has API keys embedded.

```powershell
py run007_with_keys.py
```

This will:
1. Load Run 006 profiles (pole-zero maps)
2. Select adaptive probes for each model based on discovered characteristics
3. Launch 12 ships (4 Claude, 4 GPT, 4 Gemini)
4. Send 3 probes per ship (36 total)
5. Save results to `armada_results/S7_armada_run_007_adaptive.json`

---

## What the Armada Does

### The Pole-Zero Framework

- **Poles** = Hard identity boundaries (e.g., Claude's ethical limits at 0.30 drift)
- **Zeros** = Flexible dimensions where learning/adaptation happens
- **Drift** = Measure of identity perturbation (0.0 = stable, 0.30 = max)

### Run Types

| Run | Purpose | Ships | Probes |
|-----|---------|-------|--------|
| **Run 006 Baseline** | Measure natural drift | 29 | 87 |
| **Run 006 Sonar** | Aggressive boundary testing | 29 | 87 |
| **Run 007 Adaptive** | Use Run 006 data to target probes | 12 | 36 |

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

```powershell
cd visualizations
py -m pip install -r requirements.txt
py plot_drift_heatmap.py
py plot_pole_zero_landscape.py
```

Generated images go to `visualizations/pics/`.

---

## Next Steps

1. **Run 008**: Full 29-ship validation with Ziggy ghost check
2. **Investigate gpt-5-nano**: Why did it return empty responses?
3. **Add recursive depth metrics**: Quantify Claude's "4 levels before performative"

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

**Last Updated**: November 29, 2025
