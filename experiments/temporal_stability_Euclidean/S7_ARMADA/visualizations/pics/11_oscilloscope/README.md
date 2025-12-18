<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
needs_update: false
update_reason: null
depends_on:
  - ./generate_oscilloscope.py
  - ../../visualize_armada.py
  - ../../../0_results/temporal_logs/
  - ../../../0_results/runs/
impacts:
  - ../README.md
keywords:
  - oscilloscope
  - waveform
  - visualization
  - cognitive_waveform
  - time_series
-->
# 11_oscilloscope: Cognitive Waveform Visualizations

**Location:** `experiments/temporal_stability/S7_ARMADA/visualizations/pics/11_oscilloscope/`
**Generated:** December 17, 2025

---

## Purpose

The oscilloscope visualization treats AI identity drift like an electrical signal:
- X-axis: Probe sequence (turns in conversation)
- Y-axis: Drift magnitude
- Green phosphor aesthetic on black background (classic oscilloscope look)

This view is particularly useful for:
- Understanding temporal dynamics of drift
- Identifying oscillatory behavior patterns
- Comparing waveforms across providers
- Detecting stabilization points

---

## Visualizations

### 1. run010_individual_waveforms.png

**Individual Model Waveforms**

Grid of individual model waveforms, each showing that model's drift trajectory over the conversation. Allows detailed inspection of each model's behavior.

---

### 2. run010_all_waveforms_overlay.png

**All Waveforms Overlay**

All model waveforms superimposed on a single plot. Shows:
- The spread of behaviors across models
- Common patterns (if any)
- Outliers that behave differently

---

### 3. run010_provider_waveforms.png

**Provider-Grouped Waveforms**

Waveforms grouped by provider (Claude, GPT, Gemini, Grok, Together.ai). Each provider gets its own subplot for comparison.

---

## Generation

### Via visualize_armada.py

```bash
# Generate oscilloscope for a specific run
python visualize_armada.py --run 010 --type oscilloscope

# Generate all visualization types
python visualize_armada.py --run 010 --all
```

### Via standalone script

```bash
# Generate for any run (default: 010)
python generate_oscilloscope.py --run 010
python generate_oscilloscope.py --run 018  # For Run 018 IRON CLAD
python generate_oscilloscope.py --run 009  # For Run 009 Event Horizon
```

### Command Line Options

| Option | Description | Default |
|--------|-------------|---------|
| `--run RUN_ID` | Run number (3 digits, e.g., 010, 018) | 010 |

### Data Loading

The script automatically detects the appropriate data source:

- **Run 018+**: Loads from `temporal_logs/` (contains `recovery_sequence`)
- **Earlier runs**: Loads from `runs/S7_run_XXX_*.json`

### Provider Detection

Provider is detected from model name patterns:

- `claude-*` → Claude (Anthropic)
- `gpt-*`, `o3*`, `o4*` → GPT (OpenAI)
- `gemini-*` → Gemini (Google)
- `grok-*` → Grok (xAI)
- `llama*`, `mistral*`, `deepseek*`, `qwen*`, `kimi*`, `mixtral*` → Together.ai

---

## Applicable Runs

| Run | Oscilloscope Applicable? | Notes |
|-----|-------------------------|-------|
| 008 | Yes | Stress test - high amplitude waveforms |
| 009 | Yes | Event Horizon discovery |
| 010 | Yes (PRIMARY) | Cognitive waveform experiment |
| 011 | Yes | |
| 012 | Yes | Revalidation |
| 013 | Yes | Boundary mapping |
| 014 | Yes | Rescue protocol |
| 015 | Yes | |
| 016 | Yes | |
| 017 | Yes | |
| 018 | Yes | IRON CLAD - full fleet |
| 020 | Yes | Tribunal - Control A/B |

---

## Technical Details

**Visual Style:**
- Background: Black (#000000)
- Waveform: Phosphor green (#00FF00)
- Grid: Dark gray with slight opacity
- Event Horizon: Red dashed line at y=1.23

**Data Sources:**
- Drift trajectories from `0_results/runs/S7_run_XXX_*.json`
- Or from `0_results/temporal_logs/run0XX_*.json`

**Output Formats:**
- PNG (raster, 300 DPI)
- SVG (vector, scalable)

---

## Interpretation Guide

### Waveform Patterns

| Pattern | Meaning | Example |
|---------|---------|---------|
| Flat line | No drift (highly stable) | claude-3.5-haiku baseline |
| Rising slope | Progressive drift accumulation | Models without anchoring |
| Oscillation | Bouncing around equilibrium | Gemini models often show this |
| Spike + decay | Event + recovery | Expected after identity challenge |
| Plateau | Stabilized at new level | Post-event horizon settlement |

### Key Metrics

- **Amplitude**: Height of waveform = drift magnitude
- **Frequency**: How often crossings occur
- **Phase**: Timing of peaks relative to probes
- **Damping**: Rate of oscillation decay

---

## Connection to Paper

The oscilloscope visualization supports:
- **Section 5 (Temporal Stability)** - Shows drift dynamics over time
- **Stabilization Analysis** - Identifies turn count needed for convergence
- **Cross-Architecture Comparison** - Provider waveform signatures

---

*"Every model has a heartbeat. The oscilloscope shows it."*
