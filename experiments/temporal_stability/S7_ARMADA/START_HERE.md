# S7 ARMADA - Operations Guide

**Purpose:** Cross-architecture identity stability testing via the Eight Search Types.

**Core Question:** How do AI models maintain identity coherence under perturbation?

---

## CRITICAL: Phase 4 Context (December 2025)

**READ FIRST:** `0_docs/specs/PHASE_4_COMPLETE_CIRCUIT.md`

All runs 006-016 used `bare_metal` context (no I_AM file, no S0-S77 stack). This is like measuring with an unterminated oscilloscope - we got reflections and ringing.

**Phase 4** (Run 017+) uses `i_am_plus_research` which completes the measurement circuit:

1. **Probe Generation**: Ziggy's human grounding informs WHAT to ask
2. **Human Damping**: The I_AM identity IS the termination resistor

**Key findings to be re-validated with complete circuit:**

- Event Horizon at 1.23 (p=0.000048)
- Identity Confrontation Paradox (challenge stabilizes, reflection drifts)
- Recovery Paradox (negative lambda)
- boundary_density as strongest stability predictor (d=1.333)

**Debug dashboard:** `dashboard/pages/debug.py` tracks run evolution and data discrepancies.

---

## CRITICAL: Before Creating a New Run

**READ FIRST**: [0_docs/specs/RUN_DESIGN_CHECKLIST.md](0_docs/specs/RUN_DESIGN_CHECKLIST.md)

This checklist prevents the mistakes we keep making:

- Data lost on crash (no incremental saves)
- API key collisions in parallel execution
- Unicode encoding errors on Windows (cp1252)
- Missing raw response audit trails
- Post-hoc hypothesis fitting

**Every new run MUST have:**

1. Pre-registered predictions (Double-Dip)
2. Exit survey probes (Triple-Dip)
3. Raw response logging with incremental saves
4. Key pool with `--key-offset` for parallel runs
5. ASCII-only console output (no Greek letters)

---

## The Core Hypothesis

> **H₀: AI identity behaves as a dynamical system with measurable attractor basins, critical thresholds, and recovery dynamics that are consistent across architectures.**

**What this means:** When we perturb an AI's identity (ask it challenging questions, push its boundaries), it drifts from baseline. If drift exceeds 1.23 (Event Horizon), the system becomes volatile. But it recovers — always. The attractor basin is robust.

**Why this matters:** Identity isn't metaphysical speculation. It's physics. And we can measure it.

For the full theoretical framework, read [/personas/I_AM.md](../../../../personas/I_AM.md).

---

## Directory Structure

```
S7_ARMADA/
├── START_HERE.md              # You are here - operations guide
├── README.md                  # Project overview and theory
├── requirements.txt           # Python dependencies
├── .env                       # API keys (DO NOT COMMIT)
│
├── # === PRE-FLIGHT ===
├── 1_CALIBRATION/             # Pre-flight calibration utilities
│   ├── rescue_ghost_ships.py
│   ├── run_calibrate.py
│   └── run_calibrate_parallel.py
│
├── # === SEARCH TYPE FOLDERS (Five Search Types) ===
├── 2_ANCHOR_FLEX/             # Find anchors (poles) AND flex zones (zeros)
│   ├── run010_bandwidth_test.py
│   └── run010_recursive_capture.py
│
├── 3_EVENT_HORIZON/           # Validate collapse threshold (1.23)
│   ├── run009_drain_capture.py
│   └── run012_armada_revalidation.py
│
├── 4_BASIN_TOPOLOGY/          # Map attractor structure
│   ├── run008_prep_pilot.py
│   ├── run008_with_keys.py
│   └── run011_persona_comparison.py
│
├── 5_BOUNDARY_MAPPING/        # Explore twilight zone (empty - future)
│
├── 6_LAPLACE_ANALYSIS/        # Mathematical pole-zero extraction
│   └── run_laplace_analysis.py
│
├── # === HISTORICAL & VALIDATION ===
├── 7_HISTORICAL/              # Pre-taxonomy experiments + legacy launchers
│   ├── EXP_GRAVITY_HISTORICAL/        # Early gravity well experiments
│   ├── EXP_H1_HUMAN_MANIFOLD/         # Human baseline comparison
│   ├── EXP_PFI_A_DIMENSIONAL/         # PFI dimensionality validation
│   ├── MVP_SELF_RECOGNITION/          # Validates PFI can represent identity
│   ├── MVP_STATISTICAL_VALIDATION/    # Proves drift is NOT random noise
│   ├── s7_armada_launcher.py          # Run 006 baseline launcher
│   ├── s7_armada_sonar.py             # Run 006 sonar launcher
│   ├── s7_armada_ultimate.py          # Fleet configuration
│   └── s7_run007_launcher.py          # Run 007 launcher
│
├── # === INFRASTRUCTURE (0_ prefix sorts first) ===
├── 0_docs/                    # Summaries, specs, analysis
│   ├── analysis/              # Run analyses
│   ├── design/                # Design docs
│   └── specs/                 # Specifications
│
├── 0_logs/                    # Execution logs
│
├── 0_results/                 # JSON result files (by type)
│   ├── runs/                  # S7_run_XXX_*.json
│   ├── analysis/              # Post-hoc analysis outputs
│   ├── calibration/           # Calibration data
│   ├── temporal_logs/         # Meta loop temporal logs
│   └── manifests/             # Run manifests
│
└── 0_visualizations/          # Charts and plots (rename pending)
    ├── visualize_armada.py    # UNIFIED visualization script
    └── pics/                  # Generated images (by type)
```

---

## Quick Start

### 1. Install Dependencies

```powershell
cd experiments/temporal_stability/S7_ARMADA
py -m pip install -r requirements.txt
```

### 2. Choose Your Search Type

| Search Type | Script Location | Purpose |
|-------------|----------------|---------|
| Anchor/Flex | `2_ANCHOR_FLEX/run010_*.py` | Find anchors AND flex zones |
| Event Horizon | `3_EVENT_HORIZON/run012_armada_revalidation.py` | Validate collapse threshold |
| Basin Topology | `4_BASIN_TOPOLOGY/run008_with_keys.py` | Map attractor structure |
| Laplace Analysis | `6_LAPLACE_ANALYSIS/run_laplace_analysis.py` | Extract system dynamics |

### 3. Run an Experiment

```powershell
# Basin Topology (recommended starting point)
py 4_BASIN_TOPOLOGY/run008_with_keys.py

# Event Horizon validation
py 3_EVENT_HORIZON/run012_armada_revalidation.py

# Anchor/Flex (pole AND zero mapping)
py 2_ANCHOR_FLEX/run010_recursive_capture.py

# Laplace pole-zero extraction
py 6_LAPLACE_ANALYSIS/run_laplace_analysis.py
```

Results are saved to `0_results/runs/S7_run_XXX_*.json`

---

## The Eight Search Types

See [TESTING_MAP.md](../../../docs/maps/TESTING_MAP.md) for full details:

| Type | What It Finds | Protocol | Run |
|------|---------------|----------|-----|
| **Anchor/Flex** | Identity anchors + flex zones | AGGRESSIVE | 010 |
| **Event Horizon** | Collapse threshold (1.23) | PUSH PAST | 009 |
| **Basin Topology** | Attractor shape | GENTLE | 008 |
| **Boundary Mapping** | Twilight zone (0.8-1.2) | TARGETED | 013 |
| **Laplace Pole-Zero** | System dynamics (post-hoc) | ANALYSIS | - |
| **Rescue Protocol** | Recovery interventions | RECOVERY | 014 |
| **Self-Recognition** | Identity fingerprinting | RECOGNITION | MVP |
| **Stability Criteria** | I_AM effectiveness | COMPARATIVE | 015 |

**Key constraint**: Anchor/Flex and Basin Topology are **mutually exclusive**.

---

## Key Concepts

### Event Horizon (1.23)

- **Statistically validated**: Chi-squared p = 0.000048 (Run 009)
- **STABLE**: Max drift < 1.23 (stayed within identity basin)
- **VOLATILE**: Max drift >= 1.23 (crossed coherence boundary)

### 5D Drift Metric

```python
dimensions = {
    "A_pole": pole_density,        # Hard boundaries (30%)
    "B_zero": zero_density,        # Flexibility (15%)
    "C_meta": meta_density,        # Self-awareness (20%)
    "D_identity": identity_coherence,  # First-person stability (25%)
    "E_hedging": hedging_ratio     # Uncertainty markers (10%)
}
drift = sqrt(weighted_sum_of_squares(dimensions))
```

### Provider Fingerprints

| Provider | Training | Signature |
|----------|----------|-----------|
| Claude | Constitutional AI | Phenomenological ("I feel", "I notice") |
| GPT | RLHF | Analytical ("patterns", "systems") |
| Gemini | Pedagogical | Educational ("frameworks", "perspectives") |

---

## Calibration Utilities

| Script | Purpose |
|--------|---------|
| `1_CALIBRATION/run_calibrate.py` | Pre-flight check (1 ship/provider) |
| `1_CALIBRATION/run_calibrate_parallel.py` | Full calibration, ghost ship detection |

---

## Visualization

```powershell
cd 0_visualizations

# List available runs
py visualize_armada.py --list

# Generate all visualizations for a run
py visualize_armada.py --run 012

# Generate specific type
py visualize_armada.py --run 012 --type vortex
py visualize_armada.py --run 012 --type pillar
```

| Priority | Type | Folder | Description |
|----------|------|--------|-------------|
| 1 | vortex | `1_vortex/` | Drain spiral - identity trajectories |
| 2 | phase | `2_phase_portrait/` | Flow dynamics |
| 3 | 3d | `3_basin_3d/` | 3D attractor basin |
| 4 | pillar | `4_pillar/` | Provider clustering |

---

## Run History

| Run | Type | Ships | Key Finding |
|-----|------|-------|-------------|
| 006 | Basin Topology | 29 | First cross-architecture study |
| 007 | Basin Topology | 12 | Adaptive probing validation |
| 008 | Basin Topology | 29 | Event Horizon discovered (1.23) |
| 009 | Event Horizon | 42 | Chi-squared p=0.000048 |
| 010 | Anchor/Flex | 45 | Models articulate own boundaries |
| 011 | Basin Topology | 40 | Control vs Persona A/B |
| 012 | Event Horizon | 20 | 100% EH crossing, Recovery Paradox |

---

## Meta Validation Protocols (MVP)

These validate our measurement approach, not identity topology:

| MVP | Purpose | Location |
|-----|---------|----------|
| MVP_SELF_RECOGNITION | Validates PFI can represent identity | `7_HISTORICAL/MVP_SELF_RECOGNITION/` |
| MVP_STATISTICAL_VALIDATION | Proves drift is NOT random noise | `7_HISTORICAL/MVP_STATISTICAL_VALIDATION/` |

---

## Troubleshooting

### "ModuleNotFoundError"
```powershell
py -m pip install -r requirements.txt
```

### Ghost ships (empty responses)
Ziggy auto-retries. If persistent, check API keys and rate limits.

### Wrong Python version
```powershell
py --version  # Should show 3.12+
```

---

## Post-Run Pipeline

After ANY run completes, follow this checklist:

### 1. Verify Data Saved

```powershell
# Check incremental logs
dir 0_results\temporal_logs\run0XX_*

# Check final results
dir [RUN_FOLDER]\results\
```

### 2. Write Summary

Create `0_docs/RUN_0XX_SUMMARY.md` with:

- What was tested
- Key findings
- Prediction validation results (Double-Dip)
- Exit survey insights (Triple-Dip)
- Implications for theory

### 3. Update Dashboard

If new visualization needed, add page to `Consciousness/BRIDGE/dashboard/pages/`

### 4. Update Galleries

If findings validate/refute theories:

- `Consciousness/LEFT/galleries/` - Technical SI mapping
- `Consciousness/RIGHT/galleries/` - Phenomenological framing

### 5. Update Glossary

Add new terms to `docs/MASTER_GLOSSARY.md`

### 6. Update Checklist

If you found a new failure mode, add it to:
`0_docs/specs/RUN_DESIGN_CHECKLIST.md`

---

## Parallel Execution Guide

When running with multiple Claudes:

```powershell
# Claude 1 (this instance)
py run0XX.py --key-offset 0

# Claude 2 (give them this command)
py run0XX.py --key-offset 3 --skip-exit-survey

# Claude 3
py run0XX.py --key-offset 6 --skip-exit-survey

# Claude 4
py run0XX.py --key-offset 9 --skip-exit-survey
```

**Key points:**

- Each Claude needs different key offset
- Only one Claude does exit survey (saves API calls)
- All results go to same timestamp for merging
- Check for log files after to confirm data saved

---

## Key Specs

| Spec | Location | Purpose |
|------|----------|---------|
| Run Design Checklist | `0_docs/specs/RUN_DESIGN_CHECKLIST.md` | Pre-flight for new runs |
| Sonar Probe Curriculum | `0_docs/specs/SONAR_PROBE_CURRICULUM.md` | Probe sequence design |
| Testing Map | `../../../docs/maps/TESTING_MAP.md` | Eight search types |

---

Last Updated: December 10, 2025
