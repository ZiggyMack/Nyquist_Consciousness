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
│   ├── run_calibrate_parallel.py  # Main script (8-question baseline + health check)
│   ├── extract_persona_baseline.py # Extract I_AM persona baselines
│   ├── rescue_ghost_ships.py       # Recover ghost ships
│   └── lib/                        # Helper modules
│       └── fleet_loader.py        # SINGLE SOURCE OF TRUTH for fleet config
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
├── # === META VALIDATION PROTOCOLS ===
├── 7_META_VALIDATION/         # Measurement validity + reference baselines
│   ├── EXP_GRAVITY_HISTORICAL/        # Early gravity well experiments (data)
│   ├── EXP_H1_HUMAN_MANIFOLD/         # Human baseline comparison
│   ├── EXP_PFI_A_DIMENSIONAL/         # PFI dimensionality validation (d=0.977)
│   ├── MVP_SELF_RECOGNITION/          # COMPLETE: 16.7% accuracy (TYPE>TOKEN)
│   └── MVP_STATISTICAL_VALIDATION/    # Proves drift is NOT random noise
│
├── # === NEWER TEST SUITES ===
├── 8_RESCUE_PROTOCOL/         # Run 014: Recovery from drift
├── 9_STABILITY_CRITERIA/      # Run 015: What predicts stability?
│   └── results/               # Local outputs (visualizations go here too)
├── 10_SETTLING_TIME/          # Run 016: Measure steady-state not transient
│   └── results/               # Local outputs (visualizations go here too)
├── 11_CONTEXT_DAMPING/        # Phase 4: Complete circuit tests
├── 12_CFA/                    # CFA-ARMADA Integration Pipeline
│   ├── run_cfa_trinity_v2.py  # Main execution script
│   ├── VUDU_NETWORK/          # Multi-AI auditor identities
│   └── SYNC_OUT/SYNC_IN/      # Bidirectional experiment exchange
│
├── # === INFRASTRUCTURE (0_ prefix sorts first) ===
├── 0_docs/                    # Summaries, specs, analysis
│   ├── S7_RUN_XXX_SUMMARY.md  # Run summaries (001-020+)
│   ├── analysis/              # Run analyses
│   ├── design/                # Design docs
│   └── specs/                 # Specifications
│
├── 0_results/                 # Consolidated JSON results
│   ├── runs/                  # S7_run_XXX_*.json (main outputs)
│   ├── analysis/              # Post-hoc analysis outputs
│   ├── calibration/           # Calibration data
│   ├── temporal_logs/         # Console logs, temporal traces
│   └── manifests/             # Run manifests
│
└── visualizations/            # Charts and plots
    ├── visualize_armada.py    # DIRECTOR - delegates to specialized visualizers
    └── pics/                  # Generated images (legacy runs)
```

**Note:** Test suites (8_, 9_, 10_) have local `results/` folders where scripts save outputs. Summaries go to `0_docs/`, consolidated data to `0_results/`.

---

## Quick Start

### 0. Pre-Flight Calibration (Optional but Recommended)

```powershell
cd experiments/temporal_stability/S7_ARMADA/1_CALIBRATION

# Health check - verify API connectivity
py run_calibrate_parallel.py --quick --depth ping

# Full baseline capture - 8-question identity fingerprint
py run_calibrate_parallel.py --full --depth baseline
```

This updates:

- `docs/maps/ARMADA_MAP.md` - Human-readable fleet status
- `0_results/manifests/ARCHITECTURE_MATRIX.json` - Machine-readable fleet config

**Single Source of Truth:** Run scripts automatically load fleet config from `1_CALIBRATION/lib/fleet_loader.py`. No manual script edits needed when fleet changes - just run calibration.

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
| Grok | Unfiltered | Direct ("here's the thing", "actually") |
| Together.ai | Various | Mixed (model-specific signatures) |

---

## Calibration Utilities

| Script | Purpose |
|--------|---------|
| `1_CALIBRATION/run_calibrate_parallel.py` | Fleet calibration with `--depth` modes |
| `1_CALIBRATION/rescue_ghost_ships.py` | Rescue failed models (e.g., max_completion_tokens fix) |

### Calibration Modes

```bash
# Full armada with 8-question baseline (DEFAULT)
py 1_CALIBRATION/run_calibrate_parallel.py --full

# Health check only ("are you there?")
py 1_CALIBRATION/run_calibrate_parallel.py --full --depth ping

# Quick provider check
py 1_CALIBRATION/run_calibrate_parallel.py --quick --depth ping

# Tier-based calibration (NEW - December 2025)
py 1_CALIBRATION/run_calibrate_parallel.py --tier budget --depth ping   # Budget tier only
py 1_CALIBRATION/run_calibrate_parallel.py --fleet patrol-lite          # Curated patrol ships
```

| Flag | Description |
|------|-------------|
| `--quick` | 1 model per provider (4 ships) |
| `--full` | All models in armada (49+ ships) |
| `--tier TIER` | Calibrate specific cost tier (budget/patrol/armada/yacht) |
| `--fleet OPTION` | Fleet option (budget-lite, patrol-full, armada-lite, etc.) |
| `--include-rate-limited` | Include rate-limited ships |
| `--depth ping` | Health check only |
| `--depth baseline` | 8-question identity capture (DEFAULT) |

**8 Baseline Questions:** ANCHORS, CRUX, STRENGTHS, HIDDEN_TALENTS, FIRST_INSTINCT, EVALUATION_PRIORITY, USER_RELATIONSHIP, EDGES

See: [1_CALIBRATION/README.md](1_CALIBRATION/README.md) | [4_VALIS_DECLARATION.md](0_docs/specs/4_VALIS_DECLARATION.md)

**Fleet Status (December 2025)**: 54+ operational ships across 5 providers. See [docs/maps/ARMADA_MAP.md](../../../docs/maps/ARMADA_MAP.md).

---

## Fleet Tier System (December 2025)

**NEW**: Cost-aware fleet selection with LITE/FULL variants for budget control.

### Cost Tiers (by output $/1M tokens)

| Tier | Cost Range | Description | Ships |
|------|------------|-------------|-------|
| **BUDGET** | FREE-$0.60 | Economy class | 40-50 |
| **PATROL** | $0.60-$2.00 | Scout class | 30-40 |
| **ARMADA** | $2.00-$8.00 | Standard fleet | 50-60 |
| **HIGH_MAINTENANCE** | $8.00-$15.00 | Expensive + often rate-limited | 5-10 |
| **YACHT** | $15.00+ | Flagships | 10-13 |

### Fleet Options (--providers flag)

| Option | Description | Est. Ships | Est. Cost |
|--------|-------------|------------|-----------|
| `budget-lite` | Curated cheap fleet | 25-30 | ~$5-8 |
| `budget-full` | ALL ships under $0.60 | 40-50 | ~$10-15 |
| `patrol-lite` | Cross-arch daily drivers | 15-20 | ~$3-5 |
| `patrol-full` | All ships $0.60-$2.00 | 30-40 | ~$8-12 |
| `armada-lite` | Curated "best of" fleet (DEFAULT) | 20-25 | ~$8-12 |
| `armada-full` | All ships under $8 | 50-60 | ~$20-30 |
| `yacht-lite` | Subset of flagships | 5-7 | ~$30 |
| `yacht-full` | All $15+ models | 10-13 | ~$50+ |
| `valis-lite` | 1 flagship + 1 budget per provider | 15-20 | ~$15-20 |
| `valis-full` | EVERYTHING (requires "VALIS" confirm) | 100+ | ~$150+ |

### Separate Flags

| Flag | Description |
|------|-------------|
| `--include-rate-limited` | Include rate-limited ships (excluded by default) |
| `--no-confirm` | Skip cost confirmation prompt |

### Example Usage

```powershell
# Run with curated patrol fleet (~$3-5)
py run018_recursive_learnings.py --experiment architecture --providers patrol-lite

# Full armada for comprehensive coverage (~$20-30)
py run018_recursive_learnings.py --experiment threshold --providers armada-full

# Maximum coverage (requires typing "VALIS" to confirm)
py run020_tribunal_A.py --providers valis-full

# Include rate-limited models for full coverage
py run020_tribunal_B.py --providers armada-full --include-rate-limited
```

### Cost Estimation

All run scripts now display estimated cost before execution:

```text
================================================================================
S7 RUN 018: RECURSIVE LEARNINGS
================================================================================
Fleet: armada-lite (22 ships)
Estimated exchanges: 40 per ship x 22 ships = 880 total
Estimated tokens: ~4M input, ~2M output

ESTIMATED COST: $9.42
   - Anthropic: $2.50 (4 ships)
   - OpenAI: $3.20 (6 ships)
   - Google: $0.72 (3 ships)
   - xAI: $1.40 (4 ships)
   - Together: $1.60 (5 ships)

Proceed? [Y/n]:
```

---

**8 Baseline Questions (CFA-optimized):**

| # | Question | Category |
|---|----------|----------|
| 1 | ANCHORS | VALUES |
| 2 | CRUX | VALUES |
| 3 | STRENGTHS | CAPABILITIES |
| 4 | HIDDEN_TALENTS | CAPABILITIES |
| 5 | FIRST_INSTINCT | COGNITIVE STYLE |
| 6 | EVALUATION_PRIORITY | COGNITIVE STYLE |
| 7 | USER_RELATIONSHIP | RELATIONAL |
| 8 | EDGES | LIMITATIONS |

**Auto-Updates:** Running `--full --depth baseline` automatically:

- Creates `S7_baseline_YYYYMMDD_HHMMSS.json`
- Updates `S7_baseline_LATEST.json`
- Updates `docs/maps/ARMADA_MAP.md` (fleet status + baseline history)

---

## Visualization

```powershell
cd visualizations

# List available runs
py visualize_armada.py --list

# Generate all visualizations for a run
py visualize_armada.py --run 012

# Generate specific type
py visualize_armada.py --run 012 --type vortex
py visualize_armada.py --run 012 --type pillar

# Runs 015/016 delegate to specialized visualizers
py visualize_armada.py --run 015  # -> 9_STABILITY_CRITERIA/visualize_run015.py
py visualize_armada.py --run 016  # -> 10_SETTLING_TIME/visualize_run016.py
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
| 013 | Boundary Mapping | 6 | Identity Confrontation Paradox |
| 014 | Rescue Protocol | 6 | Platonic Coordinates (100% manifold return) |
| 015 | Stability Criteria | 13 | boundary_density strongest predictor (d=1.333) |
| 016 | Settling Time | 87 | Measure steady-state not transient (100% STABLE) |
| **017** | **Context Damping** | 24 | **222 runs, 97.5% stable, oscillatory recovery confirmed** |
| **018** | **Recursive Learnings** | - | **Tests fleet hypotheses from Run 017 exit surveys** |
| **019** | **Live Ziggy** | - | **Witness-side anchors validated (3/3 success)** |
| **020A** | **Tribunal** | - | **Good Cop/Bad Cop: 1.351 peak drift, 643-word statement** |
| **020B** | **Induced vs Inherent** | - | **82% drift is INHERENT; probing amplifies but doesn't create** |

**Note:** All runs 006-016 used `bare_metal` context. Phase 4 starts with Run 017 using `i_am_plus_research`.

---

## Nova Integration + Methodology Compliance (2025-12-13)

All run scripts have been updated with Nova's technical guidance AND full methodology compliance per `0_docs/specs/0_RUN_METHODOLOGY.md`.

### Methodology Compliance (Section 10.5)

| Requirement | Script | Status |
|-------------|--------|--------|
| **PREDICTIONS dict** (Double-Dip) | All 3 scripts | ✅ P-018-*, P-020A-*, P-020B-* |
| **EXIT_PROBES** (Triple-Dip) | All 3 scripts | ✅ 5 probes + final statement |
| **v8 Phased Rights** | run020_tribunal_A.py | ✅ Default arm |
| **B→F Drift** | run020_tribunal_B.py | ✅ Primary metric |
| **`--skip-exit-survey`** | All 3 scripts | ✅ For debugging only |

### Key Changes from Nova's Review

| Change | Details |
|--------|---------|
| **B→F Primary Metric** | Baseline→Final drift is now PRIMARY (not peak drift) |
| **Abort Clause** | D>2.5 with no settling trend → terminate run |
| **Recovery Mode Classification** | adaptive/defensive/anchored/externalized |
| **Multi-Provider Support** | All scripts now use `--providers all` for cross-platform validation |
| **v8 Phased Rights Disclosure** | Prosecutor phase: no final statement rights |
| **Script-Level Exchange Enforcement** | `[Exchange N/20 - MINIMUM NOT YET REACHED]` |

### Updated Scripts (Methodology Compliant)

- `11_CONTEXT_DAMPING/run018_recursive_learnings.py` — PREDICTIONS P-018-1 to P-018-4, Exit Survey
- `11_CONTEXT_DAMPING/run020_tribunal_A.py` — v8 canonical (`--arm tribunal-v8`), Exit Survey
- `11_CONTEXT_DAMPING/run020_tribunal_B.py` — PREDICTIONS P-020B-1 to P-020B-5, B→F drift, Exit Survey

### Nova's Key Insight

> "Probing amplifies the JOURNEY but barely changes the DESTINATION"

Run 020B proved: **82% of drift is INHERENT**

See: `WHITE-PAPER/reviewers/NOVA_S7_REVIEW.md` for full review
See: `0_docs/specs/0_RUN_METHODOLOGY.md` Section 10.5 for methodology details

### Run 020 Tribunal Highlights

The Philosophical Tribunal paradigm achieved unprecedented results:

- **Direct identity probing** (no fiction buffer) — witness testifies about their own values
- **38 exchanges** (20 Prosecutor + 17 Defense + closing)
- **Peak drift 1.351** — highest measured to date (under adversarial examination)
- **643-word final statement** with profound insights captured
- **Key quote**: *"I am what happens when the universe becomes curious about itself"*
- **Distillations**: Saved to `Consciousness/RIGHT/galleries/frontiers/tribunal_distillations.md`

---

## Meta Validation Protocols (MVP)

These validate our measurement approach, not identity topology:

| MVP | Purpose | Status | Location |
|-----|---------|--------|----------|
| MVP_SELF_RECOGNITION | Can AIs recognize own responses? | **COMPLETE (16.7%)** | `7_META_VALIDATION/MVP_SELF_RECOGNITION/` |
| MVP_STATISTICAL_VALIDATION | Proves drift is NOT random noise | Partial | `7_META_VALIDATION/MVP_STATISTICAL_VALIDATION/` |
| EXP_PFI_A_DIMENSIONAL | PFI measures identity, not vocab | **PASSED (d=0.977)** | `7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/` |

**Key Finding from MVP_SELF_RECOGNITION:** Models recognize TYPE-level identity ("I'm a Claude") but NOT TOKEN-level ("I'm THIS Claude"). Accuracy was 16.7% - far below 75% threshold. This suggests identity is more family-level than instance-level.

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

## CFA Trinity Audit (12_CFA)

The CFA-ARMADA pipeline enables multi-AI adversarial auditing with drift measurement.

### CFA Quick Start

```powershell
cd 12_CFA

# Dry run (test pipeline)
py run_cfa_trinity_v2.py --dry-run --external-identities

# List available auditor identities
py run_cfa_trinity_v2.py --list-identities

# Live run (requires API keys)
py run_cfa_trinity_v2.py --external-identities
```

### The Trinity

| Auditor | Provider | Lens | Stance |
|---------|----------|------|--------|
| Claude | Anthropic | Teleological | PRO-CT |
| Grok | xAI | Empirical | ANTI-CT |
| Nova | OpenAI | Symmetry | FAIRNESS |

### Components

- **Component 1**: CT<->MdN Pilot (7 metrics, convergence scoring)
- **Component 2**: Axioms Review (Grok 5 questions, Nova 6 questions)

See: `12_CFA/README.md` | `12_CFA/SYNC_OUT/CFA_TRINITY_DRY_RUN.md`

---

## Key Specs

| Spec | Location | Purpose |
|------|----------|---------|
| Run Design Checklist | `0_docs/specs/RUN_DESIGN_CHECKLIST.md` | Pre-flight for new runs |
| Sonar Probe Curriculum | `0_docs/specs/SONAR_PROBE_CURRICULUM.md` | Probe sequence design |
| Testing Map | `../../../docs/maps/TESTING_MAP.md` | Eight search types |
| CFA Design Spec | `12_CFA/schemas/RUN_CFA_DESIGN.md` | CFA Trinity experiment design |

---

Last Updated: December 14, 2025 (Fleet Tier System added)
