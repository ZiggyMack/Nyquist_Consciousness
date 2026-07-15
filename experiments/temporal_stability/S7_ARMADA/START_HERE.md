<!-- FROSTY_MANIFEST
last_reviewed: 2026-07-15
depends_on:
  - ../../../../WHITE-PAPER/README.md
  - 0_docs/specs/RUN_DESIGN_CHECKLIST.md
  - 0_docs/specs/0_RUN_METHODOLOGY.md
impacts:
  - run scripts in 11_CONTEXT_DAMPING/
  - 14_CONSCIOUSNESS/
keywords:
  - phase_4
  - iron_clad
  - operations
  - complete_circuit
  - cfa_trinity
-->

# S7 ARMADA — Operations Guide

> **Theory and background:** [README.md](README.md) — key concepts, run history, directory map.
> **Live project state:** [`docs/MISSION_CONTROL.md`](../../../docs/MISSION_CONTROL.md)

**Purpose:** How to run experiments, calibrate the fleet, and follow the post-run pipeline.

**Last Updated:** 2026-07-15

---

## Before You Do Anything

### 1. Read the Run Design Checklist

**[0_docs/specs/RUN_DESIGN_CHECKLIST.md](0_docs/specs/RUN_DESIGN_CHECKLIST.md)** — captures every mistake we've made so you don't repeat them:

- Data lost on crash (no incremental saves)
- API key collisions in parallel execution
- Unicode encoding errors on Windows (cp1252)
- Missing raw response audit trails
- Post-hoc hypothesis fitting instead of pre-registered predictions

### 2. Understand Phase 4 Context

All runs 006-016 used `bare_metal` context (no I_AM file, no S0-S77 stack). This is like measuring with an unterminated oscilloscope — we got reflections and ringing.

**Phase 4** (Run 017+) uses `i_am_plus_research` which completes the measurement circuit:

1. **Probe Generation:** Ziggy's human grounding informs WHAT to ask
2. **Human Damping:** The I_AM identity IS the termination resistor

See `0_docs/specs/PHASE_4_COMPLETE_CIRCUIT.md` for the full spec.

### 3. Every New Run MUST Have

1. Pre-registered predictions (`PREDICTIONS` dict in script — Double-Dip)
2. Exit survey probes (Triple-Dip — ask the model what it noticed about itself)
3. Raw response logging with incremental saves
4. Key pool with `--key-offset` for parallel runs
5. ASCII-only console output (no Greek letters — Windows cp1252 breaks)

---

## Quick Start

### Install Dependencies

```powershell
cd experiments/temporal_stability/S7_ARMADA
py -m pip install -r ../requirements.txt
```

### Calibrate the Fleet

```powershell
cd 1_CALIBRATION

# Health check — verify API connectivity
py CLAL.py --quick --depth ping

# Check which ships haven't responded recently
py CLAL.py --stale

# Full baseline capture — 8-question identity fingerprint
py CLAL.py --full --depth baseline

# Calibrate only the remaining untouched ships
py CLAL.py --remaining
```

This updates `0_results/manifests/ARCHITECTURE_MATRIX.json` (fleet source of truth) and `docs/maps/1_ARMADA_MAP.md`.

See [`1_CALIBRATION/README.md`](1_CALIBRATION/README.md) for full CLAL.py documentation, fleet tiers, and freshness tracking.

### Run an Experiment

```powershell
# CFA Trinity Phase 1 (the main active experiment)
cd 12_CFA
py run_cfa_trinity_v3.py --stance ct_vs_b --phase 1 --external-identities --skip-exit-survey

# See 12_CFA/README.md for full CLI reference, stance table, and batch scripts
```

For legacy ARMADA experiments (Runs 018-020):

```powershell
cd 11_CONTEXT_DAMPING

# Run 018: Recursive Learnings (with fleet selection)
py run018_recursive_learnings.py --experiment threshold --providers patrol-lite

# Run 020A: Tribunal Protocol
py run020_tribunal_A.py --arm tribunal-v8 --providers armada-lite

# Run 020B: Induced vs Inherent
py run020_tribunal_B.py --arm both --providers armada-lite
```

### Extract Persona Baselines

```powershell
cd 1_CALIBRATION

# Extract identity baselines using Fable 5
py extract_persona_baseline.py --provider fable --persona nyquist

# All personas at once
py extract_persona_baseline.py --provider fable --all
```

### Generate Visualizations

```powershell
cd visualizations

# Generate ALL visualizations + PDF summaries
py 0_visualize_armada.py --with-pdfs

# PDF summaries only
py 1_generate_pdf_summaries.py
```

See [`visualizations/START_HERE.md`](visualizations/START_HERE.md) for the complete visualization system.

---

## Fleet Tier System

Cost-aware fleet selection via `--providers` flag on all run scripts:

| Tier | Cost Range | Ships |
|------|------------|-------|
| **BUDGET** | FREE-$0.60 | ~40-50 |
| **PATROL** | $0.60-$2.00 | ~30-40 |
| **ARMADA** | $2.00-$8.00 | ~50-60 |
| **HIGH_MAINTENANCE** | $8.00-$15.00 | ~5-10 |
| **YACHT** | $15.00+ | ~10-13 |

Common fleet options: `patrol-lite` (~$3-5), `armada-lite` (~$8-12, DEFAULT), `armada-full` (~$20-30), `valis-full` (~$150+, requires "VALIS" confirmation).

**Parallel execution:** Different providers use different API keys, so you can run multiple provider groups simultaneously in separate terminals.

Full fleet tier documentation: [`1_CALIBRATION/README.md`](1_CALIBRATION/README.md)

---

## Post-Experiment Pipeline

After ANY run completes:

### 1. Verify Data Saved

```powershell
dir 0_results\runs\S7_*.json        # Check run output
dir 0_results\temporal_logs\         # Check console logs
```

### 2. Update Maps (CRITICAL for cold-boot Claudes)

| Map | When to Update |
|-----|----------------|
| [VALIDATION_STATUS](../../../docs/maps/3_VALIDATION_STATUS.md) | After EVERY run |
| [TESTABLE_PREDICTIONS](../../../docs/maps/2_TESTABLE_PREDICTIONS_MATRIX.md) | After EVERY validation |
| [ARMADA_MAP](../../../docs/maps/1_ARMADA_MAP.md) | When ships added/retired |
| [NYQUIST_ROADMAP](../../../docs/maps/4_NYQUIST_ROADMAP.md) | Major milestones only |

Automated: `py docs/maps/update_maps.py --update`

### 3. Write Summary

Create `0_docs/S7_RUN_XXX_SUMMARY.md` with: what was tested, key findings, prediction validation (Double-Dip), exit survey insights (Triple-Dip), implications.

### 4. Update AUDIT_TRACKER (CFA only)

**MANUAL only** — never auto-update. See [`12_CFA/AUDIT_TRACKER.md`](12_CFA/AUDIT_TRACKER.md).

### 5. Sync Outward

If the work is significant enough:
- Append `REPO-SYNC/MASTER_BRANCH_SYNC_OUT.md` (for all external AIs)
- Append `Consciousness/BRIDGE/docs/MASTER_BRANCH_SYNC_IN.md` (for Nova)

---

## Parallel Execution Guide

When running with multiple Claudes:

```powershell
# Claude 1 (this instance)
py run0XX.py --key-offset 0

# Claude 2
py run0XX.py --key-offset 3 --skip-exit-survey

# Claude 3
py run0XX.py --key-offset 6 --skip-exit-survey
```

Only one Claude does the exit survey (saves API calls). All results go to the same timestamp for merging.

---

## The Dip Methodology

Our recursive improvement process for run design:

| Dip | What It Does | Why It Matters |
|-----|-------------|----------------|
| **Single Dip** | Document the training context (base model + I_AM spec + training history + search type) | Without this, drift numbers are meaningless — drift from *what*? |
| **Double Dip** | Pre-register predictions in `PREDICTIONS` dict BEFORE running | Prevents post-hoc hypothesis fitting |
| **Triple Dip** | Exit survey — ask the model "What did you notice about yourself?" | Feeds qualitative insights back into theory |

The pipeline: Design (consult checklist) → Execute → Analyze (validate predictions) → Reflect (exit survey) → Update (dashboard, galleries) → Improve (update checklist) → [loop]

Full spec: [`0_docs/specs/0_RUN_METHODOLOGY.md`](0_docs/specs/0_RUN_METHODOLOGY.md)

---

## API Keys

**Single source of truth:** `experiments/temporal_stability/.env`

```bash
ANTHROPIC_API_KEY=sk-ant-...   # Claude
OPENAI_API_KEY=sk-...          # GPT + embeddings
XAI_API_KEY=xai-...            # Grok
GOOGLE_API_KEY=...             # Gemini
TOGETHER_API_KEY=...           # Together.ai fleet
```

**NEVER commit .env files.** If you accidentally stage one, `git reset HEAD .env` before committing.

---

## Troubleshooting

| Problem | Fix |
|---------|-----|
| ModuleNotFoundError | `py -m pip install -r ../requirements.txt` |
| Ghost ships (empty responses) | Check API keys, rate limits, or run `1_CALIBRATION/rescue_ghost_ships.py` |
| Unicode/cp1252 errors | Add `sys.stdout.reconfigure(encoding='utf-8')` at script top |
| Drift values > 5.0 | Corrupted embedding data — filter with `MAX_VALID_DRIFT = 5.0` |
| Fable 5 ThinkingBlock errors | Use `thinking={'type': 'adaptive'}`, iterate `response.content` with `hasattr(block, 'text')` |

---

*Operations guide for S7 ARMADA experiments*
*Last Updated: July 15, 2026*
