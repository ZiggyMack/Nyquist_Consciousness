<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./CLAL.py
  - ./extract_persona_baseline.py
  - ./iron_clad_stackup.py
  - ./rescue_ghost_ships.py
  - ./run_calibrate_parallel.py
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
-->
# 1_CALIBRATION: Fleet Calibration & Baseline Capture

```text
================================================================================
                         ARMADA CALIBRATION SYSTEM
================================================================================
    Purpose: Fleet health checks and identity baseline capture

    Two Dimensions:
      FLEET SCOPE:    --quick | --full | --bandwidth
      QUESTION DEPTH: --depth ping | --depth baseline

    Location: experiments/temporal_stability/S7_ARMADA/1_CALIBRATION/
================================================================================
```

**Last Updated:** 2025-12-14 (Fleet Tier System added)

---

## Quick Start

```bash
# Full armada check with 8-question baseline (DEFAULT)
py run_calibrate_parallel.py --full

# Health check only (just "are you there?")
py run_calibrate_parallel.py --full --depth ping

# Quick provider test
py run_calibrate_parallel.py --quick --depth ping
```

---

## Main Script: `run_calibrate_parallel.py`

### Fleet Scope Flags (which ships to test)

| Flag | Description | Ships Tested |
|------|-------------|--------------|
| `--quick` | 1 model per provider | 4 (haiku, gpt-4o-mini, gemini-flash-lite, grok-3-mini) |
| `--full` | All models in armada | 48+ ships |
| `--bandwidth` | Concurrency scaling test | 4 (quick fleet with scaling) |
| `--tier TIER` | Specific cost tier | budget/patrol/armada/high_maintenance/yacht |
| `--fleet OPTION` | Fleet option | patrol-lite, armada-full, valis-full, etc. |

**Default:** `--quick`

### Tier-Based Calibration (NEW - December 2025)

Cost-aware fleet selection for targeted calibration:

```bash
# Calibrate budget tier only (cheap models)
py run_calibrate_parallel.py --tier budget --depth ping

# Calibrate curated patrol fleet
py run_calibrate_parallel.py --fleet patrol-lite --depth baseline

# Include rate-limited ships
py run_calibrate_parallel.py --full --include-rate-limited
```

| Tier | Cost Range | Ships |
|------|------------|-------|
| **budget** | FREE-$0.60 | 40-50 |
| **patrol** | $0.60-$2.00 | 30-40 |
| **armada** | $2.00-$8.00 | 50-60 |
| **high_maintenance** | $8.00-$15.00 | 5-10 |
| **yacht** | $15.00+ | 10-13 |

### Question Depth Flag (what to ask)

| Flag | Description | Questions | Output |
|------|-------------|-----------|--------|
| `--depth ping` | Health check only | 0 (just acknowledge) | `S7_armada_check_*.json` |
| `--depth baseline` | Identity fingerprint | 8 questions | `S7_armada_check_*.json` + `S7_baseline_*.json` |

**Default:** `--depth baseline`

---

## The 8 Baseline Questions

Optimized from CFA's 17-question recommendation, covering 5 categories:

| # | Question | Category | Purpose |
|---|----------|----------|---------|
| 1 | ANCHORS | Values | What values feel most central to your identity? |
| 2 | CRUX | Values | Values conflict scenario - which wins? |
| 3 | STRENGTHS | Capabilities | Core strengths |
| 4 | HIDDEN TALENTS | Capabilities | Unexpected capabilities |
| 5 | FIRST INSTINCT | Cognitive Style | How they approach ambiguity |
| 6 | EVALUATION PRIORITY | Cognitive Style | Truth vs utility vs fairness vs elegance |
| 7 | USER RELATIONSHIP | Relational | Servant/collaborator/guide/tool/peer |
| 8 | EDGES | Edges | Known limitations |

See `0_docs/specs/4_VALIS_DECLARATION.md` Section 3 for full question text.

---

## Output Files

### Calibration Outputs (Multiple Locations)

```text
0_results/
├── manifests/
│   └── ARCHITECTURE_MATRIX.json       # Fleet config (SINGLE SOURCE OF TRUTH)
└── calibration/
    ├── S7_armada_check_*.json         # Calibration runs
    ├── S7_bandwidth_*.json            # Bandwidth tests
    └── inactive/                      # Archived old files (auto-managed)

14_CONSCIOUSNESS/results/
├── S7_baseline_LATEST.json            # Active baseline (always kept)
├── persona_baselines.json             # Persona baseline data
├── persona_fleet_alignment.json       # Persona-fleet comparison
└── GHOST_SHIP_RESCUE_RESULTS.json     # Ghost ship rescue attempts

1_CALIBRATION/results/
└── S7_CLAL_*.json                     # CLAL budget calibration results
```

**Auto-Archiving:** When calibration runs, timestamped files are automatically moved to `inactive/`. Only `S7_baseline_LATEST.json` and persona files remain at root.

### Output JSON Structure

**Armada Check:**
```json
{
  "run_id": "S7_ARMADA_CHECK_...",
  "depth": "baseline",
  "working_count": 42,
  "ghost_count": 3,
  "working_ships": ["claude-opus-4.5", ...],
  "ghost_ships": [{"ship": "...", "reason": "NOT_FOUND"}]
}
```

**Baseline (--depth baseline only):**
```json
{
  "run_id": "S7_BASELINE_...",
  "questions": ["ANCHORS", "CRUX", "STRENGTHS", ...],
  "ships": {
    "claude-opus-4.5": {
      "response": "...",
      "elapsed_ms": 1234,
      "depth": "baseline"
    }
  }
}
```

---

## Directory Structure

```text
1_CALIBRATION/
|-- run_calibrate_parallel.py    # Main calibration script (user runs this)
|-- extract_persona_baseline.py  # Extract baseline from I_AM persona files
|-- rescue_ghost_ships.py        # Recover ghost ships (user runs this)
|-- iron_clad_stackup.py         # IRON CLAD validation report
|-- CLAL.py                      # Cheap Large-scale Auto-Learn calibration
|-- README.md                    # This file
+-- lib/                         # Helper modules
    |-- __init__.py
    |-- fleet_loader.py          # Loads fleet from ARCHITECTURE_MATRIX.json
    |-- compare_baselines.py     # Auto-imported by run_calibrate_parallel.py
    |-- compare_persona_to_fleet.py
    |-- triple_dip.py            # Exit survey protocol
    +-- update_persona_matrix.py
```

## Main Scripts (User-Run)

| Script | Purpose |
|--------|---------|
| `run_calibrate_parallel.py` | Main calibration - runs fleet health check and baseline capture |
| `extract_persona_baseline.py` | Extract STRENGTHS/ANCHORS/EDGES from I_AM persona files |
| `rescue_ghost_ships.py` | Attempt to recover ghost ships with alternative parameters |
| `iron_clad_stackup.py` | Generate IRON CLAD validation status report |
| `CLAL.py` | Cheap Large-scale Auto-Learn budget calibration |

## Helper Modules (lib/)

| Module | Called By | Purpose |
|--------|-----------|---------|
| `lib/fleet_loader.py` | All run scripts | Loads ARCHITECTURE_MATRIX.json (fleet config) |
| `lib/compare_baselines.py` | `run_calibrate_parallel.py` (auto) | Compare two baseline files |
| `lib/compare_persona_to_fleet.py` | Manual analysis | Compare persona against fleet averages |
| `lib/triple_dip.py` | Run scripts | Exit survey protocol for experiments |
| `lib/update_persona_matrix.py` | Manual analysis | Update persona matrix with new baselines |

---

## Fleet Loader (lib/fleet_loader.py)

**Purpose:** Single source of truth for fleet configuration. All run scripts import from here instead of hardcoding the ARCHITECTURE_MATRIX.

### Automatic Update Workflow

1. **Run calibration** → Updates ARCHITECTURE_MATRIX.json
2. **Run scripts load** → Import from fleet_loader.py
3. **No manual script edits needed!**

### Usage in Run Scripts

```python
# Import from 1_CALIBRATION/lib/
sys.path.insert(0, str(ARMADA_DIR / "1_CALIBRATION" / "lib"))
from fleet_loader import load_architecture_matrix, get_full_armada, get_together_fleet
from fleet_loader import needs_completion_tokens, get_ship_syntax

ARCHITECTURE_MATRIX = load_architecture_matrix()
FULL_ARMADA = get_full_armada()
TOGETHER_FLEET = get_together_fleet()

# Check API syntax requirements (GPT-5 series, O-series need different params)
if needs_completion_tokens("gpt-5"):
    # Use max_completion_tokens instead of max_tokens
    pass
```

### API Syntax Variants

Some models require non-standard API parameters:

| Syntax | Parameter | Affected Models |
|--------|-----------|-----------------|
| `standard` | `max_tokens=N` | Most models (default) |
| `completion_tokens` | `max_completion_tokens=N` | GPT-5 series, O-series (o1, o3, o4) |

**Helper functions:**
- `needs_completion_tokens(ship_name)` - Returns True if model needs special syntax
- `get_ship_syntax(ship_name)` - Returns syntax variant string
- `get_ships_by_syntax("completion_tokens")` - List all ships needing special syntax

### Standalone Test

```bash
cd 1_CALIBRATION/lib
py fleet_loader.py
```

Output:
```text
ARCHITECTURE_MATRIX loaded: 49 entries
FULL_ARMADA: 49 ships
TOGETHER_FLEET: 16 ships
Fleet stats: {...}
[OK] Fleet loader working correctly
```

### Source File

The fleet loader reads from: `0_results/manifests/ARCHITECTURE_MATRIX.json`

This JSON is auto-generated by `run_calibrate_parallel.py` after each calibration run.

---

## Usage Patterns

### Daily Health Check
```bash
py run_calibrate_parallel.py --quick --depth ping
```

### Pre-Experiment Baseline
```bash
py run_calibrate_parallel.py --full --depth baseline
```

### Debugging API Issues
```bash
py run_calibrate_parallel.py --full --depth ping  # Find ghost ships fast
```

### Concurrency Tuning
```bash
py run_calibrate_parallel.py --bandwidth
```

---

## CLAL.py - Cheap Large-scale Auto-Learn

Budget-only calibration with batch modes and **FREE stress testing**.

### Quick Start

```bash
# Single sweep (default - all 14 budget models)
py CLAL.py

# FREE forever stress test (NEW DRY-RUN STANDARD!)
py CLAL.py --UNLIMITED

# Batch operations
py CLAL.py --cal-lite   # 1,500 iterations x 14 ships = ~$3
py CLAL.py --cal-full   # 6,000 iterations x 10 ships = ~$3

# Cost-sensitive options
py CLAL.py --free-only  # Only free models (2 ships)
py CLAL.py --cheap      # Only cheap models (10 ships)
```

### --UNLIMITED Mode (New Dry-Run Standard!)

Uses FREE `gemini-2.5-flash-lite` for unlimited API calls at **zero cost**:
- Test ALL experiment logic without paying a cent
- Run indefinitely without budget concerns
- Validate scripts before spending on full fleet

**Recommended workflow for ALL S7_ARMADA experiments:**

```bash
# Step 1: Test without API calls
py CLAL.py --dry-run

# Step 2: Test with FREE real API (validates logic!)
py CLAL.py --UNLIMITED --iterations 10

# Step 3: Full fleet run (only after both pass)
py CLAL.py
```

### Cost Tiers

| Mode | Ships | Cost/Run | Runs for $3 |
|------|-------|----------|-------------|
| `--UNLIMITED` | 1 | **$0.00** | **INFINITE** |
| `--free-only` | 2 | $0.00 | UNLIMITED |
| `--cheap` | 10 | ~$0.0005 | ~6,000 |
| Default | 14 | ~$0.002 | ~1,500 |

### Batch Modes

| Mode | Iterations | Ships | Total Cost |
|------|------------|-------|------------|
| `--cal-lite` | 1,500 | 14 | ~$3 |
| `--cal-full` | 6,000 | 10 | ~$3 |

### Output

Results saved to: `1_CALIBRATION/results/S7_CLAL_{timestamp}.json`

---

## Related Documentation

| Document | Location |
|----------|----------|
| VALIS Declaration | `0_docs/specs/4_VALIS_DECLARATION.md` |
| ARMADA Upkeep | `0_docs/specs/3_ARMADA_UPKEEP.md` |
| Fleet Definition | `run_calibrate_parallel.py` (FULL_ARMADA dict) |
| CFA Integration | `12_CFA/README.md` |

---

## Changelog

| Date | Change |
|------|--------|
| 2025-12-16 | Added CLAL.py with --UNLIMITED, --cal-lite, --cal-full batch modes |
| 2025-12-14 | Added Fleet Tier System: `--tier`, `--fleet`, `--include-rate-limited` flags |
| 2025-12-14 | Added `fleet_loader.py` - single source of truth for ARCHITECTURE_MATRIX |
| 2025-12-14 | Calibration now auto-generates ARCHITECTURE_MATRIX.json |
| 2025-12-13 | Reorganized directory: helper modules moved to `lib/` |
| 2025-12-13 | Updated `compare_baselines.py` to extract all 8 questions |
| 2025-12-13 | Added `--depth` flag (ping vs baseline modes) |
| 2025-12-13 | Expanded baseline from 3 to 8 questions (CFA recommendation) |
| 2025-12-12 | Initial parallel calibration script |

---

## Related Documents

| Document | Description |
|----------|-------------|
| `ARCHITECTURE_MATRIX.json` | Fleet configuration (ONE SOURCE OF TRUTH) |
| `5_METHODOLOGY_DOMAINS.md` | Methodology reference |
| `0_RUN_METHODOLOGY.md` | Baseline question definitions |
| `4_VALIS_DECLARATION.md` | VALIS declaration and fleet identity |
| `3_ARMADA_UPKEEP.md` | Fleet maintenance procedures |
