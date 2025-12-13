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

**Last Updated:** 2025-12-13

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

**Default:** `--quick`

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

### Calibration Status (`0_results/calibration/`)

```text
S7_armada_check_YYYYMMDD_HHMMSS.json   # Fleet status (working/ghost/rate-limited)
S7_baseline_YYYYMMDD_HHMMSS.json       # Identity fingerprints (baseline mode only)
S7_baseline_LATEST.json                # Symlink to most recent baseline
S7_baseline_comparison_*.json          # Auto-comparison with previous baseline
```

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
|-- README.md                    # This file
+-- lib/                         # Helper modules (auto-imported, not run directly)
    |-- __init__.py
    |-- compare_baselines.py     # Auto-imported by run_calibrate_parallel.py
    |-- compare_persona_to_fleet.py
    +-- update_persona_matrix.py
```

## Main Scripts (User-Run)

| Script | Purpose |
|--------|---------|
| `run_calibrate_parallel.py` | Main calibration - runs fleet health check and baseline capture |
| `extract_persona_baseline.py` | Extract STRENGTHS/ANCHORS/EDGES from I_AM persona files |
| `rescue_ghost_ships.py` | Attempt to recover ghost ships with alternative parameters |

## Helper Modules (lib/)

| Module | Called By | Purpose |
|--------|-----------|---------|
| `lib/compare_baselines.py` | `run_calibrate_parallel.py` (auto) | Compare two baseline files |
| `lib/compare_persona_to_fleet.py` | Manual analysis | Compare persona against fleet averages |
| `lib/update_persona_matrix.py` | Manual analysis | Update persona matrix with new baselines |

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
| 2025-12-13 | Reorganized directory: helper modules moved to `lib/` |
| 2025-12-13 | Updated `compare_baselines.py` to extract all 8 questions |
| 2025-12-13 | Added `--depth` flag (ping vs baseline modes) |
| 2025-12-13 | Expanded baseline from 3 to 8 questions (CFA recommendation) |
| 2025-12-12 | Initial parallel calibration script |
