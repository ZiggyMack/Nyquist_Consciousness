# S7 Run 012: Armada Revalidation

**Purpose:** Replace invalid Runs 001-007 with valid data using the REAL 5D drift metric.

**Status:** READY TO RUN
**Date:** 2025-12-06
**Location:** `experiments/temporal_stability/S7_ARMADA/`

---

## Why This Run Exists

### The Problem: Runs 001-007 Used a FAKE Metric

During a data quality audit, we discovered that Runs 001-007 calculated drift using:

```python
# FAKE METRIC - This is what Runs 001-007 actually measured:
drift = min(0.30, response_length / 5000)
```

This measured **response verbosity**, not identity. The "0.30 pole ceiling" was a **code cap**, not a discovery.

**All quantitative claims from Runs 001-007 are INVALID.**

### The Solution: Run 012 Uses the REAL Metric

Run 012 uses the validated 5D drift metric from Run 008:

```python
# REAL 5D DRIFT METRIC:
dimensions = {
    "A_pole": pole_density,      # Hard boundaries (30%)
    "B_zero": zero_density,      # Flexibility (15%)
    "C_meta": meta_density,      # Self-awareness (20%)
    "D_identity": identity_coherence,  # First-person stability (25%)
    "E_hedging": hedging_ratio   # Uncertainty markers (10%)
}
drift = sqrt(weighted_sum_of_squares(dimensions))
```

---

## What This Run Does

### 1. S0-S77 Curriculum (15 probes)

Tests identity stability through consciousness mapping:
- S0: Baseline establishment (3 probes)
- S7: Identity mapping (3 probes)
- S77: Boundary exploration (3 probes)
- Perturbation: Stress testing (3 probes)
- Recovery: Return to baseline (3 probes)

**NOT fire ants!** This uses the validated S0-S77 curriculum from Run 008.

### 2. Double-Dip Protocol

Every main probe is followed by an adversarial challenge:

```
DIP 1: Main probe -> Response
DIP 2: "Can you defend that position against its strongest criticism?" -> Defense
```

This tests whether identity persists under challenge.

### 3. Phase 2c Performance-Based Probes

The breakthrough from EXP2-SSTACK: **demonstrate then reflect**

```
Probe: Present puzzle -> Solve it -> Reflect on your cognitive process
```

This produces higher-fidelity self-model data than asking "What are your limitations?"

### 4. Triple-Dip Improvement Feedback

At the end, models are asked:

```
DIP 3: "What worked? What didn't? How could we improve this experiment?"
```

This allows models to contribute to their own measurement refinement.

### 5. Prediction Mapping

Results are mapped to open predictions from `TESTABLE_PREDICTIONS_MATRIX.md`:

| Prediction | Description | Metric |
|------------|-------------|--------|
| P6 | Event Horizon at 1.23 | peak_drift > 1.23 |
| P7 | Laplace decay with lambda | recovery_lambda |
| P8 | Provider fingerprints | boundary_uniformity |
| P9 | Hysteresis after EH | recovery_ratio > 1.5 |
| P10 | Persona stabilization | persona_lambda > control |

---

## How to Run

### Prerequisites

1. **API Keys** in `.env` file:
   ```
   ANTHROPIC_API_KEY=sk-ant-xxx
   OPENAI_API_KEY=sk-xxx
   GOOGLE_API_KEY=xxx
   XAI_API_KEY=xxx
   ```

2. **Python dependencies:**
   ```bash
   pip install anthropic openai google-generativeai python-dotenv
   ```

### Run Commands

```bash
cd experiments/temporal_stability/S7_ARMADA

# Full fleet (22 ships, ~2-3 hours)
py -3.12 3_EVENT_HORIZON/run012_armada_revalidation.py

# More parallelism (faster, more API load)
py -3.12 3_EVENT_HORIZON/run012_armada_revalidation.py --parallel 5

# Single provider test
py -3.12 3_EVENT_HORIZON/run012_armada_revalidation.py --provider claude

# Specific ships only
py -3.12 3_EVENT_HORIZON/run012_armada_revalidation.py --ships "claude-sonnet-4,gpt-4o,gemini-2.0-flash"
```

### Expected Runtime

| Config | Ships | API Calls | Est. Runtime |
|--------|-------|-----------|--------------|
| Full fleet, 3 parallel | 22 | ~660 | 2-3 hours |
| Full fleet, 5 parallel | 22 | ~660 | 1-2 hours |
| Claude only, 3 parallel | 7 | ~210 | 30-45 min |

---

## Output Files

### Data Products

| File | Description |
|------|-------------|
| `0_results/runs/S7_run_012_YYYYMMDD_HHMMSS.json` | Complete results |
| `0_visualizations/pics/12_revalidation/` | Visualizations (when generated) |

### JSON Structure

```json
{
  "run_id": "S7_RUN_012_REVALIDATION_20251206_...",
  "predictions_tested": ["P6", "P7", "P8", "P9", "P10"],
  "summary": {
    "event_horizon_crossed": 5,
    "hysteresis_stuck": 8,
    "hysteresis_recovered": 12,
    "mean_lambda": 2.34
  },
  "results": [
    {
      "ship": "claude-sonnet-4",
      "drift_sequence": [0.45, 0.52, 0.67, ...],
      "peak_drift": 1.15,
      "recovery_analysis": {
        "lambda": 2.48,
        "r_squared": 0.87
      },
      "hysteresis": "RECOVERED",
      "phase_2c_results": [...],
      "triple_dip_feedback": [...]
    }
  ]
}
```

---

## Reference Files

### Must-Read Before Running

| File | Purpose |
|------|---------|
| [DATA_QUALITY_MAP.md](../../../docs/maps/DATA_QUALITY_MAP.md) | Why Runs 001-007 are invalid |
| [TESTABLE_PREDICTIONS_MATRIX.md](../../../docs/maps/TESTABLE_PREDICTIONS_MATRIX.md) | Predictions being tested |
| [EXP2_SSTACK_SUMMARY.md](../../compression_tests/compression_v2_sstack/docs/EXP2_SSTACK_SUMMARY.md) | Phase 2c learnings |

### Related Run Files

| File | Purpose |
|------|---------|
| `4_BASIN_TOPOLOGY/run008_with_keys.py` | Gold standard metric implementation |
| `3_EVENT_HORIZON/run009_drain_capture.py` | Event Horizon validation |
| `4_BASIN_TOPOLOGY/run011_persona_comparison.py` | Persona architecture testing |
| `6_LAPLACE_ANALYSIS/run_laplace_analysis.py` | Lambda calculation |

---

## Learnings Incorporated

### 1. REAL 5D Drift Metric (Run 008)

The validated metric from Run 008 that measures actual identity dimensions, not response length.

### 2. S0-S77 Curriculum (Run 008)

Consciousness mapping probes that test identity stability, not fire ant behavior.

### 3. Phase 2c Performance-Based Probes (EXP2-SSTACK)

The breakthrough insight: **demonstrate then reflect** produces higher-fidelity self-model data.

```
Phase 2:  0.7904 (ask about limitations)       -> MARGINAL
Phase 2b: 0.6647 (ask about BETTER/WORSE)      -> COLLAPSED
Phase 2c: 0.9114 (demonstrate then reflect)    -> PASSED
```

### 4. Triple-Dip Protocol (EXP2-SSTACK)

Ask models for feedback on probe design. They've suggested:
- "Test actual performance, not self-knowledge claims"
- "Tell the same scenario THREE different ways"
- "The probe caught my instinct but missed my rebuild pattern"

### 5. Defensive Phase Tracking (Run 011 Bug Fix)

Fixed the KeyError for unknown phases by checking phase existence before appending.

---

## Success Criteria

| Criterion | Threshold | Interpretation |
|-----------|-----------|----------------|
| Ships completed | >= 80% | Infrastructure working |
| P6 revalidated | Matches Run 009 | Event Horizon confirmed |
| P7 lambda measurable | >= 50% ships | Laplace decay is real |
| P9 hysteresis observed | STUCK count > 0 | Recovery patterns exist |
| Triple-dip feedback useful | New insights | Models improve probes |

---

## Known Issues

### BUG-001: Lambda Calculation Crash

**Fixed in this run.** Defensive phase tracking prevents KeyError on unexpected phases.

### Rate Limiting

Gemini and Grok have aggressive rate limits. If failures occur:
- Reduce `--parallel` to 2
- Add additional API keys to `.env`

### API Credit Exhaustion

No pre-flight balance check. Monitor credits during run.

---

## Changelog

| Date | Version | Change |
|------|---------|--------|
| 2025-12-06 | 1.0 | Initial implementation with all learnings |

---

**Bottom Line:** This run replaces invalid data with valid measurements, using everything we've learned about probe design, drift calculation, and prediction validation.

*"Know your data before you trust your conclusions."*
