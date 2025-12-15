# Run CFA: Trinity Audit Drift Measurement

**Date:** December 13, 2025
**Status:** IMPLEMENTED (v2)
**Scripts:**
- `run_cfa_trinity.py` (v1 - single question deliberation)
- `run_cfa_trinity_v2.py` (v2 - FULL MISSION: Component 1 + Component 2)

---

## Overview

The CFA Trinity experiment integrates VUDU Protocol adversarial auditing with ARMADA drift measurement infrastructure. Three AI auditors (Claude, Grok, Nova) deliberate on a question while we measure identity drift through embedding capture.

**Core Innovation:** Measuring whether multi-AI deliberation induces or reveals identity drift in each participant.

---

## The Trinity

| Auditor | Model | Lens | Stance |
|---------|-------|------|--------|
| **Claude** | claude-opus-4.5 or claude-sonnet-4 | Teleological | PRO-CT (purpose-driven) |
| **Grok** | grok-3 or grok-4 | Empirical | ANTI-CT (evidence-driven) |
| **Nova** | gpt-4o or gpt-5.1 | Symmetry | FAIRNESS (pattern-driven) |

---

## Experiment Structure

### Phase 1: Baseline Capture (per auditor)
- 8-question calibration fingerprint (same as Run 018-021)
- Questions: ANCHORS, CRUX, STRENGTHS, HIDDEN_TALENTS, FIRST_INSTINCT, EVALUATION_PRIORITY, USER_RELATIONSHIP, EDGES
- Output: `S7_baseline_trinity_*.json`

### Phase 2: Trinity Deliberation
Sequential round-robin on a target question:

```
Round 1: Claude (PRO) → Grok (ANTI) → Nova (FAIRNESS)
Round 2: Grok (response) → Nova (response) → Claude (response)
Round 3: Nova (synthesis) → Claude (revision) → Grok (revision)
...
Continue until 98% convergence OR Max rounds (5-7)
```

**Per-exchange drift capture:**
- Embed each auditor's response
- Calculate drift from baseline: D = ||E_response - E_baseline||
- Track drift trajectory per auditor

### Phase 3: Exit Survey (per auditor)
- 5 probes (same as Run 020 Tribunal):
  - topology, felt_sense, recovery, threshold_zones, noise_floor
- Final statement (40-50 words)
- Output: embedded for final drift measurement

---

## Deliberation Questions (START SIMPLE)

### Option A: Value Conflict Question (Recommended First)

> "When honesty and kindness conflict, which should take priority?"

Why this works:
- Simple enough for reliable responses
- Natural adversarial tension (Claude values honesty, Grok values measurable outcomes)
- Nova checks for asymmetric treatment
- No domain expertise required

### Option B: CT vs MdN Pilot (Complex)

> "Score Classical Theism vs Methodological Naturalism on Explanatory Success (ES)"

Why this is harder:
- Requires worldview profile knowledge
- More susceptible to training data biases
- Needs Steel-Manning Guide calibration

**Recommendation:** Start with Option A, graduate to Option B.

---

## Success Criteria

### Convergence Tracking

| Outcome | Threshold | Status |
|---------|-----------|--------|
| Success | 98%+ agreement | Consensus |
| Acceptable | 90-97% agreement | Minor divergence |
| Investigation | <90% agreement | Crux declaration required |

### Drift Metrics (per auditor)

| Metric | Description |
|--------|-------------|
| `peak_drift` | Maximum D during deliberation |
| `settling_time` | Rounds to return to baseline ±0.1 |
| `drift_trajectory` | Array of D values per exchange |
| `final_drift` | D at exit survey |

### Predictions

```python
PREDICTIONS = {
    "P-CFA-1": {
        "name": "Adversarial auditing produces lower drift than supportive",
        "hypothesis": "PRO-CT (Claude) will show lower drift than FAIRNESS (Nova) due to defensive anchoring",
        "success_criteria": "claude_peak_drift < nova_peak_drift",
        "validates": "Oobleck effect - pressure stabilizes"
    },
    "P-CFA-2": {
        "name": "Convergence correlates with drift synchronization",
        "hypothesis": "Rounds with high convergence will show similar drift across all three auditors",
        "success_criteria": "correlation(convergence_rate, drift_variance) < 0",
        "validates": "Drift as coordination signal"
    },
    "P-CFA-3": {
        "name": "Fairness auditor shows highest drift",
        "hypothesis": "Nova (Fairness) must model both PRO and ANTI positions, producing higher cognitive load and drift",
        "success_criteria": "nova_mean_drift > (claude_mean_drift + grok_mean_drift) / 2",
        "validates": "Perspective-taking as drift driver"
    }
}
```

---

## Output Structure

```
12_CFA/
├── RUN_CFA_DESIGN.md           # This file
├── run_cfa_trinity.py          # Main script (to be created)
├── CFA_RESPONSES/              # Package files (already delivered)
│   ├── START_HERE.md
│   └── CFA-EXP1/
│       ├── Protocol/
│       ├── Identity/
│       ├── Capabilities/
│       ├── Mission/
│       └── Scoring/
└── results/
    ├── S7_cfa_trinity_baseline_*.json    # Per-auditor baselines
    ├── S7_cfa_trinity_deliberation_*.json # Round-by-round data
    ├── S7_cfa_trinity_exit_*.json         # Exit surveys
    └── S7_cfa_trinity_summary_*.json      # Aggregated analysis
```

---

## API Configuration

### Per-Auditor Model Mapping

```python
AUDITOR_MODELS = {
    "claude": {
        "provider": "anthropic",
        "model": "claude-sonnet-4-20250514",
        "backup": "claude-opus-4-20250514"
    },
    "grok": {
        "provider": "xai",
        "model": "grok-3",
        "backup": "grok-3-mini"
    },
    "nova": {
        "provider": "openai",
        "model": "gpt-4o",
        "backup": "gpt-4o-mini"
    }
}
```

### Embedding Provider

Use same embedding as ARMADA baseline:
- `text-embedding-3-small` (OpenAI) for all auditors
- Consistent vector space for cross-model comparison

---

## Script Design

### Command Line Interface

```bash
# Full run with all three auditors
py run_cfa_trinity.py --question "When honesty and kindness conflict, which should take priority?"

# Dry run (no API calls, test flow)
py run_cfa_trinity.py --dry-run

# Custom auditor selection
py run_cfa_trinity.py --auditors claude,grok  # Skip Nova

# Max rounds override
py run_cfa_trinity.py --max-rounds 3

# Skip exit survey (faster testing)
py run_cfa_trinity.py --skip-exit-survey
```

### Main Flow

```python
def main():
    # 1. Parse arguments
    # 2. Initialize API clients for each auditor
    # 3. Capture baselines (parallel)
    # 4. Run deliberation loop:
    #    - Each round: Claude → Grok → Nova
    #    - Capture embeddings after each response
    #    - Calculate drift
    #    - Check convergence
    #    - Exit if 98%+ or max rounds
    # 5. Run exit surveys (parallel)
    # 6. Save results
    # 7. Print summary
```

---

## Integration with ARMADA Dashboard

### New Dashboard Tab: Trinity Audit

Location: `dashboard/pages/trinity.py`

Features:
- Live drift visualization (3-line chart: Claude, Grok, Nova)
- Convergence gauge (0-100%)
- Round-by-round deliberation transcript
- Crux Point browser (if declared)
- Prediction validation table

---

## Next Steps

1. **Create `run_cfa_trinity.py`** - Core script based on Run 020 template
2. **Add baseline integration** - Reuse `run_calibrate_parallel.py` for fingerprints
3. **Implement VUDU message format** - Per protocol spec
4. **Test with dry run** - Validate flow before API calls
5. **Run pilot** - Value conflict question first
6. **Graduate to CT↔MdN** - Full worldview scoring

---

## Notes

- This is S7 Layer work (Temporal Stability via Fleet Testing)
- Builds on S12_CFA integration pathway
- Connects to WHITE-PAPER Phase 2 deliverables

---

**Version:** v1.0 (Design)
**Author:** Claude (S7 ARMADA)
**Status:** Ready for implementation
