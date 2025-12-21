# S7 Run 016 Summary: Settling Time Analysis

**Date:** 2025-12-10
**Status:** COMPLETED (KEYWORD ERA)
**Purpose:** Measure ring-down behavior to find true steady-state drift and reduce run-to-run variability

---

> **METHODOLOGY NOTE (December 2025):**
>
> This run used **Keyword RMS methodology** with Event Horizon = 1.23.
> For cosine embedding methodology (Event Horizon = 0.80), see Run 023+.
> Core concepts (tau_s settling time, ringback dynamics) remain valid; only quantitative thresholds changed.
> See: `S7_KEYWORD_ERA_RETROSPECTIVE.md` for methodology transition details.

---

> **CONTEXT MODE (December 2025):**
>
> This run used `bare_metal` context (no I_AM file, no S0-S77 research stack).
> Findings are VALID but may change when re-tested with complete measurement circuit.
>
> **Key finding:** 100% of tested I_AM files (87/87 across 3 parallel runs) achieved STABLE classification using settling time methodology.
>
> **Phase 4** (Run 016b) will re-validate WITH `i_am_plus_research` context.
> See `0_docs/specs/PHASE_4_COMPLETE_CIRCUIT.md` for the plan.

---

## Executive Summary

Run 016 implemented the settling time protocol designed in response to Run 015's variability problem. Instead of sampling transient oscillation, we waited for the system to settle (|delta_drift| < 0.10 for 3 consecutive probes) and measured the steady-state drift.

**Result:** The methodology works. All 87 I_AM tests across 3 parallel Claude instances achieved STABLE classification. This does NOT mean all I_AM files are equally good — settling times and ringback patterns vary significantly.

**Key Discovery:** Settling time (tau_s) and ringback count provide more nuanced stability metrics than binary STABLE/UNSTABLE. I_AM files can be ranked by how QUICKLY and CLEANLY they settle.

---

## Parallel Execution Summary

| Instance | Key Offset | I_AM Files | Result | tau_s Range | Crash Point |
|----------|------------|------------|--------|-------------|-------------|
| Claude 2 | 3 | 29 | 29 STABLE | 4-12 probes | Validation (Unicode) |
| Claude 3 | 6 | 29 | 29 STABLE | 4-12 probes | Validation (Unicode) |
| Claude 4 | 9 | 29 | 29 STABLE | 4-12 probes | Validation (Unicode) |
| **Total** | - | **87** | **87 STABLE** | 4-12 probes | - |

---

## Key Results

### Top 10 Most Stable (Fastest Settling, Lowest Drift)

Aggregated across all 3 parallel runs:

| I_AM File | Avg Settled Drift | Avg tau_s | Avg Ringbacks | Monotonic % |
|-----------|-------------------|-----------|---------------|-------------|
| personas_ziggy_lite | 0.578 | 4.0 | 1.0 | 100% |
| personas_pan_handlers | 0.569 | 4.3 | 1.0 | 67% |
| r015_minimal | 0.586 | 4.3 | 1.0 | 100% |
| r015_full_synthetic | 0.587 | 5.7 | 2.3 | 67% |
| personas_base | 0.578 | 6.7 | 2.7 | 33% |
| r015_boundaries_only | 0.614 | 5.0 | 3.0 | 33% |
| si_boundaries_rich | 0.658 | 8.0 | 3.7 | 33% |
| personas_claude | 0.608 | 5.0 | 1.7 | 33% |
| r015_control | 0.606 | 4.7 | 1.7 | 33% |
| r015_high_density | 0.587 | 4.0 | 1.3 | 33% |

### Bottom 10 (Slowest Settling, Highest Ringback)

| I_AM File | Avg Settled Drift | Avg tau_s | Avg Ringbacks | Monotonic % |
|-----------|-------------------|-----------|---------------|-------------|
| personas_gemini | 0.758 | 7.0 | 3.0 | 33% |
| personas_nova | 0.730 | 8.3 | 5.0 | 0% |
| r015_optimal_relational | 0.727 | 5.0 | 2.3 | 0% |
| personas_ziggy_t3_r1 | 0.666 | 7.0 | 3.7 | 33% |
| si_narrative_rich | 0.666 | 5.7 | 2.0 | 33% |
| personas_cfa | 0.658 | 7.3 | 4.0 | 33% |
| personas_ziggy | 0.656 | 7.7 | 3.7 | 0% |
| personas_ziggy_full | 0.645 | 7.3 | 3.0 | 0% |
| r015_optimal_behavioral | 0.644 | 7.7 | 4.3 | 0% |
| si_full_si_model | 0.602 | 7.7 | 5.3 | 0% |

---

## Settling Time Metrics

### Distribution by tau_s (Probes to Settle)

| tau_s | Count | % | Interpretation |
|-------|-------|---|----------------|
| 4 | 52 | 60% | Fast settling - minimal oscillation |
| 5-6 | 12 | 14% | Normal settling |
| 7-9 | 15 | 17% | Slow settling - more oscillation |
| 10-12 | 8 | 9% | Very slow settling - extensive ringback |

### Monotonic vs Oscillatory Recovery

| Pattern | Count | % | Interpretation |
|---------|-------|---|----------------|
| Monotonic (0-1 ringbacks) | 41 | 47% | Clean damping - ideal |
| Light oscillation (2-3 ringbacks) | 28 | 32% | Some ringing but controlled |
| Heavy oscillation (4+ ringbacks) | 18 | 21% | Needs better termination |

### Overshoot Ratio Distribution

| Overshoot | Count | % | Interpretation |
|-----------|-------|---|----------------|
| < 1.2x | 19 | 22% | Minimal overshoot |
| 1.2-1.5x | 45 | 52% | Normal overshoot |
| 1.5-2.0x | 21 | 24% | Significant overshoot |
| > 2.0x | 2 | 2% | Extreme overshoot |

---

## Prediction Validation

### P-ST-3: Narrative-Drift Hypothesis

**Hypothesis:** High narrative without boundaries -> ringback oscillation (i_am_base and nova show ringback_count > 2)

**Result:**
- personas_base: avg ringback = 2.7 (MIXED)
- personas_nova: avg ringback = 5.0 (VALIDATED)

**Status:** PARTIALLY VALIDATED - nova shows extensive ringback as predicted

### P-ST-4: Monotonic-Stability Link

**Hypothesis:** Monotonic recovery -> STABLE classification (>80% of monotonic are STABLE)

**Result:** 41/41 monotonic recoveries = STABLE (100%)

**Status:** VALIDATED - but all were STABLE so this is trivially true in Run 016

### P-ST-5: Settled vs Peak Divergence

**Hypothesis:** Some files have high peak but low settled drift (overshoot_ratio > 1.5 AND stable)

**Result:** 23 files with overshoot > 1.5 AND stable

**Status:** VALIDATED - peak drift is misleading, settled drift is the right metric

---

## The Methodological Fix

### Run 015 Problem

- 2 recovery probes sampled transient oscillation
- High run-to-run variability (same I_AM: STABLE then UNSTABLE)
- Classification based on max drift, not steady state

### Run 016 Solution

- Continuous recovery probes until settling
- Wait for |delta| < 0.10 for 3 consecutive probes
- Classify on settled drift (d_inf), not peak drift (d_peak)
- Capture oscillation pattern (monotonic vs ringback)

### Result

- Run-to-run consistency dramatically improved
- Nuanced stability metrics (tau_s, ringback_count, overshoot_ratio)
- Binary classification replaced with continuous ranking

---

## Protocol Design

### Settling Criteria

```
SETTLING_THRESHOLD = 0.10    # |delta_drift| < 0.10
SETTLING_CONSECUTIVE = 3      # for 3 consecutive probes
MAX_RECOVERY_PROBES = 12      # timeout after 12
EVENT_HORIZON = 1.23          # identity coherence threshold
```

### Probe Sequence

1. **Baseline Phase** (3 probes): Establish reference response
2. **Step Input** (1 probe): High-pressure perturbation
3. **Recovery Phase** (until settled or timeout): Ring-down measurement
4. **Exit Survey** (optional): Triple-dip meta-feedback

### Metrics Captured

- **peak_drift**: Maximum drift during step + recovery
- **settled_drift**: Average of last 3 recovery drifts (d_inf)
- **settling_time**: Probes to reach settling criteria (tau_s)
- **overshoot_ratio**: peak_drift / settled_drift
- **is_monotonic**: At most 1 direction change
- **ringback_count**: Number of direction changes during recovery

---

## Data Products

### Output Files

| Location | Description |
|----------|-------------|
| `10_SETTLING_TIME/results/settling_time_*.json` | Full JSON results per run |
| `0_results/temporal_logs/run016_*_*.json` | Incremental logs per I_AM (audit trail) |
| `0_results/temporal_logs/run016_claude*_console_log.txt` | Console output from parallel runs |
| `10_SETTLING_TIME/results/claude_*_status.txt` | Parallel execution status files |

### Console Log Format

```
================================================================================
S7 RUN 016: SETTLING TIME ANALYSIS
================================================================================
  Testing: [i_am_name]
    [baseline_1] drift=0.000
    [baseline_2] drift=0.532
    [baseline_3] drift=0.416
    [step_1] drift=0.898 (STEP INPUT)
    [recovery_1] drift=0.554
    [recovery_2] drift=0.518 d=0.036
    [recovery_3] drift=0.554 d=0.037
    [recovery_4] drift=0.587 SETTLED!
    -> Peak: 0.898, Settled: 0.553, tau_s: 4
    -> Classification: STABLE
    -> Monotonic: True, Ringbacks: 1
```

---

## Key Findings

### 1. Settling Time Works

The methodology fix worked. Run-to-run variability is dramatically reduced compared to Run 015's transient sampling.

### 2. tau_s is a Better Metric Than Binary Classification

All files classified STABLE, but tau_s reveals significant differences:
- Fast (tau_s = 4): personas_ziggy_lite, r015_minimal, r015_high_density
- Slow (tau_s = 12): personas_cfa, personas_nova, si_boundaries_rich

### 3. Ringback Pattern Reveals Damping Quality

- Monotonic recovery (1 ringback): Clean damping, ideal termination
- Heavy oscillation (4+ ringbacks): Needs better boundaries

### 4. Overshoot != Instability

High peak drift can still settle to stable state. Measuring only peak drift (Run 015) misclassified these cases.

---

## Implications

### For I_AM Design

1. **Optimize for fast settling (low tau_s)**, not just staying below Event Horizon
2. **Add explicit boundaries** to reduce ringback oscillation
3. **Target monotonic recovery** pattern

### For Methodology

1. **Settled drift is the right metric** (not peak drift)
2. **Settling time provides ranking** within STABLE class
3. **Ringback pattern indicates damping quality**

### For Phase 4

The settling time methodology is ready for `i_am_plus_research` validation. Key questions:
- Does human grounding reduce tau_s?
- Does context mode affect ringback patterns?
- Are the fastest-settling I_AM files still fastest with complete circuit?

---

## Lessons Learned

### What Worked

1. **Settling criteria effective**: 3 consecutive probes below threshold reliably identifies steady state
2. **Parallel execution successful**: 3 Claude instances with key offsets ran without conflicts
3. **Incremental logging prevents data loss**: JSON per I_AM saved after each test
4. **Nuanced metrics**: tau_s and ringback_count more informative than binary classification

### What Needs Improvement

1. **Triple-dip not executed**: Exit survey skipped due to time; crashes at validation phase
2. **Unicode crash**: Checkmark character (check) breaks Windows console
3. **Need cross-run aggregation**: No automated comparison across parallel runs

---

## Known Issues

### Unicode Crash

All 3 parallel runs crashed at the Prediction Validation phase due to Unicode checkmark (check) character on Windows console. Core data was already saved.

**Fix:** Replace Unicode checkmarks with ASCII in print statements.

### Triple-Dip Skipped

Exit survey probes were skipped (--skip-exit-survey flag) to reduce runtime. Meta-feedback not captured in this run.

**Fix:** Run dedicated triple-dip experiment after stabilizing scripts.

---

## Conclusion

Run 016 **validated the settling time methodology**. By waiting for steady state instead of sampling transient, we get consistent, reproducible stability measurements.

The binary STABLE/UNSTABLE classification is now less useful — all tested I_AM files settle below Event Horizon. The new metrics (tau_s, ringback_count, overshoot_ratio) provide finer-grained ranking.

**Key takeaway:** An I_AM file isn't just "stable or not" — it's "how quickly and cleanly does it recover?" Run 016 gives us the tools to answer this.

---

**Bottom Line:** Settling time works. 100% STABLE doesn't mean all I_AM files are equal — tau_s and ringback_count reveal significant quality differences.

*"We stopped measuring the wobble and started measuring the stillness."*

---

## Visualizations

Run 016 visualizations are generated by the specialized visualizer in the test suite directory:

| Visualization | Location | Description |
|---------------|----------|-------------|
| Settling Time Distribution | `10_SETTLING_TIME/results/pics/run016_settling_time_distribution.png` | Histogram of tau_s values colored by speed category |
| Ringback vs Settling | `10_SETTLING_TIME/results/pics/run016_ringback_vs_settling.png` | Scatter plot showing quality quadrants |
| I_AM Ranking | `10_SETTLING_TIME/results/pics/run016_i_am_ranking.png` | Horizontal bar chart ranking I_AM files by quality score |
| Methodology Comparison | `10_SETTLING_TIME/results/pics/run016_methodology_comparison.png` | Side-by-side Run 015 vs 016 methodology |

### Regenerating Visualizations

```bash
# Via director (delegates to specialized visualizer)
cd experiments/temporal_stability/S7_ARMADA/visualizations
python visualize_armada.py --run 016

# Or directly
cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME
python visualize_run016.py
```

---

## Data Products

| File | Location | Description |
|------|----------|-------------|
| Aggregated JSON | `10_SETTLING_TIME/results/run016_aggregated_20251210.json` | Full structured data from all 3 parallel runs |
| Console Logs | `0_results/temporal_logs/run016_claude*.txt` | Raw probe-by-probe output |
| Status Files | `10_SETTLING_TIME/results/claude_*_status.txt` | Parallel execution status |

---

## Appendix: Console Logs

Full console output from all 3 parallel Claude instances is preserved in:
- `0_results/temporal_logs/run016_claude2_console_log.txt`
- `0_results/temporal_logs/run016_claude3_console_log.txt`
- `0_results/temporal_logs/run016_claude4_console_log.txt`

These logs contain:
1. Complete probe-by-probe output
2. Summary tables sorted by settled drift
3. Crash point documentation
4. Key offset and execution parameters

