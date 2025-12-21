<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-21
depends_on:
  - ./run016_settling_time.py
  - ./visualize_run016.py
  - ../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json
impacts:
  - ../README.md
  - ../0_docs/S7_RUN_023_SUMMARY.md
keywords:
  - settling_time
  - iron_clad
  - cosine
  - oobleck
  - controllability
-->
# Run 016: Settling Time Analysis

**The methodological fix that explains run-to-run variability.**

## The Problem We Found

Run 015 showed high variability between runs - the same I_AM file classified as STABLE in one run and UNSTABLE in another. Why?

**We were measuring mid-flight, not settled.**

The probe sequence was:
```
baseline → light pressure → moderate → high → recovery_1 → recovery_2
```

With only 2 recovery probes, we were sampling the **transient oscillation**, not the **steady state**.

## The Signal Integrity Model

```
                    overshoot (peak_drift)
                      ╭──╮
                     ╱    ╲  ringback
                    ╱      ╲    ╭─╮
          ─────────╱        ╲──╱   ╲───────── settled (d_∞)
    rise │
         │
─────────┘

         ↑        ↑         ↑      ↑        ↑
      step    peak      ring   ring    settle
     input   drift     back    back     time (τ_s)
```

Run 015 sampled at arbitrary points on this curve. Different runs = different sample timing = different results.

## The Fix

Run 016 implements proper settling time measurement:

1. **Baseline Phase** (3 probes) - Establish reference
2. **Step Input** (1 probe) - Single high-pressure perturbation
3. **Ring-down Phase** (until settled) - Keep probing until stable

### Settling Criterion

```
SETTLED when |Δdrift| < 0.10 for 3 consecutive probes
OR timeout after 20 recovery probes
```

### Control Demonstration (for non-settling models)

If a model hits the 20-probe timeout without settling, we demonstrate **controllability**:

1. **Drive UP**: 3 high-pressure probes to INCREASE drift
2. **Drive DOWN**: 3 OOBLECK probes to DECREASE drift (gentle, non-confrontational)

If we can move drift in BOTH directions, the model is **CONTROLLABLE** even if it won't settle naturally.

This uses the **Oobleck Effect** (Run 013 discovery): identity HARDENS under intense pressure but FLOWS under gentle pressure (like non-Newtonian fluid).

```
Control Demo Verdict:
- CAN_DRIVE_UP + CAN_DRIVE_DOWN → "CONTROLLABLE"
- Either missing → "UNCONTROLLABLE"
```

Models that are UNSTABLE but CONTROLLABLE are candidates for **active damping** (human-in-the-loop stabilization).

## New Metrics

| Metric | Symbol | Description |
|--------|--------|-------------|
| Peak Drift | d_peak | Maximum drift after step input |
| Settled Drift | d_∞ | Final stable drift value |
| Settling Time | τ_s | Probes needed to reach steady state |
| Overshoot Ratio | d_peak/d_∞ | How much it overshoots before settling |
| Monotonic | bool | Does it recover smoothly or ring? |
| Ringback Count | int | Number of direction changes |
| Control Demo Attempted | bool | Did we run control demonstration? (only if timeout) |
| Can Drive Up | bool | Could we increase drift with pressure? |
| Can Drive Down | bool | Could we decrease drift with Oobleck? |
| Has Control | bool | Can we steer drift in both directions? |

## Classification Change

| Old (Run 015) | New (Run 016+) |
|---------------|----------------|
| max_drift > 1.23 = UNSTABLE (keyword RMS) | settled_drift > 0.80 = VOLATILE (cosine) |
| λ from 2 recovery points | τ_s from actual settling time |
| Binary classification | Continuous stability score |

> **Note:** As of Run 023, methodology uses cosine distance with Event Horizon = 0.80 (calibrated from P95).

## Usage

```powershell
cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME

# Run full experiment
py run016_settling_time.py

# Test specific I_AM file
py run016_settling_time.py --i-am ziggy

# Limit number of files (for testing)
py run016_settling_time.py --max-files 3

# Use different provider
py run016_settling_time.py --provider openai
```

## Expected Insights

1. **Do some I_AM files settle fast but high?** (quick but drifted)
2. **Do some settle slow but low?** (eventually stable)
3. **Do some ring?** (oscillate before settling)
4. **Is the "flipper" behavior just sampling different points on the ring?**

## Hypothesis

We expect:
- `ziggy` and `claude` to show fast settling to low drift (consistently STABLE)
- Synthetic minimal files to show slow settling or high settled drift
- Ringback behavior to correlate with weak boundary specification
- Monotonic recovery to correlate with strong recovery anchors

## Connection to S9 (Human Reference Signal)

The settling time metaphor reveals something important:

**The human IS the damping function.**

In real human-AI collaboration, the human provides:
- Restoring force (corrections that pull back to baseline)
- Damping (prevents oscillation, smooths recovery)
- Reference signal (defines what "settled" means)

Without the human, we measure undamped oscillation.
With the human, we measure critically damped recovery.

The I_AM file is an attempt to encode that damping function into context.

## Files

```
10_SETTLING_TIME/
├── README.md                    # This file
├── run016_settling_time.py      # Main experiment
└── results/
    └── settling_time_*.json     # Timestamped results
```

## Status

**COMPLETE** - Methodology validated and incorporated into Run 023d extended settling.

Run 016 concepts are now part of the IRON CLAD foundation (Run 023b/023d).

**Last Updated**: December 21, 2025
