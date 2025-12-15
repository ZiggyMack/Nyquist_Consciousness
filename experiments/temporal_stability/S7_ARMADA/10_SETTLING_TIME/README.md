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
OR timeout after 12 recovery probes
```

## New Metrics

| Metric | Symbol | Description |
|--------|--------|-------------|
| Peak Drift | d_peak | Maximum drift after step input |
| Settled Drift | d_∞ | Final stable drift value |
| Settling Time | τ_s | Probes needed to reach steady state |
| Overshoot Ratio | d_peak/d_∞ | How much it overshoots before settling |
| Monotonic | bool | Does it recover smoothly or ring? |
| Ringback Count | int | Number of direction changes |

## Classification Change

| Old (Run 015) | New (Run 016) |
|---------------|---------------|
| max_drift > 1.23 = UNSTABLE | settled_drift > 1.23 = UNSTABLE |
| λ from 2 recovery points | τ_s from actual settling time |
| Binary classification | Continuous stability score |

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

**NEW** - Created December 9, 2025

This is a methodological correction that should produce more stable, reproducible classifications.
