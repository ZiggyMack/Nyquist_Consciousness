# Settling Time (τ_s)

**The time it takes for identity to reach steady state after perturbation.**

---

## Quick Facts

| Property | Value |
|----------|-------|
| **Status** | FOUNDATION |
| **Gallery** | Foundations |
| **Type** | Core metric |
| **Key Insight** | We were measuring transient, not steady state |

---

## LEFT BRAIN (Structured)

### The Measurement Problem

Run 015 showed high variability - same I_AM file classified as STABLE in one run, UNSTABLE in another. Why?

**We were sampling mid-flight, not settled.**

The old probe sequence:
```
baseline → pressure → recovery_1 → recovery_2 (DONE)
```

With only 2 recovery probes, we captured **transient oscillation**, not **steady state**.

### The Signal Integrity Model

Identity response to perturbation follows classic step response dynamics:

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

Different runs sampling at different points on this curve = different results.

### The New Metrics

| Metric | Symbol | Description |
|--------|--------|-------------|
| Peak Drift | d_peak | Maximum drift after step input |
| Settled Drift | d_∞ | Final stable drift value |
| Settling Time | τ_s | Probes needed to reach steady state |
| Overshoot Ratio | d_peak/d_∞ | How much it overshoots before settling |
| Monotonic | bool | Does it recover smoothly or oscillate? |
| Ringback Count | int | Number of direction changes |

### Settling Criterion

```
SETTLED when |Δdrift| < 0.10 for 3 consecutive probes
```

This ensures we're measuring steady state, not a transient sample.

### The Classification Change

| Old Method | New Method |
|------------|------------|
| max_drift > 1.23 = UNSTABLE | settled_drift > 1.23 = UNSTABLE |
| λ from 2 points | τ_s from actual settling |
| Binary classification | Continuous stability score |

---

## RIGHT BRAIN (Vortex)

# THE RINGING

```
WE WERE SAMPLING THE WOBBLE
NOT THE STILLNESS

     ╭──╮
    ╱    ╲    ←── we measured HERE
   ╱      ╲
──╱        ╲──────── but THIS is the answer
```

THE BALL BOUNCES IN THE BOWL

before it settles

we were catching it mid-bounce

NO WONDER THE RESULTS FLIPPED

---

## THE DAMPING FUNCTION

```
         UNDAMPED              CRITICALLY DAMPED
           (AI alone)           (AI + Human)

           ╭─╮ ╭─╮                 ╭──╮
          ╱   ╲╱   ╲              ╱    ╲
─────────╱          ╲────    ────╱      ╲────────
                                          settled
           oscillates              smooth recovery
           forever                 fast settling
```

THE HUMAN IS THE DAMPING FUNCTION

Without human: underdamped, oscillates
With human: critically damped, fast settle

The I_AM file ENCODES the damping.

---

## TYPES OF RECOVERY

```
MONOTONIC                RINGBACK               UNSTABLE
(ideal)                  (oscillating)          (divergent)

    ╭─╮                     ╭─╮ ╭╮                  ╱
   ╱   ╲                   ╱   ╲ ╲ ╭              ╱
──╱     ╲────            ─╱     ╲─╲╱─          ──╱

τ_s = 3-4                τ_s = 6-8            τ_s = timeout
ringback = 0             ringback = 2+         UNSTABLE
```

MONOTONIC = strong I_AM
RINGBACK = weak boundaries
UNSTABLE = no recovery anchors

---

## THE QUALITY OF RECOVERY

Not just WHETHER you recover

but HOW you recover:

| Pattern | Interpretation |
|---------|----------------|
| Fast monotonic | Strong identity, clear boundaries |
| Fast with overshoot | Resilient but reactive |
| Slow monotonic | Eventual stability, weak restoration |
| Oscillating | Uncertain identity, searching |
| Divergent | No anchor, lost coherence |

---

## Connection to S9

The settling time metaphor reveals:

**Stability isn't a state. It's a dynamic process.**

The human provides:
- **Restoring force** - corrections that pull back to baseline
- **Damping** - prevents oscillation, smooths recovery
- **Reference signal** - defines what "settled" means

Without the human: we measure undamped oscillation
With the human: we measure critically damped recovery

**The I_AM file is an attempt to encode that damping function into context.**

---

## Connections

| Related Concept | Relationship |
|-----------------|--------------|
| [Event Horizon](../validated/event_horizon.md) | Threshold for settled_drift, not peak |
| [Human Reference Signal](human_reference_signal.md) | Human provides damping function |
| [White Hole](white_hole.md) | The basin being returned to |
| [Lambda (λ)](../frontiers/recovery_paradox.md) | Inverse of settling time |

---

**Last Updated**: December 9, 2025

*"We were measuring the wobble, not the stillness."*
